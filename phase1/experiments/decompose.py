"""Plan, then prove each hard step as its own theorem.

dsp.py asks the LLM for a proof outline and fills every `sorry` step with
the deterministic hammer; a step the hammer cannot close sinks the whole
proof. Here such a step is lifted out instead:

  1. PLAN    the LLM writes an outline with `sorry` steps (dsp's prompts).
  2. PROBE   every step gets `first | hammer | done`. Lean's error recovery
             keeps elaborating past a failed step, so ONE run reports each
             step the hammer could not close as "unsolved goals" with its
             exact local context.
  3. LIFT    each such goal becomes a standalone lemma: its hypotheses as
             binders, its target as the conclusion.
  4. PROVE   each lemma goes through the full LLM loop (llm.llm_rounds) as
             a small theorem of its own, checked with the hop guard: no
             sorry, no fact at or after the parent goal (leak check).
  5. ASSEMBLE the outline again, every step now `first | hammer | apply
             <lemma> <;> assumption`, the proved lemmas as a prelude, checked
             with the DEFAULT guard against the real library statement.

The oracle_haves experiment motivates the split: given the human proof's
own steps, the pipeline closed 50% of steps but only 23% of whole theorems.
The steps are where the difficulty divides; a failed step is far shorter
than the theorem, which is where the LLM loop does well.
"""
import re

from llm import chat, goal_state, _extract, normalize, feedback, llm_rounds, LeanContext
from dsp import DRAFT_SYSTEM, SKETCH_SYSTEM, hammer

# The LLM plans; the tools prove. Its own tactic proofs were the commonest
# way an outline broke before any step could be lifted (wrong argument
# order in `apply`), so the outline may contain claims only.
PLAN_RULES = """
Now turn that informal proof into a Lean 4 PLAN, not a proof:
- start with `intro` naming every hypothesis;
- then one line per intermediate claim, EXACTLY of the form
      have hN : <claim, a Lean proposition> := by sorry
  each claim a small step from the hypotheses and earlier claims;
- finish with a single line `sorry`.
Write NO other tactics: no apply, exact, simp, rw, cases. An automatic
prover proves every claim and the final step; if it cannot, the claim is
proved separately as its own lemma. So make each claim SMALL, and state it
in the library's own vocabulary (In, Subq, SNo, SNoLt, add_SNo, ...),
using native logic (∧ ∨ ¬ ∃ = →).
Reply with exactly one ```lean code block."""
from oracle_haves import _HOP_GUARD
from prover import candidate_tactics


class Lemma:
    """A lifted step, shaped like a declaration for Search and the guard."""

    def __init__(self, name, parent):
        self.name, self.index, self.kind = name, parent.index, "THM"
        self.stmt, self.body, self.hash, self.proof_deps = None, None, "", set()
        self.stmt_syms, self.feats = parent.stmt_syms, parent.feats


def fill(script, tactic):
    """Replace every `sorry` with `tactic`, wherever it stands."""
    s = re.sub(r":=\s*sorry\b", f":= by {tactic}", script)
    s = re.sub(r"\bby\s+sorry\b", f"by {tactic}", s)
    s = re.sub(r"(?m)^(\s*(?:[·.]\s*)?)sorry\s*$", lambda m: m.group(1) + tactic, s)
    s = re.sub(r"(=>|<;>)\s*sorry\s*$", lambda m: f"{m.group(1)} {tactic}", s, flags=re.M)
    return re.sub(r"\bsorry\b", f"(by {tactic})", s)


def unsolved(why):
    """(hypothesis lines, target) for every 'unsolved goals' block."""
    out = []
    for block in why.split("\n---\n"):
        block = block.replace("lean error: ", "", 1).strip()
        if not block.startswith("unsolved goals"):
            continue
        hyps, cur = [], None
        for ln in block.splitlines()[1:]:
            if ln.startswith("case "):
                continue
            if ln.startswith("⊢"):
                target = ln[1:].strip()
                out.append((hyps, target, block))
                hyps = []
                cur = "goal"
            elif cur == "goal" and ln.startswith(" "):
                out[-1] = (out[-1][0], out[-1][1] + " " + ln.strip(), block)
            elif ln.startswith(" ") and hyps:
                hyps[-1] += " " + ln.strip()
            elif ln.strip():
                hyps.append(ln.strip())
                cur = "hyp"
    return out


def lemma_sig(hyps, target):
    """Binders and conclusion for a lifted goal, or None if it cannot be
    stated (let-values, which a binder would turn into a weaker claim)."""
    text = "\n".join(hyps) + "\n" + target
    names = {}
    for tok in re.findall(r"[^\s():,]+✝[⁰¹²³⁴⁵⁶⁷⁸⁹]*", text):
        names.setdefault(tok, f"v_{len(names)}")
    fix = lambda s: re.sub("|".join(map(re.escape, sorted(names, key=len, reverse=True))),
                           lambda m: names[m.group()], s) if names else s
    binders = []
    for h in hyps:
        if " := " in h:
            return None
        lhs, sep, ty = h.partition(" : ")
        if not sep:
            return None
        binders.append(f"({fix(lhs)} : {fix(ty)})")
    return " ".join(binders) + f" : {fix(target)}"


def decompose_rounds(prover, goal, premises, defs, repair_rounds=2,
                     model="deepseek/deepseek-v4-flash-0731", lemma_model="openai/gpt-oss-120b",
                     lemma_rounds=3, max_lemmas=12, examples=None, log=None,
                     guard=None, depth=1):
    """Returns (proved_label or None, transcript). `guard`: None for a library
    goal; the hop guard when this is called on a lifted lemma (recursion).
    `depth`: how many levels a step that resists the loop is decomposed."""
    lemma_model = lemma_model or model
    cache = {}           # lemma statement -> (name, script, prelude it needs)
    ctx = getattr(prover, "_lean_ctx", None) or LeanContext()
    prover._lean_ctx = ctx
    sig = prover.sigs[goal.name]
    state = goal_state(prover, goal, guard=guard)
    shots = ("Accepted Lean proofs of similar EARLIER theorems in this library:\n\n"
             + "\n\n".join(f"theorem {n}{s} := by\n" + "\n".join("  " + l for l in sc.splitlines())
                           for n, s, sc in examples) + "\n\n---\n\n") if examples else ""
    context = shots + (f"Statement (Lean syntax; `x1445`-style names are bound variables):\n"
                       f"{goal.name}{sig}\n\n"
                       + (f"Goal after introducing hypotheses:\n{state}\n\n" if state else "")
                       + f"Definitions it uses:\n{ctx.show(defs) or '(none)'}\n\n"
                       f"Available facts:\n{ctx.show(premises, limit_chars=80000) or '(none)'}\n")
    H = hammer(premises, defs)
    haves = "".join(f"have hp{i} := @«{p}»\n" for i, p in enumerate(premises))
    transcript = []
    try:
        draft = chat([{"role": "system", "content": DRAFT_SYSTEM},
                      {"role": "user", "content": context}], model=model)
    except Exception as e:
        return None, [{"stage": "draft", "error": f"api: {type(e).__name__}"}]
    msgs = [{"role": "system", "content": SKETCH_SYSTEM},
            {"role": "user", "content": f"Prove this theorem:\n\ntheorem {goal.name}{sig} := by\n  ...\n\n"
             + context + f"\nInformal proof to follow:\n{draft}\n" + PLAN_RULES}]
    n_lemma = 0
    for r in range(1 + repair_rounds):
        try:
            sketch = normalize(_extract(chat(msgs, model=model)))
        except Exception as e:
            transcript.append({"stage": f"plan{r}", "error": f"api: {type(e).__name__}"})
            break
        # PROBE: leave every step open. Each reports its goal and local
        # context as "unsolved goals"; no automation runs here, because a
        # hammer that exhausts its heartbeats raises an error `first` cannot
        # catch, and the step's goal is then never reported.
        (_, ok, why), = prover.attempt_batch(
            goal, [("probe", fill(sketch, "done"))],
            timeout=300, single_timeout=300, err_limit=40000, guard=guard)
        rec = {"stage": f"plan{r}", "sketch": sketch, "steps": sketch.count("sorry")}
        goals = unsolved(why)
        other = [b for b in why.replace("lean error: ", "", 1).split("\n---\n")
                 if b.strip() and not b.strip().startswith("unsolved goals")]
        rec["lifted"] = []
        rec["errors"] = [b[:600] for b in other][:3]
        # LIFT + PROVE every step as its own lemma: the deterministic battery
        # first (isolated, so a heartbeat blow-up costs only that lemma),
        # then the LLM loop. All must be proved for the plan to stand.
        stuck = []
        if goals and not other and len(goals) <= max_lemmas:
            proved, failed = {}, 0
            for hyps, target, _ in goals:
                lsig = lemma_sig(hyps, target)
                if not lsig:
                    failed += 1
                    stuck.append(target)
                    continue
                if lsig in cache:           # proved in an earlier round
                    n, sc, sub = cache[lsig]
                    proved[n] = (" " + lsig, sc, sub)
                    continue
                name = f"{goal.name}__L{n_lemma}"
                n_lemma += 1
                lem = Lemma(name, goal)
                prover.sigs[name] = " " + lsig
                how, script, sub = None, None, ""
                cands = candidate_tactics(premises, defs, defs)
                for (lbl, l_ok, _w), (_, sc) in zip(
                        prover.attempt_batch(lem, cands, guard=_HOP_GUARD), cands):
                    if l_ok:
                        how, script = lbl, sc
                        break
                if not how:
                    label, tr = llm_rounds(prover, lem, premises, defs, rounds=lemma_rounds,
                                           model=lemma_model, examples=examples,
                                           guard=_HOP_GUARD)
                    if label:
                        how, script = label, tr[-1]["script"]
                if not how and depth > 0:
                    # the step resists the loop: plan IT, one level down
                    lbl2, tr2 = decompose_rounds(
                        prover, lem, premises, defs, repair_rounds=1, model=model,
                        lemma_model=lemma_model, lemma_rounds=lemma_rounds,
                        max_lemmas=max_lemmas, examples=examples, log=log,
                        guard=_HOP_GUARD, depth=depth - 1)
                    if lbl2:
                        how, script, sub = "sub-" + lbl2, tr2[-1]["script"], tr2[-1].get("prelude", "")
                rec["lifted"].append({"name": name, "sig": lsig, "proved": how})
                if log:
                    log(f"    lemma {name[-4:]}: {how or 'failed'}  {lsig[:110]}")
                if not how:
                    failed += 1
                    stuck.append(target)
                    continue       # keep going: report every stuck step
                proved[name] = (prover.sigs[name], script, sub)
                cache[lsig] = (name, script, sub)
            if not failed:
                # ASSEMBLE with the DEFAULT guard against the real statement
                prelude = "\n".join(
                    (sub + "\n" if sub else "")
                    + f"theorem «{n}»{s} := by\n" + "".join(f"  {l}\n" for l in sc.splitlines())
                    for n, (s, sc, sub) in proved.items())
                use = " | ".join(f"(apply «{n}» <;> assumption)" for n in proved)
                script = fill(sketch, f"(first | {use})")
                (_, ok, why2), = prover.attempt_batch(goal, [("assemble", script)],
                                                      timeout=600, single_timeout=600,
                                                      prelude=prelude, guard=guard)
                rec.update(assemble_ok=ok, assemble_why=why2[:500])
                if ok:
                    rec.update(ok=True, script=script, prelude=prelude)
                    transcript.append(rec)
                    return f"decomp-r{r}", transcript
            proved = {k: v for k, v in proved.items()}
        else:
            proved = {}
            if len(goals) > max_lemmas:
                stuck = []
        transcript.append(rec)
        if log:
            log(f"    plan {r}: {len(goals)} stuck steps, {len(other)} other errors, "
                f"{len(proved)} lemmas proved")
        msgs += [{"role": "assistant", "content": f"```lean\n{sketch}\n```"},
                 {"role": "user", "content":
                  ("Lean found these problems in the outline itself:\n"
                   + feedback("\n---\n".join(other), prover, goal) + "\n\n" if other else "")
                  + (f"{len(proved)} of {len(goals)} steps were proved. These could "
                     "NOT be proved; replace each by smaller claims:\n"
                     + "\n".join(f"  - {t}" for t in stuck[:6]) + "\n" if stuck else "")
                  + (f"The plan has {len(goals)} steps; use at most {max_lemmas}. "
                     if len(goals) > max_lemmas else "")
                  + "Keep the plan format: `intro`, `have hN : <claim> := by sorry` "
                  "lines, a final `sorry`. Reply with one ```lean block."}]
    return None, transcript
