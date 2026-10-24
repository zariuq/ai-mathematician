"""The sketch's "LLM proving lemma -> LLM formalizing proof -> ITP (+ATP)"
path, in the style of Draft, Sketch, and Prove (Jiang et al., ICLR 2023):

  1. DRAFT   (1 LLM call): the model writes an informal, step-by-step proof
             in ordinary mathematical language, naming the facts it uses.
  2. SKETCH  (1 LLM call): the model formalizes that proof as a Lean proof
             outline -- intermediate `have` steps -- and may leave any step
             it cannot finish as `sorry`.
  3. PROVE   (no LLM): every `sorry` gap is replaced by the automatic
             tactics (grind / solve_by_elim over Search's facts, the
             premises Vampire used where it found a proof). Lean checks
             the result with the usual kernel, statement and leak checks.
  4. REPAIR  (up to `repair_rounds` LLM calls): Lean's error goes back to
             the model, which revises the outline; step 3 again.

The division of labour is the point: the LLM supplies the proof's
STRUCTURE, which automation cannot find, and automation supplies the
routine steps, which is where LLM-written Lean usually breaks.
The model only proposes; only Lean decides.

All calls go through llm.chat, so they count against the hard call cap.
"""
import re

from itp import BRIDGE
from llm import LeanContext, SYSTEM, chat, goal_state, _extract, normalize, feedback

# The main prompt forbids `sorry`; here `sorry` marks a gap for the hammer.
SKETCH_SYSTEM = SYSTEM.replace(
    "Never use `sorry` or `admit`.",
    "Write `sorry` for any routine step you want the automatic prover to fill.")

DRAFT_SYSTEM = """You are a careful research mathematician working in
Megalodon's higher-order set theory (sets, ordinals, naturals as von
Neumann ordinals, surreal numbers). You write rigorous INFORMAL proofs.

Write a proof of the statement in numbered steps. Each step should follow
from earlier steps, the hypotheses, and the listed available facts in one
or two simple inferences; name the facts or definitions each step uses.
If the proof is by induction, say on which variable, with which listed
induction principle, and state the induction predicate exactly.
Do not use the theorem itself. Reply with the numbered proof only."""

SKETCH_RULES = """
Now formalize that informal proof as a Lean 4 tactic script that follows
its steps: one `have` per intermediate claim, then finish the goal.
An automatic prover will fill every `sorry` you leave, using the available
facts and `grind`, so for any single routine step you are unsure how to
write in Lean, write `sorry` rather than guessing -- but keep the
structure (the intermediate claims, case splits, induction) explicit:
the automatic prover can only close small steps.
Reply with exactly one ```lean code block, tactic script only."""


def hammer(premises, defs):
    """The tactic that replaces each `sorry`: the deterministic battery's
    main strategies, tried in turn on that one step."""
    P = ", ".join(f"«{p}»" for p in premises)
    unfold = ", ".join([BRIDGE] + [f"«{d}»" for d in defs])
    alts = [f"(intros; (try simp only [{BRIDGE}] at *); grind)",
            f"(intros; (try simp only [{unfold}] at *); grind)"]
    if premises:
        alts.insert(1, f"(solve_by_elim (maxDepth := 8) [{P}])")
    return "(first | " + " | ".join(alts) + ")"


def fill_gaps(script, premises, defs):
    """Replace each `sorry` by the hammer; the premises are introduced as
    hypotheses once, up front, so grind can use them in every gap."""
    H = hammer(premises, defs)
    s = re.sub(r":=\s*sorry\b", f":= by {H}", script)
    s = re.sub(r"\bby\s+sorry\b", f"by {H}", s)
    # tactic position: alone on a line, after a bullet, after a case arm
    s = re.sub(r"(?m)^(\s*(?:[·.]\s*)?)sorry\s*$", lambda m: m.group(1) + H, s)
    s = re.sub(r"(=>|<;>)\s*sorry\s*$", lambda m: f"{m.group(1)} {H}", s,
               flags=re.M)
    s = re.sub(r"\bsorry\b", f"(by {H})", s)
    haves = "".join(f"have hp{i} := @«{p}»\n" for i, p in enumerate(premises))
    return haves + s, script.count("sorry")


def _trim_trailing(prover, goal, sketch, premises, defs, label, why, max_drop=3):
    """Lean rejects a script that keeps going after the proof is complete
    ("No goals to be solved"), e.g. a final `exact ...` after `simp` already
    closed the goal. Retry with the last 1..max_drop top-level lines removed
    (no LLM call); a shortened script must pass every check like any other.
    Returns (ok, why, sketch, script) for the first that passes, else the
    original failure."""
    lines = sketch.rstrip().splitlines()
    cands = []
    for k in range(1, max_drop + 1):
        if len(lines) - k < 1:
            break
        s = "\n".join(lines[:-k])
        cands.append((f"{label}-trim{k}", s))
    if not cands:
        return False, why, sketch, fill_gaps(sketch, premises, defs)[0]
    filled = [(lbl, fill_gaps(s, premises, defs)[0]) for lbl, s in cands]
    res = prover.attempt_batch(goal, filled, timeout=300, single_timeout=120)
    for (lbl, ok, w), (_, s), (_, f) in zip(res, cands, filled):
        if ok:
            return True, w, s, f
    return False, why, sketch, fill_gaps(sketch, premises, defs)[0]


def dsp_rounds(prover, goal, premises, defs, repair_rounds=1,
               model="openai/gpt-oss-120b", log=None, examples=None):
    """Returns (proved_label or None, transcript). Uses at most
    2 + repair_rounds LLM calls."""
    ctx = getattr(prover, "_lean_ctx", None) or LeanContext()
    prover._lean_ctx = ctx
    sig = prover.sigs[goal.name]
    state = goal_state(prover, goal)
    facts = ctx.show(premises, limit_chars=80000) or "(none)"
    shots = ("Accepted Lean proofs of similar EARLIER theorems in this library "
             "(to show its conventions):\n\n"
             + "\n\n".join(f"theorem {n}{s} := by\n"
                             + "\n".join("  " + l for l in sc.splitlines())
                             for n, s, sc in examples) + "\n\n---\n\n") if examples else ""
    context = shots + (f"Statement (Lean syntax; `x1445`-style names are bound "
               f"variables):\n{goal.name}{sig}\n\n"
               + (f"Goal after introducing hypotheses:\n{state}\n\n" if state else "")
               + f"Definitions it uses:\n{ctx.show(defs) or '(none)'}\n\n"
               f"Available facts:\n{facts}\n")
    transcript = []

    try:
        draft = chat([{"role": "system", "content": DRAFT_SYSTEM},
                      {"role": "user", "content": context}], model=model)
    except Exception as e:
        return None, [{"stage": "draft", "error": f"api: {type(e).__name__}"}]
    transcript.append({"stage": "draft", "text": draft})
    if log:
        log(f"    draft: {' '.join(draft.split())[:200]}")

    msgs = [{"role": "system", "content": SKETCH_SYSTEM},
            {"role": "user", "content":
             f"Prove this theorem:\n\ntheorem {goal.name}{sig} := by\n  ...\n\n"
             + context + f"\nInformal proof to follow:\n{draft}\n" + SKETCH_RULES}]
    for r in range(1 + repair_rounds):
        try:
            reply = chat(msgs, model=model)
        except Exception as e:
            transcript.append({"stage": f"sketch{r}", "error": f"api: {type(e).__name__}"})
            break
        sketch = _extract(reply)
        sketch = normalize(sketch)  # see llm.py: real feedback
        script, _ = fill_gaps(sketch, premises, defs)
        label = f"dsp-r{r}"
        (_, ok, why), = prover.attempt_batch(goal, [(label, script)],
                                             timeout=300, single_timeout=300)
        if not ok and "No goals to be solved" in why:
            ok, why, sketch, script = _trim_trailing(prover, goal, sketch,
                                                     premises, defs, label, why)
        transcript.append({"stage": f"sketch{r}", "sketch": sketch,
                           "gaps": sketch.count("sorry"), "script": script,
                           "ok": ok, "why": why})
        if log:
            log(f"    sketch {r}: {sketch.count('sorry')} gaps -> "
                f"{'OK' if ok else why.splitlines()[0][:160]}")
        if ok:
            return label, transcript
        msgs += [{"role": "assistant", "content": f"```lean\n{sketch}\n```"},
                 {"role": "user", "content":
                  f"After the automatic prover filled the `sorry` gaps, Lean "
                  f"rejected the proof:\n{feedback(why, prover, goal)}\n\nRevise the outline (you may "
                  f"add intermediate `have` steps or leave more `sorry` gaps). "
                  f"Reply with one ```lean block, tactic script only."}]
    return None, transcript
