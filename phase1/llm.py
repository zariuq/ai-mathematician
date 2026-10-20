"""Phase 1 LLM plug-in: an UNTRUSTED proposer of Lean tactic scripts.

Implements the sketch's feedback arrow: propose -> Lean checks -> on
failure, Lean's actual error goes back to the model for another round.

What the model sees (and nothing else):
  * the goal statement, exactly as the library states it
  * the Megalodon definitions the goal uses
  * the facts Search/Vampire selected -- all strictly BEFORE the goal,
    statements only
  * the bridge lemmas to native logic
  * optionally, Vampire's refutation proof of the goal from those same
    facts (vampire_proof.proof_for_llm), as a guide to translate
  * optionally, accepted proofs of similar theorems EARLIER in the library
    (few-shot examples of its conventions)
  * on later rounds, its own previous attempt and Lean's error
It never sees the goal's original proof or anything after the goal.

Whatever it writes is checked exactly like every other candidate: Lean
kernel + statement-identity check + leak guard (see itp.py).

Credentials come from ../.env (LLM_API_KEY, LLM_BASE_URL); the key is never
logged or written anywhere else.
"""
import http.client
import json
import os
import re
import time
import urllib.error
import urllib.request

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
DEFAULT_MODEL = "openai/gpt-oss-120b"


def _env():
    path = os.path.join(ROOT, ".env")
    env = {}
    if os.path.exists(path):
        for line in open(path):
            if "=" in line:
                k, v = line.strip().split("=", 1)
                env[k] = v
    env.update({k: v for k, v in os.environ.items() if k.startswith("LLM_")})
    if "LLM_API_KEY" not in env or "LLM_BASE_URL" not in env:
        raise RuntimeError("LLM_API_KEY / LLM_BASE_URL missing (see README)")
    return env


# ------------------------------------------------------------ spending cap
# Every request that reaches the API -- retries included -- is appended to
# a ledger with its token usage. Before each request the ledger is counted
# under a file lock (safe across threads and processes); once it holds
# LLM_CALL_CAP entries, no further request is sent. Start a fresh ledger
# (LLM_LEDGER) for each budgeted run.
LEDGER = os.environ.get("LLM_LEDGER",
                        os.path.join(ROOT, "results", "llm_usage.jsonl"))
CALL_CAP = int(os.environ.get("LLM_CALL_CAP", "100"))


class BudgetExhausted(RuntimeError):
    pass


def _reserve(model):
    """Count the ledger and record one call, atomically; raise if the cap
    is reached. The entry is written BEFORE the request, so a crash
    mid-request still counts against the budget."""
    import fcntl
    os.makedirs(os.path.dirname(LEDGER), exist_ok=True)
    with open(LEDGER, "a+") as fh:
        fcntl.flock(fh, fcntl.LOCK_EX)
        fh.seek(0)
        n = sum(1 for l in fh if '"event": "call"' in l)
        if n >= CALL_CAP:
            raise BudgetExhausted(f"LLM call cap reached ({n}/{CALL_CAP})")
        fh.write(json.dumps({"event": "call", "n": n + 1, "model": model,
                             "time": time.strftime("%Y-%m-%dT%H:%M:%S")}) + "\n")
        fh.flush()
        return n + 1


def _log_usage(n, model, usage, secs):
    import fcntl
    with open(LEDGER, "a") as fh:
        fcntl.flock(fh, fcntl.LOCK_EX)
        fh.write(json.dumps({"event": "usage", "n": n, "model": model,
                             "prompt_tokens": usage.get("prompt_tokens"),
                             "completion_tokens": usage.get("completion_tokens"),
                             "secs": round(secs, 1)}) + "\n")


def usage_summary(path=LEDGER):
    calls, pt, ct = 0, 0, 0
    if os.path.exists(path):
        for l in open(path):
            e = json.loads(l)
            if e["event"] == "call":
                calls += 1
            else:
                pt += e.get("prompt_tokens") or 0
                ct += e.get("completion_tokens") or 0
    return {"calls": calls, "prompt_tokens": pt, "completion_tokens": ct}


def chat(messages, model=DEFAULT_MODEL, max_tokens=16000, temperature=0.2,
         retries=4, salvage=True, extra=None):
    env = _env()
    body = json.dumps({"model": model, "messages": messages,
                       "max_tokens": max_tokens,
                       "temperature": temperature, **(extra or {})}).encode()
    for attempt in range(retries):
        req = urllib.request.Request(
            env["LLM_BASE_URL"].rstrip("/") + "/chat/completions", data=body,
            headers={"Authorization": f"Bearer {env['LLM_API_KEY']}",
                     "Content-Type": "application/json"})
        n = _reserve(model)
        t0 = time.time()
        try:
            # under load the gateway can take minutes on long prompts;
            # 180 s lost whole goals to timeouts in the parallel sweeps
            r = json.load(urllib.request.urlopen(req, timeout=600))
            _log_usage(n, model, r.get("usage") or {}, time.time() - t0)
            ch = r["choices"][0]
            content = ch["message"].get("content") or ""
            notes = ch["message"].get("reasoning") or ""
            if not content.strip() and ch.get("finish_reason") == "length" \
                    and notes and salvage:
                # The gateway caps a reply at 8192 tokens, and on long
                # prompts the model spends all of them thinking: 73% of
                # replies in the first Vampire-proof A/B came back empty.
                # Hand it the end of its own notes and ask for the answer.
                return chat(messages + [{"role": "user", "content":
                    "You ran out of space while thinking. Your notes so far "
                    "(the end of them):\n\n" + notes[-12000:] + "\n\nNow reply "
                    "with ONLY the final ```lean block (tactic script only). "
                    "Think briefly; do not start over."}],
                    model=model, max_tokens=max_tokens,
                    temperature=temperature, retries=retries, salvage=False,
                    # thinking off: the notes already hold it (deepseek
                    # honours "none"; gpt-oss rejects it, "low" is its least)
                    extra={"reasoning_effort":
                           "none" if "deepseek" in model else "low"})
            return content
        # Every network failure is retried, not only URLError: the gateway
        # also drops connections (http.client.RemoteDisconnected), which
        # cut 19 goals short in the v6 sweep before this was caught.
        except (urllib.error.URLError, http.client.HTTPException, ConnectionError,
                TimeoutError, OSError, KeyError, ValueError) as e:
            if attempt == retries - 1:
                raise
            time.sleep(20 * (attempt + 1))
    return ""


# ------------------------------------------------------------ Lean context
class LeanContext:
    """Declaration texts from the verified library, for building prompts.
    Theorems are shown as statements only -- never with their proofs."""

    def __init__(self, meglib_path=os.path.join(ROOT, "lib", "MegLib.lean")):
        self.text = {}
        for line in open(meglib_path, encoding="utf-8"):
            m = re.match(r"(axiom|noncomputable def|theorem) (\S+)", line)
            if not m:
                continue
            kind, name = m.group(1), m.group(2)
            line = line.rstrip()
            if kind == "theorem":
                line = line.split(" := ", 1)[0]
            self.text[name] = line

    def show(self, names, limit_chars=12000):
        # Facts are shown up to limit_chars. Prompts pass a larger limit for
        # the premises: on the 257 hardest goals the human proofs cite a
        # median of 13 lemmas, and Search's top 24 held all of them for only
        # 7 goals (top 96: 66).
        out, total = [], 0
        for n in names:
            t = self.text.get(n)
            if not t:
                continue
            if total + len(t) > limit_chars:
                break
            out.append(t)
            total += len(t)
        return "\n".join(out)


SYSTEM = """You write Lean 4 tactic proofs (Lean 4 core only, NO Mathlib).

The library encodes Megalodon's higher-order set theory inside `namespace
Megalodon`. Its logic is ENCODED, not Lean's native logic:
  Megalodon.and P Q, Megalodon.or P Q, Megalodon.not P, Megalodon.iff P Q,
  Megalodon.ex T P, Megalodon.eq T x y, Megalodon.neq T x y,
  Megalodon.True, Megalodon.False
are definitions. These proved bridge lemmas convert them to native logic:
  b_True, b_False, b_not, b_and, b_or, b_iff, b_eq, b_neq, b_ex
e.g. `simp only [b_and, b_or, b_ex, b_eq, b_not, b_iff, b_True, b_False, b_neq] at *`
turns encoded goals/hypotheses into ∧ ∨ ∃ = ¬ ↔ True False.
Other definitions (Subq, Sing, ordsucc, ...) can be unfolded with
`simp only [Name] at *` or `unfold Name`, or used definitionally.
Useful tactics: intro, intros, exact, apply, refine, constructor, cases,
rcases, obtain, have, simp only, rw, grind, solve_by_elim, assumption.
`grind` is available and strong once the logic is native.

IMPORTANT about sets: `set`, `In`, `Empty`, `Union`, `Power`, `Repl`, `Eps_i`
are OPAQUE axioms, not inductive types. `cases`/`rcases`/`constructor`/
`⟨...⟩` do NOT work on `In x (Union X)` etc. Membership facts can only be
introduced or eliminated by applying the listed facts (e.g. a lemma like
UnionE / UPairE / ReplE / SepE turns membership into an encoded `ex`/`or`/
`and`, which the bridge lemmas then make native, after which rcases works).
Induction is not a tactic here: apply an induction principle from the
available facts (e.g. `apply nat_ind` / `apply In_ind`) with a suitable
predicate, e.g. `refine nat_ind (fun n => ...) ?_ ?_`.
The goal state after `intros` is shown to you; work from it. Names in the
statement like `x1445` are BOUND variables, NOT in scope: start your script
with `intro` and choose your own names for every binder/hypothesis, and
only refer to names you introduced.

Rules:
- Use ONLY the facts listed as available, plus the bridge lemmas and
  definitions shown. Do NOT use the theorem being proved.
- Every top-level tactic starts at column 0 (no indentation); indent only
  the body of a nested `by` block. Never use `sorry` or `admit`.
- Reply with exactly one ```lean code block containing ONLY the tactic
  script (the lines after `:= by`), no `theorem` header.
"""


def _extract(reply):
    m = re.findall(r"```(?:lean4?|)\s*\n(.*?)```", reply, re.S)
    if m:
        script = m[-1]
    elif "```" in reply:
        # unclosed fence (reply cut off): take everything after the last opener
        script = re.split(r"```(?:lean4?|)\s*\n?", reply)[-1]
    else:
        script = reply
    script = script.strip()
    # tolerate the model repeating the header anyway
    script = re.sub(r"^\s*(theorem|lemma|example)\b.*?:=\s*by\s*\n", "",
                    script, flags=re.S)
    if script.startswith("by\n"):
        script = script[3:]
    lines = script.splitlines()
    if lines:
        pad = min((len(l) - len(l.lstrip()) for l in lines if l.strip()),
                  default=0)
        lines = [l[pad:] for l in lines]
    return "\n".join(lines).strip()


def build_prompt(ctx, goal_name, goal_sig, defs, premises, state=None,
                 atp_proof=None, examples=None):
    return (
        ("Accepted Lean proofs of similar EARLIER theorems in this library "
         "(to show its conventions; do not cite these theorems unless they "
         "are listed as available facts):\n\n"
         + "\n\n".join(f"theorem {n}{sig} := by\n"
                         + "\n".join("  " + l for l in sc.splitlines())
                         for n, sig, sc in examples) + "\n\n---\n\n"
         if examples else "")
        + (
        f"Prove this theorem (the statement is fixed; write only the tactic script):\n\n"
        f"theorem {goal_name}{goal_sig} := by\n  ...\n\n"
        + (f"Lean's goal state after `intros` and converting encoded logic to native "
           f"(`intros; simp only [b_*] at *`):\n{state}\n\n" if state else "")
        + f"Definitions it uses:\n{ctx.show(defs) or '(none)'}\n\n"
        f"Available facts (you may use these, by name):\n"
        f"{ctx.show(premises, limit_chars=80000) or '(none)'}\n"
        + (f"\nThe automated prover Vampire PROVED this goal from exactly the "
           f"facts and definitions above. Its proof (TPTP, names mapped back "
           f"to the library):\n\n{atp_proof}\n" if atp_proof else "")
    ))


def goal_state(prover, goal, guard=None):
    """Ask Lean for the goal state after intros + bridging, by deliberately
    leaving it unsolved and reading the 'unsolved goals' error."""
    from itp import BRIDGE
    res = prover.attempt_batch(
        goal, [("probe", f"intros\ntry simp only [{BRIDGE}] at *\ndone")],
        guard=guard)
    why = res[0][2]
    m = re.search(r"unsolved goals\s*\n(.*)", why, re.S)
    return m.group(1).strip()[:3000] if m else None


def _bridged(lines, BRIDGE):
    """The bridge inserted before the final top-level tactic: the usual
    near-miss where the argument is right but the last step works on
    encoded `eq`/`and`/... (`simpa [h2] using h1` with h2 : eq set a b)."""
    tops = [j for j, l in enumerate(lines)
            if l.strip() and not l.startswith((" ", "\t", "--"))]
    if not tops or tops[-1] == 0:
        return None
    i = tops[-1]
    return lines[:i] + [f"simp only [{BRIDGE}] at *"] + lines[i:]


def _dedented(lines):
    """First line at column 0, everything after it indented: the model
    indented the body as if under a header, which ends the `by` block
    after line one (`unexpected token 'have'; expected command`)."""
    body = [l for l in lines[1:] if l.strip()]
    if not body or lines[0].startswith((" ", "\t")) \
            or lines[0].rstrip().endswith(("by", ":=", "=>", "·")):
        return None
    m = min(len(l) - len(l.lstrip()) for l in body)
    if m == 0:
        return None
    return [lines[0]] + [l[m:] if l.strip() else l for l in lines[1:]]


def repair_variants(script, why, premises, label):
    """Mechanical repairs of a rejected script, as (label, script) pairs:
    bridge before the last step; dedent; and, when Lean reports unsolved
    goals (the commonest failure -- the model follows the argument but
    stops short), finish every leftover goal with the deterministic
    closers the pipeline already uses."""
    from itp import BRIDGE
    from prover import _lean_name
    lines = script.rstrip().splitlines()
    if not lines:
        return []
    bases = [("", lines)]
    for tag, fn in (("-bridge", lambda l: _bridged(l, BRIDGE)),
                    ("-dedent", _dedented)):
        v = fn(lines)
        if v:
            bases.append((tag, v))
    d = _dedented(lines)
    if d and _bridged(d, BRIDGE):
        bases.append(("-dedent-bridge", _bridged(d, BRIDGE)))
    P = ", ".join(_lean_name(p) for p in premises)
    sbe = f"solve_by_elim (maxDepth := 8) [{P}]" if P else "solve_by_elim (maxDepth := 8)"
    closer = [f"all_goals (try simp only [{BRIDGE}] at *)",
              f"all_goals (first | grind | {sbe} | (intros; grind) | assumption)"]
    out = [(label + tag, "\n".join(ls)) for tag, ls in bases[1:]]
    if "unsolved goals" in why or "-dedent" in "".join(t for t, _ in bases):
        out += [(label + tag + "-finish", "\n".join(ls + closer)) for tag, ls in bases]
    return out


_BRIDGE_SIMP = re.compile(r"^simp only \[\s*(b_\w+\s*,\s*)*b_\w+\s*\] at \*\s*$")


def normalize(script):
    """Mechanical fixes applied BEFORE Lean sees a script, so the error the
    model gets back is about its argument, not about layout:
    - first line at column 0 with the body indented (49% of failed attempts
      in the v5 sweep showed the model a bogus `introN` error instead);
    - a bridge-only `simp only [b_*] at *` with nothing to rewrite fails with
      "simp made no progress" and kills the script (82 attempts): make it
      `try`."""
    lines = _dedented(script.splitlines()) or script.splitlines()
    lines = ["try " + l if _BRIDGE_SIMP.match(l) else l for l in lines]
    return "\n".join(lines)


def feedback(why, prover, goal, limit=2500):
    """Lean's error as the model should see it: without the guard's
    internals, bounded in length (long errors push deepseek past the
    gateway's 8192-token reply cap), and, for names that do not exist,
    the closest real lemmas from EARLIER in the library with their
    statements (all 469 unknown names in the v5 sweep were invented)."""
    import difflib
    body = "\n".join(l for l in why.splitlines() if not l.startswith("GUARD"))
    body = body.strip()[:limit]
    unknown = re.findall(r"[Uu]nknown (?:identifier|constant) `([^`]+)`", why)
    if unknown:
        ctx = getattr(prover, "_lean_ctx", None)
        earlier = [d.name for d in prover.decls[:goal.index]
                   if d.kind in ("THM", "AXIOM", "DEF")]
        hints = []
        for n in dict.fromkeys(u.replace("Megalodon.", "") for u in unknown):
            near = difflib.get_close_matches(n, earlier, n=4, cutoff=0.5)
            if near:
                stmts = [ctx.text.get(m, m) if ctx else m for m in near]
                hints.append(f"`{n}` does not exist. Closest real lemmas "
                             f"(you may use them):\n" + "\n".join(stmts))
            else:
                hints.append(f"`{n}` does not exist; use only listed facts.")
        body += "\n\n" + "\n\n".join(hints)[:2500]
    return body


def llm_rounds(prover, goal, premises, defs, rounds=3, model=DEFAULT_MODEL,
               log=None, atp_proof=None, examples=None, guard=None):
    """Feedback loop: propose, check, feed the Lean error back. Returns
    (proved_label or None, transcript list). `guard`: see attempt_batch
    (a lifted lemma that is not a library declaration needs its own)."""
    ctx = getattr(prover, "_lean_ctx", None) or LeanContext()
    prover._lean_ctx = ctx
    sig = prover.sigs[goal.name]
    state = goal_state(prover, goal, guard=guard)
    msgs = [{"role": "system", "content": SYSTEM},
            {"role": "user", "content": build_prompt(ctx, goal.name, sig, defs,
                                                     premises, state,
                                                     atp_proof, examples)}]
    transcript = []
    for r in range(1, rounds + 1):
        try:
            reply = chat(msgs, model=model)
        except BudgetExhausted:
            raise
        except Exception:
            # the gateway failed every retry: wait once, then give the round
            # one more chance before abandoning the goal
            time.sleep(120)
            try:
                reply = chat(msgs, model=model)
            except BudgetExhausted:
                raise
            except Exception as e:
                transcript.append({"round": r, "error": f"api: {type(e).__name__}"})
                break
        script = _extract(reply)
        # The commonest slip: first line at column 0, the rest indented, so
        # Lean reads the next lines as `intro` arguments. Repairing it only
        # at check time still showed the model the bogus error ("no
        # additional binders ... simp : Prop"): 49% of failed attempts in
        # the v5 sweep. Normalize first, so feedback is the real error.
        script = normalize(script)
        label = f"llm-r{r}"
        res = prover.attempt_batch(goal, [(label, script)], guard=guard)
        _, ok, why = res[0]
        if not ok and "No goals to be solved" in why:
            # the proof was complete before the script ended: retry without
            # the trailing lines (no LLM call; must still pass every check)
            lines = script.rstrip().splitlines()
            trims = [(f"{label}-trim{k}", "\n".join(lines[:-k]))
                     for k in (1, 2, 3) if len(lines) > k]
            for (lbl, t_ok, t_why), (_, t_script) in zip(
                    prover.attempt_batch(goal, trims, guard=guard), trims):
                if t_ok:
                    ok, why, script = True, t_why, t_script
                    break
        if not ok:
            # near-misses, repaired without an LLM call; every repaired
            # script still goes through the full check. The model is shown
            # its own script's error, not a repair's.
            variants = repair_variants(script, why, premises, label)
            if variants:
                for (lbl, r_ok, r_why), (_, r_script) in zip(
                        prover.attempt_batch(goal, variants, guard=guard), variants):
                    if r_ok:
                        ok, why, script, label = True, r_why, r_script, lbl
                        break
        transcript.append({"round": r, "script": script, "ok": ok, "why": why})
        if log:
            head = " | ".join(script.splitlines()[:4])
            log(f"    round {r}: script: {head[:200]}")
            log(f"             -> {'OK' if ok else why.splitlines()[0][:160]}")
        if ok:
            return label, transcript
        msgs += [{"role": "assistant", "content": f"```lean\n{script}\n```"},
                 {"role": "user", "content":
                  f"Lean rejected that proof:\n{feedback(why, prover, goal)}\n\n"
                  f"Fix it. Reply with one ```lean block, tactic script only."}]
    return None, transcript
