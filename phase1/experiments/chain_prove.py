"""Prove a goal as a chain of steps rather than in one leap.

`oracle_haves.py` establishes that the steps of a failed proof are
individually easy: 64% of v4's failures have intermediate steps in the
original Megalodon proof, each citing a median of 1 fact against 12 for
the whole theorem, and the prover closes most of those steps on its own.
But closing the steps is not proving the theorem. This assembles them.

For a goal whose original proof introduces intermediate propositions
P1..Pn, it proves each Pi separately, keeps the tactic script that worked,
and then emits a single Lean proof of the *real* theorem:

    theorem <goal> : <library signature> := by
      have step0 : P1 := by <script that proved P1>
      have step1 : P2 := by <script that proved P2>
      ...
      <battery over the premises, with step0..stepN in scope>

The last attempt runs through the ordinary `attempt_batch` with the
**default** guard, so the result is checked exactly as any other proof is:
the type must match the library declaration character for character, no
sorryAx, no leak. A goal that comes back ok here is proved in the same
sense as the 640.

What it does NOT claim: the steps come from Megalodon's proof, so this is
not the system finding them unaided. It measures the ceiling -- how much
is reachable if the steps are known -- which is what decides whether
having a model propose them is worth the budget.

Usage: python3 chain_prove.py <run.jsonl> <workers> <out.jsonl> [limit] [--resume]
"""
import json
import os
import sys
import threading
from concurrent.futures import ThreadPoolExecutor

from library import load, _collect, _features
from itp import load_statements
from prover import Prover, candidate_tactics
from itp import BRIDGE
import sexpr_translate as T
from oracle_haves import collect_haves, build_ctx, Hop, _HOP_GUARD

CORPUS = "../data/corpus.sexpr"
_prover = _decls = _h2n = _p2n = None


_init_lock = threading.Lock()


def _init():
    global _prover, _decls, _h2n, _p2n
    with _init_lock:
        if _prover is not None:
            return
        _init_locked()


def _init_locked():
    global _prover, _decls, _h2n, _p2n
    _decls = load(CORPUS)
    _prover = Prover(_decls, CORPUS, load_statements())
    _h2n = {d.hash: d.name for d in _decls if d.hash}
    _p2n = {d.index: d.name for d in _decls if d.kind == "PRIM"}


def _indent(script, pad="  "):
    return "".join(pad + ln + "\n" for ln in script.strip().splitlines())


def _prove_step(hop):
    """Prove one intermediate proposition; return the winning script."""
    sets, defs, _ = _prover.premise_sets(hop)
    cands = candidate_tactics(sets[0], defs, _prover.goal_defs(hop))
    for j, alt in enumerate(sets[1:], start=2):
        cands += [(f"{lbl}#{j}", s) for lbl, s in
                  candidate_tactics(alt, defs, _prover.goal_defs(hop))
                  if lbl.startswith(("prem-", "solve_by_elim", "goal-unfold"))]
    by_label = dict(cands)
    for lbl, ok, _why in _prover.attempt_batch(hop, cands, guard=_HOP_GUARD):
        if ok:
            return lbl, by_label[lbl]
    return None, None


def _run(task):
    goal_name, props = task
    goal = _prover.by_name[goal_name]
    out = {"goal": goal_name, "steps": len(props), "steps_proved": 0,
           "chain_ok": False, "by": None}

    # 1. prove each step on its own, keeping the script that worked
    lines, names = [], []
    for i, prop in enumerate(props):
        try:
            lean = T.tm_to_lean(prop, build_ctx(_decls))
        except Exception:
            continue
        hop = Hop(f"{goal_name}__s{i}", goal.index, prop, _h2n, _p2n)
        _prover.sigs[hop.name] = f" : {lean}"
        lbl, script = _prove_step(hop)
        if not script:
            continue
        out["steps_proved"] += 1
        names.append(f"step{i}")
        lines.append(f"have step{i} : {lean} := by\n{_indent(script, '    ')}")

    if not lines:
        return out

    # 2. assemble: the proved steps, then the ordinary battery on top of them
    prelude = "".join(l + "\n" for l in lines)
    sets, defs, _ = _prover.premise_sets(goal)
    cands = []
    for j, ps in enumerate(sets, start=1):
        for lbl, script in candidate_tactics(ps, defs, _prover.goal_defs(goal)):
            cands.append((f"chain-{lbl}#{j}", prelude + script))
    # also: just hand the steps to grind on their own
    cands.append(("chain-steps-grind",
                  prelude + f"intros\ntry simp only [{BRIDGE}] at *\ngrind"))

    # 3. check it as a real proof of the real theorem -- default guard
    for lbl, ok, _why in _prover.attempt_batch(goal, cands, timeout=300):
        if ok:
            out["chain_ok"], out["by"] = True, lbl
            break
    return out


def main():
    run, workers, dest = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    resume = "--resume" in sys.argv
    rest = [a for a in sys.argv[4:] if not a.startswith("--")]
    limit = int(rest[0]) if rest else None

    decls = load(CORPUS)
    by = {d.name: d for d in decls}
    rows = [json.loads(l) for l in open(run) if l.strip()]
    tasks = []
    for r in rows:
        if r.get("proved_by"):
            continue
        d = by.get(r["goal"])
        if not d or d.kind != "THM" or d.body is None:
            continue
        props = []
        collect_haves(d.body, [], props)
        if props:
            tasks.append((r["goal"], props))
    if limit:
        tasks = tasks[:limit]

    done = set()
    if resume and os.path.exists(dest):
        kept = []
        for line in open(dest):
            try:
                kept.append(json.loads(line))
            except json.JSONDecodeError:
                pass
        with open(dest, "w") as fh:
            fh.writelines(json.dumps(r) + "\n" for r in kept)
        done = {r["goal"] for r in kept}
        tasks = [t for t in tasks if t[0] not in done]
        print(f"resuming: {len(done)} done", flush=True)

    print(f"{len(tasks)} goals to chain", flush=True)
    n = proved = 0
    with ThreadPoolExecutor(max_workers=workers, initializer=_init) as ex, \
            open(dest, "a" if resume else "w") as fh:
        for r in ex.map(_run, tasks):
            fh.write(json.dumps(r) + "\n"); fh.flush()
            n += 1; proved += bool(r["chain_ok"])
            print(f"{n}/{len(tasks)} {r['goal'][:32]:32s} "
                  f"steps {r['steps_proved']}/{r['steps']}"
                  f"{'   *** PROVED: ' + str(r['by']) if r['chain_ok'] else ''}",
                  flush=True)
    print(f"\nnewly proved by chaining: {proved}/{n}")


if __name__ == "__main__":
    main()
