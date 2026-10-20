"""Measure depth-2 backward chaining on v4's failures.

The failures are theorems a human proved in several steps; every strategy
in the current battery assumes one step. `apply_tactics` goes one level
deeper -- apply a premise, then grind the subgoals -- but still expects
grind to finish each subgoal outright. `apply2_tactics` gives each
subgoal the full battery instead, including a bounded backward search.

Run against goals v4 failed. Anything that comes back ok here passed the
ordinary guard: type identical to the library declaration, no sorryAx, no
leak -- the same bar as the 640.

Usage: python3 try_apply2.py <run.jsonl> <workers> <out.jsonl> [limit] [--resume]
"""
import json
import os
import sys
import threading
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover, apply2_tactics

CORPUS = "../data/corpus.sexpr"
_prover = None
_lock = threading.Lock()


def _init():
    global _prover
    with _lock:
        if _prover is None:
            decls = load(CORPUS)
            _prover = Prover(decls, CORPUS, load_statements())


def _run(name):
    goal = _prover.by_name[name]
    sets, defs, vstatus = _prover.premise_sets(goal)
    cands = []
    for j, ps in enumerate(sets, start=1):
        cands += [(f"{lbl}#{j}", s) for lbl, s in apply2_tactics(ps, defs)]
    res = {"goal": name, "vampire": vstatus, "proved_by": None}
    for lbl, ok, _why in _prover.attempt_batch(goal, cands, timeout=300,
                                               max_retry_secs=600):
        if ok:
            res["proved_by"] = lbl
            break
    return res


def main():
    run, workers, dest = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    resume = "--resume" in sys.argv
    rest = [a for a in sys.argv[4:] if not a.startswith("--")]
    limit = int(rest[0]) if rest else None

    rows = [json.loads(l) for l in open(run) if l.strip()]
    todo = [r["goal"] for r in rows if not r.get("proved_by")]
    if limit:
        todo = todo[:limit]

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
        todo = [g for g in todo if g not in done]
        print(f"resuming: {len(done)} done", flush=True)

    print(f"{len(todo)} failed goals to retry with depth-2 apply", flush=True)
    n = won = 0
    with ThreadPoolExecutor(max_workers=workers, initializer=_init) as ex, \
            open(dest, "a" if resume else "w") as fh:
        for r in ex.map(_run, todo):
            fh.write(json.dumps(r) + "\n"); fh.flush()
            n += 1; won += bool(r["proved_by"])
            mark = f"   *** PROVED by {r['proved_by']}" if r["proved_by"] else ""
            print(f"{n}/{len(todo)} {r['goal'][:34]:34s}{mark}", flush=True)
    print(f"\nnewly proved: {won}/{n}")


if __name__ == "__main__":
    main()
