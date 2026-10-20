"""Run the incremental prover (incremental.py) over a set of goals.

Usage: python3 try_incremental.py <run.jsonl> <workers> <out.jsonl>
                                  [limit] [--resume] [--all]

<run.jsonl> is a prover run; by default the goals tried are the ones it
FAILED, which is the population the incremental search was built for.
--all tries every goal in the file instead.

A result is recorded only after Prover.attempt_batch has accepted the script
under the ordinary guard, so `proved` here means the same thing it means in
results/phase1_v2.md.
"""
import json
import os
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover
import incremental as inc

CORPUS = "../data/corpus.sexpr"
_prover = None
_lock = threading.Lock()
_out_lock = threading.Lock()


def _init():
    """One Prover per process, built once. Threads share it: Search is read
    only after construction, and each attempt runs in its own Lean process."""
    global _prover
    with _lock:
        if _prover is None:
            decls = load(CORPUS)
            _prover = Prover(decls, CORPUS, load_statements())
    return _prover


def _run(arg):
    name, pre = arg
    p = _init()
    goal = p.by_name[name]
    try:
        ok, label, script, stats = inc.prove(
            p, goal, max_depth=4, max_probes=25, beam=4, k=8, pre=pre,
            deadline=time.time() + 420)
    except Exception as e:                      # a bad state should not stop the run
        return {"goal": name, "proved": False, "error": f"{type(e).__name__}: {e}"}
    return {"goal": name, "proved": bool(ok), "label": label,
            "script": script, "stats": stats}


def main():
    run, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    rest = sys.argv[4:]
    resume = "--resume" in rest
    every = "--all" in rest
    limit = next((int(a) for a in rest if a.isdigit()), None)

    rows = [json.loads(l) for l in open(run)]
    todo = [(r["goal"], (r.get("premise_sets") or [], r.get("defs") or [],
                         r.get("vampire")))
            for r in rows
            if every or not (r.get("proved") or r.get("proved_by"))]
    done = set()
    if resume and os.path.exists(out):
        done = {json.loads(l)["goal"] for l in open(out)}
        todo = [t for t in todo if t[0] not in done]
    if limit:
        todo = todo[:limit]
    names = todo
    print(f"{len(todo)} goals, {workers} workers"
          f"{f', {len(done)} already done' if done else ''}", flush=True)

    _init()
    n = 0
    proved = 0
    fh = open(out, "a" if resume else "w")
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for res in ex.map(_run, names):
            n += 1
            proved += res["proved"]
            with _out_lock:
                fh.write(json.dumps(res) + "\n")
                fh.flush()
            mark = f"*** PROVED by {res.get('label')}" if res["proved"] else ""
            print(f"{n}/{len(todo)} {res['goal']:<36} {mark}", flush=True)
    fh.close()
    print(f"\nproved {proved}/{n}")


if __name__ == "__main__":
    main()
