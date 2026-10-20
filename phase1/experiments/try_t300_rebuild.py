"""Reconstruct the goals the 300 s Vampire run newly proved.

The 30 s budget found no proof for these; `vampire300.jsonl` does. This runs
the *whole* v4 pipeline on them -- all four reconstruction lines including
Duper, exactly the code path that produced the 640 -- with the stored 300 s
premise sets substituted for a fresh Vampire call, so the ATP work is not
repeated and the comparison is only about reconstruction.

Usage: python3 try_t300_rebuild.py <vampire300.jsonl> <workers> <out.jsonl>
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover

CORPUS = "../data/corpus.sexpr"
src, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]

rows = [json.loads(l) for l in open(src)]
todo = [r for r in rows if str(r.get("vampire", "")).startswith("Theorem")]

# Substitute the stored premise sets for a fresh Vampire run. Patching the
# lookup rather than editing prove() keeps this run on byte-identical
# reconstruction logic to v4; a goal with nothing stored falls through to
# the real thing.
_PRE = {r["goal"]: (r["premise_sets"], r["defs"], r["vampire"]) for r in todo}
_orig = Prover.premise_sets


def _patched(self, goal, **kw):
    if goal.name in _PRE:
        return _PRE[goal.name]
    return _orig(self, goal, **kw)


Prover.premise_sets = _patched

decls = load(CORPUS)
by = {d.name: d for d in decls}
prover = Prover(decls, CORPUS, load_statements())
print(f"{len(todo)} goals the 300 s run newly proved", flush=True)


def run(r):
    g = by[r["goal"]]
    t0 = time.time()
    try:
        res = prover.prove(g)
    except Exception as e:
        return {"goal": g.name, "proved_by": None, "error": f"{type(e).__name__}: {e}"}
    res["secs"] = round(time.time() - t0, 1)
    return res


won = 0
t0 = time.time()
with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
    for r in ex.map(run, todo):
        won += bool(r.get("proved_by"))
        fh.write(json.dumps(r) + "\n")
        fh.flush()
        print(f"{'PROVED' if r.get('proved_by') else 'failed':7s} "
              f"{r['goal'][:42]:42s} {r.get('proved_by') or ''} "
              f"({r.get('secs')}s)", flush=True)
print(f"\nrebuilt {won}/{len(todo)} in {time.time()-t0:.0f}s", flush=True)
