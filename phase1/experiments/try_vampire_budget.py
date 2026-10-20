"""Does a larger Vampire budget find proofs the 5 s run missed? Vampire only
(no Lean, no LLM) on goals where the v2 run found no Vampire proof.

Usage: python3 try_vampire_budget.py <run.jsonl> <every> <timeout> <workers> <out.jsonl> [slices]
  slices: comma-separated premise-slice sizes (default 16,32,64,128)
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover

CORPUS = "../data/corpus.sexpr"
src, every, tmo, workers, out = (sys.argv[1], int(sys.argv[2]), int(sys.argv[3]),
                                 int(sys.argv[4]), sys.argv[5])
SLICES = tuple(int(x) for x in sys.argv[6].split(",")) if len(sys.argv) > 6 else (16, 32, 64, 128)
decls = load(CORPUS)
by = {d.name: d for d in decls}
prover = Prover(decls, CORPUS, load_statements())
todo = [r for r in map(json.loads, open(src))
        if not r["proved_by"] and not r["vampire"].startswith("Theorem")][::every]
print(f"{len(todo)} goals, Vampire timeout {tmo}s, slices {SLICES}", flush=True)


def run(r):
    g = by[r["goal"]]
    t0 = time.time()
    sets, defs, status = prover.premise_sets(g, slices=SLICES,
                                             vampire_timeout=tmo)
    return {"goal": g.name, "index": g.index, "vampire": status,
            "premise_sets": sets, "premises": sets[0], "defs": defs,
            "proved_by": None, "secs": round(time.time() - t0, 1)}


won = 0
with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
    for r in ex.map(run, todo):
        won += r["vampire"].startswith("Theorem")
        fh.write(json.dumps(r) + "\n")
        fh.flush()
        if r["vampire"].startswith("Theorem"):
            print(f"FOUND  {r['goal'][:40]:40s} {r['vampire']} ({r['secs']}s)", flush=True)
print(f"\nVampire now proves {won}/{len(todo)}")
