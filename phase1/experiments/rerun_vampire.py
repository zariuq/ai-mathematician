"""Re-run only Search + Vampire (no Lean, no LLM) on the theorems where
Vampire found no proof in a baseline run, to measure what a Search change
buys. Same premise slices and timeouts as the baseline.

Usage: python3 rerun_vampire.py <baseline.jsonl> <workers> <out.jsonl>
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover

CORPUS = "../data/corpus.sexpr"
base, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
decls = load(CORPUS)
by = {d.name: d for d in decls}
prover = Prover(decls, CORPUS, load_statements())
todo = [json.loads(l) for l in open(base)]
todo = [r for r in todo if not r["proved_by"] and not r["vampire"].startswith("Theorem")]
print(f"{len(todo)} theorems", flush=True)


def run(r):
    g = by[r["goal"]]
    premises, defs, status = prover.hints(g)
    return {"goal": g.name, "index": g.index, "vampire": status,
            "premises": premises, "defs": defs, "proved_by": None}


won = 0
t0 = time.time()
with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
    for r in ex.map(run, todo):
        won += r["vampire"].startswith("Theorem")
        fh.write(json.dumps(r) + "\n")
print(f"Vampire now proves {won}/{len(todo)} in {time.time()-t0:.0f}s")
