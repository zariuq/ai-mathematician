"""Re-run ONLY the deterministic Lean battery on theorems where Vampire found
a proof but the baseline reconstruction failed, reusing the premises the
baseline stored (no Vampire re-run, no LLM). Measures what the distilled
strategies and the timeout fix recover for free.

Usage: python3 rebuild_failures.py <baseline.jsonl> <workers> <out.jsonl>
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover, candidate_tactics

CORPUS = "../data/corpus.sexpr"
base, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
decls = load(CORPUS)
by = {d.name: d for d in decls}
prover = Prover(decls, CORPUS, load_statements())
todo = [json.loads(l) for l in open(base)]
todo = [r for r in todo if not r["proved_by"] and r["vampire"].startswith("Theorem")]
print(f"{len(todo)} theorems", flush=True)


def run(r):
    g = by[r["goal"]]
    cands = candidate_tactics(r["premises"], r["defs"], prover.goal_defs(g))
    t0 = time.time()
    res = prover.attempt_batch(g, cands)
    win = next((lbl for lbl, ok, _ in res if ok), None)
    return {"goal": g.name, "proved_by": win, "results": res,
            "secs": round(time.time() - t0, 1)}


won = 0
t0 = time.time()
with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
    for r in ex.map(run, todo):
        won += bool(r["proved_by"])
        fh.write(json.dumps(r) + "\n")
        print(f"{'PROVED' if r['proved_by'] else 'failed':7s} {r['goal'][:40]:40s} "
              f"{r['proved_by'] or ''} ({r['secs']}s)", flush=True)
print(f"\nrecovered {won}/{len(todo)} in {time.time()-t0:.0f}s")
