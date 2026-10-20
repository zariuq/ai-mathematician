"""Lean reconstruction of induction splits found by try_induction.py
(see Prover.induction_lean). Same checks as everything else: kernel,
statement identity, leak guard.

Usage: python3 rebuild_induction.py <splits.jsonl> <workers> <out.jsonl> [--limit N]
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
limit = int(sys.argv[sys.argv.index("--limit") + 1]) if "--limit" in sys.argv else None
decls = load(CORPUS)
by = {d.name: d for d in decls}
prover = Prover(decls, CORPUS, load_statements())
todo = [r for r in map(json.loads, open(src)) if r["principle"]][:limit]
print(f"{len(todo)} splits", flush=True)


def run(r):
    t0 = time.time()
    ok, why, script = prover.induction_lean(by[r["goal"]], r)
    return {"goal": r["goal"], "principle": r["principle"],
            "proved_by": "induction" if ok else None, "why": why,
            "script": script, "secs": round(time.time() - t0, 1)}


won = 0
with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
    for r in ex.map(run, todo):
        won += bool(r["proved_by"])
        fh.write(json.dumps(r) + "\n")
        print(f"{'PROVED' if r['proved_by'] else 'failed':7s} {r['goal'][:40]:40s} "
              f"{r['principle']} ({r['secs']}s)", flush=True)
        if not r["proved_by"]:
            print("   ", r["why"][:300].replace("\n", " | "), flush=True)
print(f"\nLean proved {won}/{len(todo)}")
