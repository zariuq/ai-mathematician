"""Duper reconstruction on goals that have a Vampire proof but no Lean
reconstruction (reusing the stored premise sets; no Vampire, no LLM).

Usage: python3 try_duper.py <goals.jsonl> <workers> <out.jsonl> [heartbeats]
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover, duper_tactics

CORPUS = "../data/corpus.sexpr"


def main():
    src, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    hb = int(sys.argv[4]) if len(sys.argv) > 4 else 1000000
    decls = load(CORPUS)
    by = {d.name: d for d in decls}
    prover = Prover(decls, CORPUS, load_statements())
    todo = [r for r in map(json.loads, open(src)) if r["vampire"].startswith("Theorem")]
    print(f"{len(todo)} goals, heartbeats {hb}", flush=True)

    def run(r):
        g = by[r["goal"]]
        t0 = time.time()
        cands = []
        for j, ps in enumerate(r["premise_sets"], start=1):
            cands += [(f"{l}#{j}", s) for l, s in duper_tactics(ps, r["defs"])]
        res = prover.attempt_batch(g, cands, timeout=400, single_timeout=150,
                                   max_retry_secs=600, heartbeats=hb, duper=True)
        wins = [l for l, ok, _ in res if ok]
        return {"goal": g.name, "wins": wins,
                "scripts": {l: s for l, s in cands if l in wins},
                "secs": round(time.time() - t0, 1)}

    won = 0
    with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
        for r in ex.map(run, todo):
            won += bool(r["wins"])
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            print(f"{'PROVED' if r['wins'] else 'failed':7s} {r['goal'][:40]:40s} "
                  f"{','.join(r['wins'][:2])} ({r['secs']}s)", flush=True)
    print(f"\nDuper rebuilds {won}/{len(todo)}")


if __name__ == "__main__":
    main()
