"""Measure apply_tactics on goals where the given run found a Vampire proof
but no reconstruction, reusing its stored premise sets (no Vampire, no LLM).

Usage: python3 try_apply.py <run.jsonl> <workers> <out.jsonl>
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover, apply_tactics

CORPUS = "../data/corpus.sexpr"


def main():
    src, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    decls = load(CORPUS)
    by = {d.name: d for d in decls}
    prover = Prover(decls, CORPUS, load_statements())
    todo = [r for r in map(json.loads, open(src))
            if not r["proved_by"] and r["vampire"].startswith("Theorem")]
    print(f"{len(todo)} goals", flush=True)

    def run(r):
        g = by[r["goal"]]
        t0 = time.time()
        cands = []
        for j, ps in enumerate(r["premise_sets"], start=1):
            cands += [(f"{l}#{j}", s) for l, s in apply_tactics(ps, r["defs"])]
        res = prover.attempt_batch(g, cands, timeout=300, single_timeout=60,
                                   max_retry_secs=600) if cands else []
        wins = [l for l, ok, _ in res if ok]
        return {"goal": g.name, "wins": wins, "n": len(cands),
                "scripts": {l: s for l, s in cands if l in wins},
                "secs": round(time.time() - t0, 1)}

    won = 0
    with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
        for r in ex.map(run, todo):
            won += bool(r["wins"])
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            print(f"{'PROVED' if r['wins'] else 'failed':7s} {r['goal'][:40]:40s} "
                  f"{','.join(r['wins'][:2])} [{r['n']} cands] ({r['secs']}s)", flush=True)
    print(f"\napply-then-grind rebuilds {won}/{len(todo)}")


if __name__ == "__main__":
    main()
