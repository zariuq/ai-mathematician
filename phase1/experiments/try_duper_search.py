"""Duper as a standalone prover, from Search's top facts, on goals with NO
Vampire proof (no Vampire premise set to reuse).

Usage: python3 try_duper_search.py <goals.jsonl> <every> <k> <workers> <out.jsonl>
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
    src, every, k, workers, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    decls = load(CORPUS)
    by = {d.name: d for d in decls}
    prover = Prover(decls, CORPUS, load_statements())
    todo = [by[json.loads(l)["goal"]] for l in open(src)][::every]
    print(f"{len(todo)} goals, top {k} facts", flush=True)

    def run(g):
        t0 = time.time()
        ranked = [n for n, _ in prover.search.rank(g.index, limit=4 * k)]
        facts = [n for n in ranked if by[n].kind in ("THM", "AXIOM")][:k]
        cands = duper_tactics(facts, prover.goal_defs(g))
        res = prover.attempt_batch(g, cands, timeout=400, single_timeout=150,
                                   max_retry_secs=400, heartbeats=1000000, duper=True)
        wins = [l for l, ok, _ in res if ok]
        return {"goal": g.name, "wins": wins, "facts": facts,
                "scripts": {l: s for l, s in cands if l in wins},
                "secs": round(time.time() - t0, 1)}

    won = 0
    with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
        for r in ex.map(run, todo):
            won += bool(r["wins"])
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            print(f"{'PROVED' if r['wins'] else 'failed':7s} {r['goal'][:40]:40s} ({r['secs']}s)", flush=True)
    print(f"\nDuper from Search facts proves {won}/{len(todo)}")


if __name__ == "__main__":
    main()
