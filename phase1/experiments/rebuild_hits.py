"""Lean reconstruction for goals where a later Vampire run found a proof:
the v2 battery on every premise set first, then the follow-up strategies
from try_rebuild.py if that fails. Same acceptance checks as always.

Usage: python3 rebuild_hits.py <vampire_run.jsonl> <workers> <out.jsonl>
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover, candidate_tactics, apply_tactics
from prover import followup_tactics as new_candidates

CORPUS = "../data/corpus.sexpr"


def main():
    src, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    decls = load(CORPUS)
    by = {d.name: d for d in decls}
    prover = Prover(decls, CORPUS, load_statements())
    todo = [r for r in map(json.loads, open(src)) if r["vampire"].startswith("Theorem")]
    print(f"{len(todo)} goals with a Vampire proof", flush=True)

    def run(r):
        g = by[r["goal"]]
        gd = prover.goal_defs(g)
        t0 = time.time()
        first, second, third = [], [], []
        for j, ps in enumerate(r["premise_sets"], start=1):
            first += [(f"{l}#{j}", s) for l, s in candidate_tactics(ps, r["defs"], gd)]
            second += [(f"{l}#{j}", s) for l, s in new_candidates(ps, r["defs"], gd)]
            third += [(f"{l}#{j}", s) for l, s in apply_tactics(ps, r["defs"])]
        win, script = None, None
        for batch in (first, second, third):
            if not batch:
                continue
            res = prover.attempt_batch(g, batch, timeout=300, single_timeout=90,
                                       max_retry_secs=600)
            win = next((l for l, ok, _ in res if ok), None)
            if win:
                script = dict(batch)[win]
                break
        return {"goal": g.name, "proved_by": win, "script": script,
                "vampire": r["vampire"], "secs": round(time.time() - t0, 1)}

    won = 0
    with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
        for r in ex.map(run, todo):
            won += bool(r["proved_by"])
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            print(f"{'PROVED' if r['proved_by'] else 'failed':7s} {r['goal'][:40]:40s} "
                  f"{r['proved_by'] or ''} ({r['secs']}s)", flush=True)
    print(f"\nLean rebuilt {won}/{len(todo)}")


if __name__ == "__main__":
    main()
