"""Try NEW Lean reconstruction strategies on goals where Vampire found a
proof but the v2 battery could not rebuild it, reusing the premise sets the
run stored (no Vampire rerun, no LLM). Measures which new strategies help,
before any of them is added to the battery.

Usage: python3 try_rebuild.py <run.jsonl> <workers> <out.jsonl>
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements, BRIDGE
from prover import Prover

CORPUS = "../data/corpus.sexpr"
from prover import followup_tactics as new_candidates  # noqa: E402


def main():
    global prover, by
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
            cands += [(f"{lbl}#{j}", s) for lbl, s in
                      new_candidates(ps, r["defs"], prover.goal_defs(g))]
        res = prover.attempt_batch(g, cands, timeout=300, single_timeout=90,
                                   max_retry_secs=600)
        wins = [lbl for lbl, ok, _ in res if ok]
        return {"goal": g.name, "wins": wins, "secs": round(time.time() - t0, 1),
                "scripts": {lbl: s for lbl, s in cands if lbl in wins}}


    won = 0
    with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
        for r in ex.map(run, todo):
            won += bool(r["wins"])
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            print(f"{'PROVED' if r['wins'] else 'failed':7s} {r['goal'][:40]:40s} "
                  f"{','.join(r['wins'][:3])} ({r['secs']}s)", flush=True)
    print(f"\nnew strategies rebuild {won}/{len(todo)}")


if __name__ == "__main__":
    main()
