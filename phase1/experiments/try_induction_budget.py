"""Induction splits with a larger Vampire budget, on goals still without any
Vampire proof. Vampire only (Lean reconstruction is a separate step).

Usage: python3 try_induction_budget.py <out.jsonl> <every> <timeout> <workers> <runs...>
  runs: result files; a goal is attempted if it is unproved in the first and
  has no Vampire proof in any of them.
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover

CORPUS = "../data/corpus.sexpr"


def main():
    out, every, tmo, workers = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    runs = sys.argv[5:]
    decls = load(CORPUS)
    by = {d.name: d for d in decls}
    prover = Prover(decls, CORPUS, load_statements())
    base = [json.loads(l) for l in open(runs[0])]
    has_vamp = set()
    for f in runs:
        for l in open(f):
            r = json.loads(l)
            if r["vampire"].startswith("Theorem"):
                has_vamp.add(r["goal"])
    todo = [by[r["goal"]] for r in base
            if not r["proved_by"] and r["goal"] not in has_vamp][::every]
    print(f"{len(todo)} goals, case timeout {tmo}s, slices 32/128", flush=True)
    orig = prover._vampire_case

    def case(c, ranked, slices, timeout=5):
        return orig(c, ranked, slices, timeout=tmo)
    prover._vampire_case = case

    def run(g):
        t0 = time.time()
        split = prover.induction_split(g, slices=(32, 128))
        return {"goal": g.name, **(split or {"principle": None}),
                "secs": round(time.time() - t0, 1)}

    won = 0
    with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
        for r in ex.map(run, todo):
            won += bool(r["principle"])
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            if r["principle"]:
                print(f"SPLIT  {r['goal'][:40]:40s} {r['principle']} ({r['secs']}s)", flush=True)
    print(f"\nall cases proved by Vampire: {won}/{len(todo)}")


if __name__ == "__main__":
    main()
