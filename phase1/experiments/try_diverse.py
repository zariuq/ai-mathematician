"""Vampire on diverse small premise slices (Search.diverse_slices), for goals
still without a Vampire proof. Vampire only.

Usage: python3 try_diverse.py <run.jsonl> <timeout> <workers> <out.jsonl> [extra_vampire_runs...]
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover
from atp import run_vampire, Unsupported

CORPUS = "../data/corpus.sexpr"


def main():
    src, tmo, workers, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    decls = load(CORPUS)
    by = {d.name: d for d in decls}
    prover = Prover(decls, CORPUS, load_statements())
    found = set()
    for f in sys.argv[5:]:
        for l in open(f):
            r = json.loads(l)
            if r["vampire"].startswith("Theorem"):
                found.add(r["goal"])
    todo = [r for r in map(json.loads, open(src))
            if not r["proved_by"] and not r["vampire"].startswith("Theorem")
            and r["goal"] not in found]
    print(f"{len(todo)} goals", flush=True)

    def run(r):
        g = by[r["goal"]]
        t0 = time.time()
        sl = prover.search.diverse_slices(g.index)
        defs = set(prover.goal_defs(g))
        sets, hits = [], []
        for name, facts in sl.items():
            try:
                text, ids, _ = prover.thf.problem(g, facts)
            except Unsupported:
                continue
            st, used = run_vampire(text, timeout=tmo)
            if st == "Theorem":
                vf = [ids[u] for u in used if u in ids]
                defs |= {prover._def_of(u) for u in used} - {None}
                hits.append(name)
                if vf not in sets:
                    sets.append(vf)
        status = ("Theorem@" + ",".join(hits)) if hits else "none"
        return {"goal": g.name, "vampire": status, "premise_sets": sets or [[]],
                "premises": sets[0] if sets else [], "defs": sorted(defs),
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


if __name__ == "__main__":
    main()
