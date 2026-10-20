"""Oracle premise test on goals the given run left without a Vampire proof:
give Vampire exactly the facts the ORIGINAL proof cited (never used for
proving; a diagnostic of how much premise selection could still gain).

Usage: python3 oracle_v3.py <run.jsonl> <workers> <out.jsonl> [extra_vampire_runs...]
"""
import json
import re
import sys
from concurrent.futures import ThreadPoolExecutor

from library import load
from atp import THF, attach_prim_indices, run_vampire, Unsupported

CORPUS = "../data/corpus.sexpr"
IND = re.compile(r"_ind$|_ind_|induction")


def main():
    src, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    decls = load(CORPUS)
    by = {d.name: d for d in decls}
    thf = THF(decls)
    attach_prim_indices(thf, CORPUS)
    found = set()
    for f in sys.argv[4:]:
        for l in open(f):
            r = json.loads(l)
            if r["vampire"].startswith("Theorem"):
                found.add(r["goal"])
    todo = [by[r["goal"]] for r in map(json.loads, open(src))
            if not r["proved_by"] and not r["vampire"].startswith("Theorem")
            and r["goal"] not in found]
    print(f"{len(todo)} goals", flush=True)

    def run(g):
        prem = sorted(g.proof_deps)
        ind = any(IND.search(p) for p in prem)
        try:
            text, _, _ = thf.problem(g, prem)
        except Unsupported:
            return g.name, ind, "unsupported"
        st, _ = run_vampire(text, timeout=30)
        return g.name, ind, st

    res = []
    with ThreadPoolExecutor(max_workers=workers) as ex:
        res = list(ex.map(run, todo))
    json.dump(res, open(out, "w"))
    for grp, flag in (("induction", True), ("non-induction", False)):
        rs = [r for r in res if r[1] == flag]
        ok = sum(r[2] == "Theorem" for r in rs)
        print(f"{grp}: {len(rs)} goals, Vampire proves {ok} with the original proof's facts")


if __name__ == "__main__":
    main()
