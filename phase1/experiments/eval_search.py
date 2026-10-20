"""Compare Search variants by premise recall: of the facts a theorem's real
proof cited, what fraction appear in Search's top-k (and for how many
theorems were ALL of them found)?

Reported on three sets so tuning cannot flatter the result:
  tune  -- theorems in the first half of the library (settings chosen here)
  test  -- theorems in the second half (never used to choose settings)
  fail  -- the 327 non-induction theorems where Vampire found no proof in
           the v1 run: the set better Search is meant to rescue.

Usage: python3 eval_search.py [baseline.jsonl]
"""
import json
import re
import sys
from multiprocessing import Pool

from library import load
from search import Search

CORPUS = "../data/corpus.sexpr"
KS = (16, 32, 64)
decls = load(CORPUS)
S = Search(decls)
IND = re.compile(r"_ind$|_ind_|induction")

VARIANTS = {
    "current": {},
    "nb only": {"nb_w": 4.0, "knn_w": 0.0},
    "current+nb": {"nb_w": 3.0},
    "current+nb strong": {"nb_w": 6.0},
    "current+nb, no knn": {"nb_w": 3.0, "knn_w": 0.0},
}


def one(args):
    idx, kw = args
    return [n for n, _ in S.rank(idx, limit=max(KS), **kw)]


def report(name, rows):
    n = len(rows)
    cells = []
    for k in KS:
        rec = sum(len(set(r[:k]) & deps) / len(deps) for r, deps in rows) / n
        full = sum(set(r[:k]) >= deps for r, deps in rows)
        cells.append(f"@{k} {rec:5.1%} all:{full/n:5.1%}")
    print(f"  {name:6s} n={n:4d}  " + "  ".join(cells))


def main():
    thms = [d for d in decls if d.kind == "THM" and d.proof_deps]
    half = decls[len(decls) // 2].index
    fail = set()
    if len(sys.argv) > 1:
        for l in open(sys.argv[1]):
            r = json.loads(l)
            if r["proved_by"] or r["vampire"].startswith("Theorem"):
                continue
            d = next(x for x in thms if x.name == r["goal"]) if any(
                x.name == r["goal"] for x in thms) else None
            if d and not any(IND.search(p) for p in d.proof_deps):
                fail.add(d.name)
    print(f"fail set: {len(fail)} non-induction Vampire failures")
    with Pool(16) as pool:
        for vname, kw in VARIANTS.items():
            ranked = pool.map(one, [(d.index, kw) for d in thms], chunksize=8)
            rows = list(zip(ranked, [d.proof_deps for d in thms]))
            print(vname)
            report("tune", [x for x, d in zip(rows, thms) if d.index < half])
            report("test", [x for x, d in zip(rows, thms) if d.index >= half])
            if fail:
                report("fail", [x for x, d in zip(rows, thms) if d.name in fail])


if __name__ == "__main__":
    main()
