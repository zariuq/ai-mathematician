"""Quick ATP-only probe: for a sample of theorems, can Vampire prove the
goal from Search's top-k premises? Measures the ATP stage in isolation --
nothing here is checked by Lean yet, so these are NOT verified results."""
import sys
import time

from library import load
from search import Search
from atp import THF, attach_prim_indices, run_vampire, Unsupported

corpus = sys.argv[1] if len(sys.argv) > 1 else "../data/corpus.sexpr"
step = int(sys.argv[2]) if len(sys.argv) > 2 else 10
k = int(sys.argv[3]) if len(sys.argv) > 3 else 32
t = int(sys.argv[4]) if len(sys.argv) > 4 else 5

decls = load(corpus)
search = Search(decls)
thf = THF(decls)
attach_prim_indices(thf, corpus)

thms = [d for d in decls if d.kind == "THM"][::step]
stats = {}
t0 = time.time()
for d in thms:
    prem = [n for n, _ in search.rank(d.index, limit=k)]
    try:
        text, ids, skipped = thf.problem(d, prem)
    except Unsupported as e:
        stats["unsupported"] = stats.get("unsupported", 0) + 1
        continue
    status, used = run_vampire(text, timeout=t)
    stats[status] = stats.get(status, 0) + 1
print(f"sample: {len(thms)} theorems, top-{k} premises, {t}s Vampire, "
      f"{time.time()-t0:.0f}s total")
for s, c in sorted(stats.items(), key=lambda x: -x[1]):
    print(f"  {s:20s} {c}")
