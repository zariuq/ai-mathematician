"""Re-check the scripts an LLM sweep already produced, with the mechanical
repairs of llm.repair_variants -- no LLM calls. Same arm, same scripts, same
Lean checks; only the repairs are new.

  python3 recheck_vp_repairs.py <cache.jsonl> <sweep.jsonl> <out.jsonl> [workers]
"""
import json
import sys
import threading
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover
from llm import repair_variants

CORPUS = "../data/corpus.sexpr"
cache_path, sweep_path, out_path = sys.argv[1:4]
workers = int(sys.argv[4]) if len(sys.argv) > 4 else 4
p = Prover(load(CORPUS), CORPUS, load_statements())
cache = {r["goal"]: r for r in map(json.loads, open(cache_path))}
rows = [r for r in map(json.loads, open(sweep_path)) if not r["proved_by"]]
lock = threading.Lock()


def one(r):
    g = p.by_name[r["goal"]]
    facts = cache[r["goal"]]["facts"]
    cands = []
    for t in r.get("transcript") or []:
        if t.get("script"):
            cands += repair_variants(t["script"], t.get("why") or "", facts,
                                     f"llm-r{t['round']}")
    if not cands:
        return {"goal": r["goal"], "proved_by": None, "n": 0}
    for (lbl, ok, why), (_, s) in zip(p.attempt_batch(g, cands), cands):
        if ok:
            return {"goal": r["goal"], "proved_by": lbl, "script": s, "n": len(cands)}
    return {"goal": r["goal"], "proved_by": None, "n": len(cands)}


won = 0
with ThreadPoolExecutor(workers) as ex, open(out_path, "w") as fh:
    for i, res in enumerate(ex.map(one, rows), 1):
        won += bool(res["proved_by"])
        fh.write(json.dumps(res) + "\n")
        fh.flush()
        tag = f"*** PROVED by {res['proved_by']}" if res["proved_by"] else ""
        print(f"{i}/{len(rows)} {res['goal']:<36} {res['n']} variants {tag}", flush=True)
print(f"\nrepairs proved {won}/{len(rows)}", flush=True)
