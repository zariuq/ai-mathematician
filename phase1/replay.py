"""Re-check every proof in the bundle from scratch: one command.

Each script from results/proof_bundle.jsonl (build_bundle.py) is checked on
its own, in a fresh Lean process, with the full guard: kernel, statement
identity, no sorryAx, only the library's own axioms and Lean's standard
ones, nothing cited from after the theorem in the library order.

  python3 replay.py [workers] [bundle.jsonl] [out.jsonl]

Writes one row per proof and exits non-zero if any proof fails.
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover

CORPUS = "../data/corpus.sexpr"
workers = int(sys.argv[1]) if len(sys.argv) > 1 else 4
src = sys.argv[2] if len(sys.argv) > 2 else "../results/proof_bundle.jsonl"
out = sys.argv[3] if len(sys.argv) > 3 else "../results/replay.jsonl"
decls = load(CORPUS)
by = {d.name: d for d in decls}
prover = Prover(decls, CORPUS, load_statements())
rows = [json.loads(l) for l in open(src)]


def check(r):
    t0 = time.time()
    duper = r["duper"]
    (_, ok, why), = prover.attempt_batch(
        by[r["goal"]], [("replay", r["script"])], prelude=r["prelude"], duper=duper,
        timeout=600 if duper else 300, single_timeout=600 if duper else 300,
        heartbeats=1000000 if duper else 200000)
    return {"goal": r["goal"], "origin": r["origin"], "ok": ok,
            "why": "" if ok else why[:500], "secs": round(time.time() - t0, 1)}


good, failed = 0, []
with ThreadPoolExecutor(workers) as ex, open(out, "w") as fh:
    for i, res in enumerate(ex.map(check, rows), 1):
        fh.write(json.dumps(res) + "\n")
        fh.flush()
        good += res["ok"]
        if not res["ok"]:
            failed.append(res)
            print(f"FAILED {res['goal']} ({res['origin']}): {res['why'].splitlines()[0][:150]}",
                  flush=True)
        if i % 50 == 0:
            print(f"  {i}/{len(rows)} checked, {len(failed)} failed", flush=True)
print(f"\nreplayed {good}/{len(rows)} proofs from scratch -> {out}")
sys.exit(1 if failed else 0)
