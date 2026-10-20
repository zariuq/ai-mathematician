"""LLM intervention on theorems the deterministic pipeline failed.

Input: a baseline results file (experiment.py output). Selects failures,
feeds each to the LLM feedback loop with the SAME premises/definitions the
baseline computed (Vampire's premise set where it found a proof), so every
model sees identical input. Every success passes Lean's kernel, the
statement check and the leak guard -- the same bar as the baseline.

Usage:
  python3 llm_experiment.py <baseline.jsonl> <model> <rounds> <workers> \
      <out.jsonl> [--vampire-only] [--every N]
"""
import argparse
import json
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover
from llm import llm_rounds, usage_summary
from dsp import dsp_rounds

CORPUS = "../data/corpus.sexpr"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("baseline")
    ap.add_argument("model")
    ap.add_argument("rounds", type=int)
    ap.add_argument("workers", type=int)
    ap.add_argument("out")
    ap.add_argument("--vampire-only", action="store_true",
                    help="only failures where Vampire DID find a proof")
    ap.add_argument("--every", type=int, default=1,
                    help="take every Nth selected failure (fixed sample)")
    ap.add_argument("--limit", type=int, default=None,
                    help="at most this many theorems")
    ap.add_argument("--skip", type=int, default=0,
                    help="skip the first N of the selected sample (e.g. ones "
                         "already run in a smoke test)")
    ap.add_argument("--mode", choices=("direct", "dsp"), default="direct",
                    help="direct: LLM writes Lean with error feedback; "
                         "dsp: informal proof -> Lean outline -> automation "
                         "fills gaps (rounds = repair rounds)")
    a = ap.parse_args()

    decls = load(CORPUS)
    by = {d.name: d for d in decls}
    prover = Prover(decls, CORPUS, load_statements())

    rows = [json.loads(l) for l in open(a.baseline)]
    todo = [r for r in rows if not r["proved_by"]]
    if a.vampire_only:
        todo = [r for r in todo if r["vampire"].startswith("Theorem")]
    todo = todo[::a.every][:a.limit][a.skip:]
    print(f"{len(todo)} theorems, model={a.model}, rounds={a.rounds}", flush=True)

    def run(r):
        g = by[r["goal"]]
        premises = r["premises"]
        if not r["vampire"].startswith("Theorem"):
            premises = [n for n, _ in prover.search.rank(g.index, limit=24)
                        if by[n].kind in ("THM", "AXIOM")][:16]
        t0 = time.time()
        if a.mode == "dsp":
            label, tr = dsp_rounds(prover, g, premises, r["defs"],
                                   repair_rounds=a.rounds, model=a.model)
        else:
            label, tr = llm_rounds(prover, g, premises, r["defs"],
                                   rounds=a.rounds, model=a.model)
        return {"goal": g.name, "model": a.model, "proved_by": label,
                "rounds_used": len(tr), "secs": round(time.time() - t0, 1),
                "transcript": tr}

    t0 = time.time()
    won = 0
    with ThreadPoolExecutor(max_workers=a.workers) as ex, open(a.out, "w") as fh:
        for res in ex.map(run, todo):
            won += bool(res["proved_by"])
            fh.write(json.dumps(res) + "\n")
            fh.flush()
            print(f"{'PROVED' if res['proved_by'] else 'failed':7s} "
                  f"{res['goal'][:40]:40s} {res['proved_by'] or ''} "
                  f"({res['secs']}s)", flush=True)
    print(f"\n{a.model}: proved {won}/{len(todo)} "
          f"({won/max(1,len(todo)):.0%}) in {time.time()-t0:.0f}s")
    print("API usage (ledger):", usage_summary())


if __name__ == "__main__":
    main()
