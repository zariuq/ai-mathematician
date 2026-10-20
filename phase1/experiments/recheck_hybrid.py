"""Re-verify hybrid-induction proofs in fresh Lean processes.

Each recorded proof (lifted case lemmas + the assembled induction script) is
re-elaborated from scratch against the library statement, with the standard
statement-identity, sorryAx and leak guard -- nothing from the search run is
reused except the proof text itself.

Usage: python3 recheck_hybrid.py <hybrid.jsonl> [out.jsonl]
"""
import json
import sys

from library import load
from itp import load_statements
from prover import Prover

CORPUS = "../data/corpus.sexpr"


def main():
    rows = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
    rows = [r for r in rows if r.get("proved_by")]
    p = Prover(load(CORPUS), CORPUS, load_statements())
    out = open(sys.argv[2], "w") if len(sys.argv) > 2 else None
    ok_n = 0
    for r in rows:
        g = p.by_name[r["goal"]]
        (_, ok, why), = p.attempt_batch(g, [("recheck", r["script"])], timeout=900,
                                        single_timeout=900, heartbeats=1000000,
                                        duper=r.get("duper", False),
                                        prelude=r["prelude"])
        ok_n += ok
        print(f"{r['goal']:<32} {'OK' if ok else 'FAIL'}  {why[:100]}", flush=True)
        if out:
            out.write(json.dumps({"goal": r["goal"], "ok": ok, "why": why}) + "\n")
    print(f"\nre-verified {ok_n}/{len(rows)}")


if __name__ == "__main__":
    main()
