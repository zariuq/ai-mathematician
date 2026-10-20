"""Re-verify, from scratch, every proof the Vampire-proof LLM work claims.

Collects the accepted script for each goal from the given result files
(sweep transcripts or repair rechecks), re-checks each one alone in a fresh
Lean run with the full guard (kernel, statement identity, leak guard), and
writes the ones that pass again. Only these are counted.

  python3 verify_vp_final.py <out.json> <result.jsonl> [<result.jsonl> ...]
"""
import json
import os
import sys
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover

CORPUS = "../data/corpus.sexpr"


def scripts(path):
    for r in map(json.loads, open(path)):
        if not r.get("proved_by"):
            continue
        if r.get("script"):
            yield r["goal"], r["script"], path, r.get("prelude", "")
            continue
        ok = [t for t in r.get("transcript") or [] if t.get("ok") and t.get("script")]
        if ok:
            # decompose.py proofs cite lemmas proved alongside them (prelude)
            yield r["goal"], ok[-1]["script"], path, ok[-1].get("prelude", "")


def main():
    out, paths = sys.argv[1], sys.argv[2:]
    claims = {}
    missing = [x for x in paths if not os.path.exists(x)]
    if missing:
        print("skipping missing:", " ".join(missing), flush=True)
    for path in (x for x in paths if os.path.exists(x)):
        for goal, script, src, prelude in scripts(path):
            claims.setdefault(goal, []).append((script, src, prelude))
    p = Prover(load(CORPUS), CORPUS, load_statements())

    def check(goal):
        # every distinct claimed script for this goal; keep the first that passes
        for script, src, prelude in dict.fromkeys(claims[goal]):
            (_, ok, why), = p.attempt_batch(p.by_name[goal], [("verify", script)],
                                            prelude=prelude, timeout=600,
                                            single_timeout=600)
            if ok:
                return goal, {"script": script, "source": src, "prelude": prelude}
        return goal, None

    verified, failed = {}, []
    with ThreadPoolExecutor(4) as ex:
        for goal, res in ex.map(check, sorted(claims)):
            if res:
                verified[goal] = res
            else:
                failed.append(goal)
            print(f"{goal:<36} {'ok' if res else 'FAILED re-check'}", flush=True)
    json.dump({"verified": verified, "failed_recheck": failed}, open(out, "w"),
              indent=1)
    print(f"\nre-verified {len(verified)}/{len(claims)} claimed proofs", flush=True)


if __name__ == "__main__":
    main()
