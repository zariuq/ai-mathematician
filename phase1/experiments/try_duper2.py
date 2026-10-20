"""Second Duper pass on group-A goals the first pass missed: all premise
sets combined, and Duper's expensive higher-order rules switched on.

Usage: python3 try_duper2.py <goals.jsonl> <workers> <out.jsonl>
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements, BRIDGE
from prover import Prover

CORPUS = "../data/corpus.sexpr"
EXP = " {includeExpensiveRules := true}"


def cands_for(r):
    union = []
    for ps in r["premise_sets"]:
        union += [p for p in ps if p not in union]
    unfold = ", ".join([BRIDGE] + [f"«{d}»" for d in r["defs"]])
    out = []
    for tag, P in (("union", union), ("set1", r["premise_sets"][0])):
        haves = "".join(f"have hp{i} := @«{p}»\n" for i, p in enumerate(P))
        for utag, u in (("", BRIDGE), ("-unfold", unfold)):
            out.append((f"duper2-{tag}{utag}-exp",
                        f"intros\n{haves}(try simp only [{u}] at *)\nduper [*]{EXP}"))
        if tag == "union" and len(r["premise_sets"]) > 1:
            haves_u = haves
            out.append((f"duper2-union-unfold",
                        f"intros\n{haves_u}(try simp only [{unfold}] at *)\nduper [*]"))
    return out


def main():
    src, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    decls = load(CORPUS)
    by = {d.name: d for d in decls}
    prover = Prover(decls, CORPUS, load_statements())
    todo = [json.loads(l) for l in open(src)]
    print(f"{len(todo)} goals", flush=True)

    def run(r):
        g = by[r["goal"]]
        t0 = time.time()
        cands = cands_for(r)
        res = prover.attempt_batch(g, cands, timeout=500, single_timeout=180,
                                   max_retry_secs=720, heartbeats=2000000, duper=True)
        wins = [l for l, ok, _ in res if ok]
        return {"goal": g.name, "wins": wins,
                "scripts": {l: s for l, s in cands if l in wins},
                "secs": round(time.time() - t0, 1)}

    won = 0
    with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
        for r in ex.map(run, todo):
            won += bool(r["wins"])
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            print(f"{'PROVED' if r['wins'] else 'failed':7s} {r['goal'][:40]:40s} "
                  f"{','.join(r['wins'][:2])} ({r['secs']}s)", flush=True)
    print(f"\nDuper pass 2 rebuilds {won}/{len(todo)}")


if __name__ == "__main__":
    main()
