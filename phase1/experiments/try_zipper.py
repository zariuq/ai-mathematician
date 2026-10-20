"""Pilot Zipperposition on the goals Vampire times out on.

Usage: python3 try_zipper.py <run.jsonl> <workers> <out.jsonl> [limit]
                             [--timeout S] [--slices a,b,c] [--resume]
"""
import json
import os
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover
from atp import Unsupported
from zipper import run_zipperposition

CORPUS = "../data/corpus.sexpr"
_prover = None
_lock = threading.Lock()
_out = threading.Lock()


def _init():
    global _prover
    with _lock:
        if _prover is None:
            _prover = Prover(load(CORPUS), CORPUS, load_statements())
    return _prover


def _run(args):
    name, slices, tmo = args
    p = _init()
    g = p.by_name[name]
    ranked = [n for n, _ in p.search.rank(g.index, limit=max(slices), goal_obj=g)]
    t0 = time.time()
    found = []
    for k in slices:
        try:
            text, ids, _ = p.thf.problem(g, ranked[:k])
        except Unsupported:
            return {"goal": name, "zipper": "unsupported"}
        st, used = run_zipperposition(text, timeout=tmo)
        if st == "Theorem":
            facts = sorted({ids[u] for u in used if u in ids})
            found.append({"slice": k, "premises": facts})
            break                       # first proof is enough for a pilot
    return {"goal": name, "zipper": "Theorem" if found else "Timeout",
            "found": found, "secs": round(time.time() - t0, 1)}


def main():
    run, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    rest = sys.argv[4:]
    tmo = int(rest[rest.index("--timeout") + 1]) if "--timeout" in rest else 30
    slices = tuple(int(x) for x in rest[rest.index("--slices") + 1].split(",")) \
        if "--slices" in rest else (16, 32, 64, 128)
    # a bare digit is the limit, but only if it is not the VALUE of a flag --
    # scanning for any digit read "--timeout 30" as "limit 30"
    flagged = {rest[i + 1] for i, a in enumerate(rest[:-1]) if a.startswith("--")}
    limit = next((int(a) for a in rest if a.isdigit() and a not in flagged), None)

    rows = [json.loads(l) for l in open(run)]
    names = [r["goal"] for r in rows
             if not r.get("proved_by") and "Theorem" not in str(r.get("vampire"))]
    if "--resume" in rest and os.path.exists(out):
        seen = {json.loads(l)["goal"] for l in open(out)}
        names = [n for n in names if n not in seen]
    if limit:
        names = names[:limit]
    print(f"{len(names)} goals Vampire could not prove, "
          f"slices {slices}, {tmo}s each, {workers} workers", flush=True)
    _init()
    n = won = 0
    with ThreadPoolExecutor(max_workers=workers) as ex, \
            open(out, "a" if "--resume" in rest else "w") as fh:
        for r in ex.map(_run, ((x, slices, tmo) for x in names)):
            n += 1
            won += r["zipper"] == "Theorem"
            with _out:
                fh.write(json.dumps(r) + "\n")
                fh.flush()
            tag = (f"*** PROOF @{r['found'][0]['slice']} "
                   f"({len(r['found'][0]['premises'])} facts)") if r.get("found") else ""
            print(f"{n}/{len(names)} {r['goal'][:34]:<34} {tag}", flush=True)
    print(f"\nZipperposition proved {won}/{n} that Vampire could not", flush=True)


if __name__ == "__main__":
    main()
