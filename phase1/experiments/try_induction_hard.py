"""Stop discarding induction splits over a 5-second Vampire call.

`Prover.induction_split` accepts a split only if Vampire proves EVERY case,
and `_vampire_case` gives it 5 s at slices 16/32/64. Everywhere else in the
pipeline Vampire gets 30 s and up to 512 facts. The recogniser proposes a
usable split for 87 of the 88 failing goals whose proofs need a principle it
knows, yet only 20 survive that filter -- and when a split does get through,
Lean closes it 70% of the time.

This re-runs the induction line with the ATP budget the rest of the pipeline
uses, and -- with --lean-anyway -- hands a split to Lean even when Vampire
could not discharge every case, since Lean's battery and Duper may still
close them.

Usage: python3 try_induction_hard.py <run.jsonl> <workers> <out.jsonl>
                                     [--timeout S] [--slices a,b,c]
                                     [--lean-anyway] [--resume]
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
    name, slices, tmo, anyway = args
    p = _init()
    g = p.by_name[name]
    t0 = time.time()
    ranked = [n for n, _ in p.search.rank(g.index, limit=max(slices), goal_obj=g)]
    best = None
    for pname, xi, gi, cases in p.inductor.splits(g):
        used, missing = [], 0
        for c in cases:
            u = p._vampire_case(c, ranked, slices, timeout=tmo)
            if u is None:
                missing += 1
                # Lean may still close this case from Search's own facts
                u = [n for n in ranked if p.by_name[n].kind in ("THM", "AXIOM")][:8]
            used.append(u)
        if missing == 0:
            best = {"principle": pname, "x": xi, "guard": gi,
                    "case_premises": used, "missing": 0}
            break
        if anyway and best is None:
            best = {"principle": pname, "x": xi, "guard": gi,
                    "case_premises": used, "missing": missing}
    if best is None:
        return {"goal": name, "proved_by": None, "why": "no split",
                "secs": round(time.time() - t0, 1)}
    try:
        ok, why, script = p.induction_lean(g, best)
    except Exception as e:
        return {"goal": name, "proved_by": None,
                "why": f"{type(e).__name__}: {e}", "split": best["principle"],
                "secs": round(time.time() - t0, 1)}
    return {"goal": name, "proved_by": f"induction:{best['principle']}" if ok else None,
            "split": best["principle"], "missing_cases": best["missing"],
            "why": why, "secs": round(time.time() - t0, 1)}


def main():
    run, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    rest = sys.argv[4:]
    tmo = int(rest[rest.index("--timeout") + 1]) if "--timeout" in rest else 30
    slices = tuple(int(x) for x in rest[rest.index("--slices") + 1].split(",")) \
        if "--slices" in rest else (16, 32, 64, 128, 256)
    anyway = "--lean-anyway" in rest

    decls_names = None
    rows = [json.loads(l) for l in open(run)]
    names = [r["goal"] for r in rows
             if not r.get("proved_by") and "Theorem" not in str(r.get("vampire"))]
    if "--resume" in rest and os.path.exists(out):
        seen = {json.loads(l)["goal"] for l in open(out)}
        names = [n for n in names if n not in seen]
    print(f"{len(names)} goals, slices {slices}, {tmo}s/case, "
          f"lean-anyway={anyway}, {workers} workers", flush=True)
    _init()
    n = won = 0
    with ThreadPoolExecutor(max_workers=workers) as ex, \
            open(out, "a" if "--resume" in rest else "w") as fh:
        for r in ex.map(_run, ((x, slices, tmo, anyway) for x in names)):
            n += 1
            won += bool(r["proved_by"])
            with _out:
                fh.write(json.dumps(r) + "\n")
                fh.flush()
            tag = f"*** PROVED {r['proved_by']}" if r["proved_by"] else (r.get("why") or "")[:40]
            print(f"{n}/{len(names)} {r['goal'][:32]:<32} {r['secs']:>7}s  {tag}", flush=True)
    print(f"\ninduction recovered {won}/{n}", flush=True)


if __name__ == "__main__":
    main()
