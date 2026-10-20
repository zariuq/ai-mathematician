"""Give Duper the room the throttle has been denying it.

Duper is the strongest reconstruction line we have -- 51 of the 109 goals
every other tactic failed on, and 2 of the 5 theorems the 300 s Vampire pass
added. In `Prover.prove` it is nonetheless the *last* line, it sees only the
first two premise sets, and the whole Duper phase is capped at 900 s. One of
this week's successes took 1864 s, so that cap was discarding proofs that
were on their way.

This runs the same `duper_tactics` scripts with the throttle opened:
every premise set, each attempt in its own Lean process with a long single
timeout, and a per-goal budget set from the evidence rather than from
caution. Everything still goes through the ordinary guard.

Usage: python3 try_duper_hard.py <targets.jsonl> <workers> <out.jsonl>
                                 [--per-goal S] [--single S] [--resume]
"""
import json
import os
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover, duper_tactics
from duper2 import duper2_tactics

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
    row, per_goal, single, hb = args
    p = _init()
    g = p.by_name[row["goal"]]
    sets = row.get("premise_sets") or [row.get("premises") or []]
    defs = row.get("defs") or []
    t0 = time.time()
    tried = []
    gdefs = p.goal_defs(g)
    for j, ps in enumerate(sets, start=1):          # every set, not just two
        for lbl, script in duper2_tactics(ps, defs, gdefs) + duper_tactics(ps, defs):
            if time.time() - t0 > per_goal:
                return {"goal": g.name, "proved_by": None,
                        "why": "per-goal budget", "tried": tried,
                        "secs": round(time.time() - t0, 1)}
            res = p.attempt_batch(g, [(f"{lbl}#{j}", script)],
                                  timeout=single + 30, single_timeout=single,
                                  max_retry_secs=0, heartbeats=hb,
                                  duper=True)
            lab, ok, why = res[0]
            tried.append([lab, bool(ok), why[:80]])
            if ok:
                return {"goal": g.name, "proved_by": lab, "tried": tried,
                        "secs": round(time.time() - t0, 1)}
    return {"goal": g.name, "proved_by": None, "why": "exhausted",
            "tried": tried, "secs": round(time.time() - t0, 1)}


def main():
    src, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    rest = sys.argv[4:]
    per_goal = int(rest[rest.index("--per-goal") + 1]) if "--per-goal" in rest else 3600
    single = int(rest[rest.index("--single") + 1]) if "--single" in rest else 1800
    hb = int(rest[rest.index("--hb") + 1]) if "--hb" in rest else 4000000
    rows = [json.loads(l) for l in open(src)]
    if "--resume" in rest and os.path.exists(out):
        seen = {json.loads(l)["goal"] for l in open(out)}
        rows = [r for r in rows if r["goal"] not in seen]
    print(f"{len(rows)} goals, {workers} workers, "
          f"per-goal {per_goal}s, per-attempt {single}s, heartbeats {hb}", flush=True)
    _init()
    n = won = 0
    with ThreadPoolExecutor(max_workers=workers) as ex, \
            open(out, "a" if "--resume" in rest else "w") as fh:
        for r in ex.map(_run, ((x, per_goal, single, hb) for x in rows)):
            n += 1
            won += bool(r["proved_by"])
            with _out:
                fh.write(json.dumps(r) + "\n")
                fh.flush()
            tag = f"*** PROVED by {r['proved_by']}" if r["proved_by"] else ""
            print(f"{n}/{len(rows)} {r['goal'][:34]:<34} {r['secs']:>7}s "
                  f"{len(r['tried'])} tries  {tag}", flush=True)
    print(f"\nDuper recovered {won}/{n}", flush=True)


if __name__ == "__main__":
    main()
