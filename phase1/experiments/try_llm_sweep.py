"""Run the LLM proposer over every goal the deterministic pipeline still
misses -- the last stage of the Phase 1 design.

The model is untrusted, exactly like Vampire: it proposes Lean tactic
scripts, and every script goes through `attempt_batch` with the ordinary
guard (statement identity against the library declaration, no sorryAx, no
leak). A success here counts for the same reason the 645 do.

Spending is bounded by llm.CALL_CAP, which is counted in a ledger under a
file lock before each request, so the cap holds across threads and survives
a crash. Point LLM_LEDGER at a fresh file for each budgeted run.

Usage: python3 try_llm_sweep.py <run.jsonl> <workers> <out.jsonl>
                                [--model M] [--rounds N] [--resume]
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
from llm import llm_rounds, BudgetExhausted, DEFAULT_MODEL

CORPUS = "../data/corpus.sexpr"
_prover = None
_lock = threading.Lock()
_out_lock = threading.Lock()
_stop = threading.Event()


def _init():
    global _prover
    with _lock:
        if _prover is None:
            _prover = Prover(load(CORPUS), CORPUS, load_statements())
    return _prover


def _run(args):
    name, model, rounds, pre = args
    if _stop.is_set():
        return {"goal": name, "proved_by": None, "why": "budget exhausted"}
    p = _init()
    g = p.by_name[name]
    t0 = time.time()
    try:
        # Reuse the premise sets the run being extended already computed.
        # Recomputing them means six Vampire slices per goal -- up to three
        # minutes of CPU each, before the model is even asked -- for premises
        # that are already on disk and would come back identical.
        premises, defs, vstat = pre
        if not vstat.startswith("Theorem"):
            # no Vampire proof to lean on: give the model Search's top facts
            premises = [n for n, _ in p.search.rank(g.index, limit=24)
                        if p.by_name[n].kind in ("THM", "AXIOM")][:16]
        label, _ = llm_rounds(p, g, premises, defs, rounds=rounds, model=model)
    except BudgetExhausted:
        _stop.set()
        return {"goal": name, "proved_by": None, "why": "budget exhausted"}
    except Exception as e:
        return {"goal": name, "proved_by": None,
                "why": f"{type(e).__name__}: {e}"}
    return {"goal": name, "proved_by": label, "vampire": vstat,
            "secs": round(time.time() - t0, 1)}


def main():
    run, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    rest = sys.argv[4:]
    model = rest[rest.index("--model") + 1] if "--model" in rest else DEFAULT_MODEL
    rounds = int(rest[rest.index("--rounds") + 1]) if "--rounds" in rest else 2

    rows = [json.loads(l) for l in open(run)]
    pre = {r["goal"]: ((r.get("premises") or []), (r.get("defs") or []),
                       str(r.get("vampire") or ""))
           for r in rows}
    names = [r["goal"] for r in rows if not r.get("proved_by")]
    # drop the ones the 300 s Vampire pass has since closed
    done_path = "../results/t300_rebuild.jsonl"
    if os.path.exists(done_path):
        for l in open(done_path):
            try:
                r = json.loads(l)
            except Exception:
                continue
            if r.get("proved_by") and r["goal"] in names:
                names.remove(r["goal"])
    if "--resume" in rest and os.path.exists(out):
        seen = {json.loads(l)["goal"] for l in open(out)}
        names = [n for n in names if n not in seen]

    print(f"{len(names)} goals, model={model}, rounds<={rounds}, "
          f"cap={os.environ.get('LLM_CALL_CAP')}, workers={workers}", flush=True)
    _init()
    n = won = 0
    with ThreadPoolExecutor(max_workers=workers) as ex, \
            open(out, "a" if "--resume" in rest else "w") as fh:
        for r in ex.map(_run, ((x, model, rounds, pre[x]) for x in names)):
            n += 1
            won += bool(r["proved_by"])
            with _out_lock:
                fh.write(json.dumps(r) + "\n")
                fh.flush()
            tag = f"*** PROVED by {r['proved_by']}" if r["proved_by"] else ""
            print(f"{n}/{len(names)} {r['goal'][:36]:<36} {tag}", flush=True)
    print(f"\nLLM added {won}/{n}", flush=True)


if __name__ == "__main__":
    main()
