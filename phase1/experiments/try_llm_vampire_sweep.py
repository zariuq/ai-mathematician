"""A/B test: does Vampire's PROOF in the prompt help the LLM where the Lean
rebuild failed?

Targets: the goals in the v4 run where Vampire found a proof but every Lean
line failed. Both arms get the SAME facts and definitions -- those of one
cached Vampire proof per goal -- and differ only in whether the proof text
is in the prompt. Every success passes the usual Lean checks (kernel,
statement identity, leak guard).

  python3 try_llm_vampire_sweep.py prep <cache.jsonl> [procs]
      run Vampire once per target goal, cache proof text + facts + defs
  python3 try_llm_vampire_sweep.py run <cache.jsonl> <out.jsonl> proof|noproof
                                   [--model M] [--rounds N] [--workers W]
  prep [--timeout S] [--targets-from cache.jsonl] retries goals without a proof
  prep-search <cache.jsonl> [--facts N]: Search-only rows for EVERY goal no
       run has proved yet (for the noproof arm, and as Vampire targets)
  run  [--examples N] adds N accepted proofs of similar earlier theorems
       [--skip-proved-in a.jsonl,b.jsonl] skips goals already proved there
       [--mode dsp] plan-and-fill (experiments/dsp.py) instead of the loop
       [--mode decompose] plan, then prove stuck steps as lemmas (decompose.py)
      LLM_LEDGER / LLM_CALL_CAP bound the spend, as in try_llm_sweep.py
"""
import json
import os
import sys
import threading
import time
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover

CORPUS = "../data/corpus.sexpr"
RUN = "../results/phase1_full_v4.jsonl"
_prover = None
_lock = threading.Lock()
_stop = threading.Event()


def _init():
    global _prover
    with _lock:
        if _prover is None:
            _prover = Prover(load(CORPUS), CORPUS, load_statements())
    return _prover


def targets():
    return [r["goal"] for r in map(json.loads, open(RUN))
            if str(r.get("vampire")).startswith("Theorem") and not r["proved_by"]]


def proved_anywhere(results_dir="../results"):
    """Goals any result file records as proved (union of every run)."""
    import glob
    done = set()
    for f in glob.glob(os.path.join(results_dir, "*.jsonl")):
        if "ledger" in f or "usage" in f:
            continue
        for l in open(f):
            try:
                r = json.loads(l)
            except Exception:
                continue
            if isinstance(r, dict) and r.get("goal") and (
                    r.get("proved_by") or r.get("ok") is True):
                done.add(r["goal"])
    return done


def unproved():
    """Every v4 goal no run has proved yet, in library order."""
    done = proved_anywhere()
    return [r["goal"] for r in map(json.loads, open(RUN)) if r["goal"] not in done]


def prep_search(cache, n_facts=24):
    """Rows without a Vampire proof for every unproved goal: Search's top
    facts (only declarations before the goal) and the goal's definitions."""
    p = _init()
    names = unproved()
    with open(cache, "w") as fh:
        for n in names:
            g = p.by_name[n]
            facts = [x for x, _ in p.search.rank(g.index, limit=n_facts * 2)
                     if p.by_name[x].kind in ("THM", "AXIOM")][:n_facts]
            fh.write(json.dumps({"goal": n, "k": 0, "facts": facts,
                                 "defs": p.goal_defs(g), "proof": None}) + "\n")
    print(f"{len(names)} unproved goals -> {cache}", flush=True)


def _prep(args):
    from vampire_proof import proof_for_llm
    name, timeout = args
    p = _init()
    t0 = time.time()
    got = proof_for_llm(p, p.by_name[name], timeout=timeout)
    if got is None:
        return {"goal": name, "proof": None, "secs": round(time.time() - t0, 1)}
    proof, facts, vdefs, k = got
    defs = sorted(set(vdefs) | set(p.goal_defs(p.by_name[name])))
    return {"goal": name, "k": k, "facts": facts, "defs": defs, "proof": proof,
            "secs": round(time.time() - t0, 1)}


def prep(cache, procs, timeout=30, names=None):
    """Cache one Vampire proof per target. Goals already cached WITH a
    proof are skipped; goals cached without one are retried (use a longer
    timeout), and the newest row for a goal is the one `run` uses."""
    names = names or targets()
    done = set()
    if os.path.exists(cache):
        done = {r["goal"] for r in map(json.loads, open(cache)) if r["proof"]}
    todo = [n for n in names if n not in done]
    print(f"{len(names)} targets, {len(todo)} to prep, {procs} procs, "
          f"{timeout}s per slice", flush=True)
    with ProcessPoolExecutor(procs) as ex, open(cache, "a") as fh:
        for i, r in enumerate(ex.map(_prep, ((n, timeout) for n in todo)), 1):
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            st = f"k={r['k']} {len(r['facts'])} facts {len(r['proof'])} chars" \
                if r["proof"] else "NO PROOF"
            print(f"{i}/{len(todo)} {r['goal']:<36} {st} ({r['secs']}s)", flush=True)


POOL = "../results/llm_proof_pool.json"


def examples_for(p, goal, n):
    """Accepted proofs of the n theorems most similar to the goal, drawn
    only from theorems strictly BEFORE it (same leak discipline as Search)."""
    if not n or not os.path.exists(POOL):
        return None
    pool = json.load(open(POOL))
    syms = set(goal.stmt_syms)
    cands = [(p.search._overlap(syms, p.by_name[g]), g) for g in pool
             if g in p.by_name and p.by_name[g].index < goal.index
             and g in p.sigs]
    best = [g for sc, g in sorted(cands, reverse=True)[:n] if sc > 0]
    return [(g, p.sigs[g], pool[g]) for g in best] or None


def _run(args):
    from llm import llm_rounds, BudgetExhausted
    row, arm, model, rounds, n_ex, mode = args
    name = row["goal"]
    if _stop.is_set():
        return {"goal": name, "arm": arm, "proved_by": None, "why": "budget exhausted"}
    p = _init()
    g = p.by_name[name]
    t0 = time.time()
    try:
        if mode == "decompose":
            # plan, then prove each stuck step as its own lemma (decompose.py)
            from decompose import decompose_rounds
            label, tr = decompose_rounds(p, g, row["facts"], row["defs"],
                                         repair_rounds=max(rounds - 1, 0), model=model,
                                         examples=examples_for(p, g, n_ex))
        elif mode == "dsp":
            # plan with the LLM, fill each `sorry` step with the hammer
            from dsp import dsp_rounds
            label, tr = dsp_rounds(p, g, row["facts"], row["defs"],
                                   repair_rounds=max(rounds - 1, 0), model=model,
                                   examples=examples_for(p, g, n_ex))
        else:
            label, tr = llm_rounds(p, g, row["facts"], row["defs"], rounds=rounds,
                                   model=model,
                                   atp_proof=row["proof"] if arm == "proof" else None,
                                   examples=examples_for(p, g, n_ex))
    except BudgetExhausted:
        _stop.set()
        return {"goal": name, "arm": arm, "proved_by": None, "why": "budget exhausted"}
    except Exception as e:
        return {"goal": name, "arm": arm, "proved_by": None,
                "why": f"{type(e).__name__}: {e}"}
    return {"goal": name, "arm": arm, "proved_by": label, "k": row["k"],
            "secs": round(time.time() - t0, 1), "transcript": tr}


def run(cache, out, arm, model, rounds, workers, n_ex=0, only_failed=None, mode="loop"):
    rows = list({r["goal"]: r for r in map(json.loads, open(cache))}.values())
    # the proof arm needs a Vampire proof; the noproof arm runs on any row
    rows = [r for r in rows if r["proof"] or (arm != "proof" and r.get("facts") is not None)]
    if os.path.exists(out):
        seen = {json.loads(l)["goal"] for l in open(out)
                if "budget exhausted" not in l}
        rows = [r for r in rows if r["goal"] not in seen]
    if only_failed:
        # only goals no earlier result file has proved
        done = set()
        for f in only_failed.split(","):
            if os.path.exists(f):
                done |= {r["goal"] for r in map(json.loads, open(f))
                         if r.get("proved_by")}
        rows = [r for r in rows if r["goal"] not in done]
    print(f"{len(rows)} goals, arm={arm}, model={model}, rounds<={rounds}, "
          f"cap={os.environ.get('LLM_CALL_CAP')}, workers={workers}", flush=True)
    _init()
    n = won = 0
    with ThreadPoolExecutor(workers) as ex, open(out, "a") as fh:
        for r in ex.map(_run, ((x, arm, model, rounds, n_ex, mode) for x in rows)):
            n += 1
            won += bool(r["proved_by"])
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            tag = f"*** PROVED by {r['proved_by']}" if r["proved_by"] else r.get("why", "")
            print(f"{n}/{len(rows)} {r['goal'][:36]:<36} {tag}", flush=True)
    print(f"\n[{arm}] LLM proved {won}/{n}", flush=True)


if __name__ == "__main__":
    cmd, rest = sys.argv[1], sys.argv[2:]
    opt = lambda k, d: rest[rest.index(k) + 1] if k in rest else d
    if cmd == "prep":
        names = None
        if "--targets-from" in rest:
            names = [r["goal"] for r in map(json.loads, open(opt("--targets-from", "")))]
        prep(rest[0], int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 6,
             int(opt("--timeout", "30")), names)
    elif cmd == "prep-search":
        prep_search(rest[0], int(opt("--facts", "24")))
    else:
        run(rest[0], rest[1], rest[2], opt("--model", "deepseek/deepseek-v4-flash-0731"),
            int(opt("--rounds", "3")), int(opt("--workers", "3")),
            int(opt("--examples", "0")), opt("--skip-proved-in", None),
            opt("--mode", "loop"))
