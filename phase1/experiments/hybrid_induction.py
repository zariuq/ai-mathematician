"""Hybrid induction: the inductor supplies the predicate, the whole
pipeline proves each case, and Lean assembles the result.

The induction line (Prover.induction_lean) splits a goal into the cases of a
principle and then tries only the cheap grind battery on each case, inline,
under the motive Lean inferred. The unstarved run (try_induction_hard.py)
showed where that breaks: 4/59 proved, and in 8 of the failures Vampire had
proved EVERY case -- the split was right and the ATP had the proof; only the
Lean replay failed. Duper, the line that rescues 51 of 109 ordinary replay
failures, was never tried on a case.

Here the provers support one another instead of each having to finish alone:

  1. the inductor proposes splits (it invents the predicate, which no
     saturation prover does);
  2. each case is lifted out as a stand-alone lemma and handed to the full
     Prover.prove cascade -- Vampire at every slice, the grind battery,
     followups, backward chaining, Duper;
  3. a case that still fails is split again (nested induction: step cases
     often need an inductive lemma of their own, e.g. distributivity needs
     an induction on the other argument);
  3b. for nat_ind splits, Vampire's OWN structural induction runs first,
     through smt_bridge (a Nat datatype bridge plus the inductor's motive
     as a named predicate). A proof there ranks the split first and its
     facts become an extra premise set for every case;
  4. Lean assembles the lemmas and the outer `apply principle` into one
     file and checks it with the ordinary statement-identity guard, so the
     final theorem is exactly the library's, sorry-free and leak-free
     (the guard walks through the lifted lemmas' own dependencies).

Usage: python3 hybrid_induction.py <names.txt|run.jsonl> <workers> <out.jsonl>
                                   [--depth D] [--splits K] [--resume]
"""
import json
import os
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover, candidate_tactics
from induction import lean_script
from oracle_haves import _HOP_GUARD, build_ctx
import sexpr_translate as T
from smt_bridge import run as run_smt
from atp import Unsupported

CORPUS = "../data/corpus.sexpr"
_prover = None
_decls = None
_lock = threading.Lock()


def _init():
    global _prover, _decls
    with _lock:
        if _prover is None:
            _decls = load(CORPUS)
            _prover = Prover(_decls, CORPUS, load_statements())
            _prover.enable_smt()
    return _prover


def _prefix_len(stmt):
    n = 0
    while isinstance(stmt, list) and stmt[0] in ("ALL", "IMP"):
        n, stmt = n + 1, stmt[2]
    return n


def _theorem(name, sig, script):
    body = "".join(f"  {ln}\n" for ln in script.strip().splitlines())
    return f"theorem «{name}»{sig} := by\n{body}"


BRIDGE_OPTS = ("-ind", "struct", "-updr", "off", "-nm", "0")


def bridge_facts(p, goal, xi, gi, slices=(8, 16, 32, 64), timeout=30):
    """Facts Vampire's own induction on variable xi used, or None."""
    ranked = [n for n, _ in p.search.rank(goal.index, limit=max(slices),
                                          goal_obj=goal)]
    for k in slices:
        try:
            text, ids = p.smt.problem(goal, ranked[:k], xi, gi, motive=True)
        except (Unsupported, KeyError, IndexError):
            return None
        st, used, _ = run_smt(text, timeout=timeout, extra=BRIDGE_OPTS)
        if st == "Theorem":
            return [ids[u] for u in used if u in ids]
    return None


def prove_lemma(p, case, depth, splits, log, hint=None):
    """Prove a lifted case. Returns (prelude, duper) on success, else None.
    `prelude` is Lean source defining «case.name» and every lemma it uses."""
    try:
        p.sigs[case.name] = " : " + T.tm_to_lean(case.stmt, build_ctx(_decls))
    except Exception as exc:
        log.append([case.name, "translate", str(exc)[:80]])
        return None
    t0 = time.time()
    extra = []
    if hint:
        gd = p.goal_defs(case)
        extra = [(f"{lbl}#bridge", s) for lbl, s in candidate_tactics(hint, gd, gd)]
    r = p.prove(case, extra_candidates=extra, induction=False, guard=_HOP_GUARD)
    if r["proved_by"]:
        log.append([case.name, r["proved_by"], round(time.time() - t0)])
        return (_theorem(case.name, p.sigs[case.name], r["script"]),
                r["proved_by"].startswith("duper"))
    log.append([case.name, None, r["vampire"], round(time.time() - t0)])
    if depth <= 0:
        return None
    sub = split_and_prove(p, case, depth - 1, splits, log, guard=_HOP_GUARD)
    return sub and (sub[0] + "\n" + _theorem(case.name, p.sigs[case.name], sub[1]),
                    sub[2])


def split_and_prove(p, goal, depth, splits, log, guard=None):
    """Try up to `splits` induction splits of `goal`; the first whose every
    case is proved is assembled and checked. Returns (prelude, script, duper)."""
    n = _prefix_len(goal.stmt)
    cands = list(p.inductor.splits(goal))[:splits + 2]
    hints = {}
    for s_no, (pname, xi, gi, _) in enumerate(cands):
        if pname == "nat_ind":
            hints[s_no] = bridge_facts(p, goal, xi, gi)
            log.append([goal.name, f"bridge x={xi}", hints[s_no]])
    # splits Vampire's own induction proved go first
    order = sorted(range(len(cands)), key=lambda i: hints.get(i) is None)
    for rank, s_no in enumerate(order):
        if rank >= splits and hints.get(s_no) is None:
            break
        pname, xi, gi, cases = cands[s_no]
        log.append([goal.name, f"split {pname} x={xi}"])
        lemmas = []
        for c in cases:
            got = prove_lemma(p, c, depth, splits, log, hint=hints.get(s_no))
            if got is None:
                break
            lemmas.append(got)
        if len(lemmas) != len(cases):
            continue
        prelude = "\n".join(l for l, _ in lemmas)
        duper = any(d for _, d in lemmas)
        script = lean_script(n, xi, gi, pname, [[f"exact «{c.name}»"] for c in cases])
        (_, ok, why), = p.attempt_batch(goal, [("hybrid", script)], timeout=600,
                                        single_timeout=600, heartbeats=1000000,
                                        duper=duper, guard=guard, prelude=prelude)
        log.append([goal.name, f"assemble {pname}", why[:200]])
        if ok:
            return prelude, script, duper
    return None


def _run(args):
    name, depth, splits = args
    p = _init()
    g = p.by_name[name]
    t0 = time.time()
    log = []
    try:
        res = split_and_prove(p, g, depth, splits, log)
    except Exception as exc:
        log.append([name, "error", f"{type(exc).__name__}: {exc}"[:200]])
        res = None
    out = {"goal": name, "proved_by": "hybrid-induction" if res else None,
           "secs": round(time.time() - t0, 1), "log": log}
    if res:
        out["prelude"], out["script"], out["duper"] = res
    return out


def main():
    src, workers, dest = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    rest = sys.argv[4:]
    depth = int(rest[rest.index("--depth") + 1]) if "--depth" in rest else 1
    splits = int(rest[rest.index("--splits") + 1]) if "--splits" in rest else 3
    if src.endswith(".jsonl"):
        names = [json.loads(l)["goal"] for l in open(src) if l.strip()]
    else:
        names = [l.strip() for l in open(src) if l.strip()]
    if "--resume" in rest and os.path.exists(dest):
        seen = {json.loads(l)["goal"] for l in open(dest)}
        names = [n for n in names if n not in seen]
    print(f"{len(names)} goals, depth {depth}, {splits} splits, {workers} workers",
          flush=True)
    _init()
    n = won = 0
    with ThreadPoolExecutor(max_workers=workers) as ex, \
            open(dest, "a" if "--resume" in rest else "w") as fh:
        for r in ex.map(_run, ((x, depth, splits) for x in names)):
            n += 1
            won += bool(r["proved_by"])
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            tag = "*** PROVED" if r["proved_by"] else (r["log"][-1][-1] if r["log"] else "")
            print(f"{n}/{len(names)} {r['goal'][:32]:<32} {r['secs']:>7}s  {str(tag)[:50]}",
                  flush=True)
    print(f"\nhybrid induction: {won}/{n}", flush=True)


if __name__ == "__main__":
    main()
