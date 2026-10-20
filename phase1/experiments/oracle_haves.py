"""Oracle experiment: can the prover close a goal if it is given the
stepping stones instead of being asked to leap?

v4 solves 640/999. The 359 it fails are not uniformly harder -- they are
*structured*: 64% of them have at least one `have` step in the original
Megalodon proof, against 5% of the goals it proves. The whole theorem cites
a median of 12 facts; one hop of its proof cites a median of 1. So the
failures look hard in aggregate and easy step by step.

This script tests that directly. For each failed goal it lifts the
intermediate propositions out of Megalodon's own proof term, turns each into
a self-contained Lean goal, and asks the existing prover to close it.

The stepping stones come from the answer key, so nothing here counts as the
system proving a theorem. The question is narrower and worth money:
*if* the system knew the right intermediate lemmas, could it finish? A yes
makes "have an LLM propose the lemmas" worth the API budget; a no says the
bottleneck is somewhere else and saves it.

A `have` in Megalodon's proof language is a beta-redex

    (PPFAP (PLAM p rest) justification)

read as "assume p, justified by <justification>, then carry on". Such a p
lives under the enclosing binders, so it is closed over them before being
translated: enclosing TLAMs become ALL, enclosing PLAMs become IMP
antecedents. That is the standard lift of an inline step to a standalone
lemma, and it is what makes the hop a goal the prover can be handed.

Usage: python3 oracle_haves.py <run.jsonl> <workers> <out.jsonl> [limit] [--resume]
"""
import json
import sys
import threading
import os
from concurrent.futures import ThreadPoolExecutor

from library import load, _collect, _features
from itp import load_statements
from prover import Prover, candidate_tactics
from itp import _GUARD

# A hop is not a library declaration, so there is nothing to compare its type
# against: its statement comes from Megalodon's own proof term and Lean
# elaborates and proves exactly that. Drop only the `orig` lookup; the
# sorryAx audit and the leak check below it are kept verbatim.
_HOP_GUARD = _GUARD.replace(
    "  let some orig := env.find? `Megalodon.{orig} | IO.println \"GUARD noorig\"\n"
    "  IO.println s!\"GUARD samestmt {att.type == orig.type}\"",
    "  IO.println \"GUARD samestmt true\"")
import sexpr_translate as T

CORPUS = "../data/corpus.sexpr"


def build_ctx(decls):
    ctx = T.Ctx()
    for d in decls:
        if d.hash:
            ctx.hash_to_name[d.hash] = d.name
        if d.kind == "PRIM":
            ctx.prim_to_name[d.index] = d.name
    return ctx


def collect_haves(node, binders, out):
    """Walk a proof term, tracking the binders in scope, and lift out every
    `have` step as a proposition closed over its context.

    `binders` is the enclosing context, outermost first: ('tm', tp) for a
    TLAM (a bound term variable) and ('pf', prop) for a PLAM (an assumed
    hypothesis). Closing over it rebuilds the proposition as a standalone
    statement."""
    if not isinstance(node, list) or not node:
        return
    tag = node[0]

    if tag == "PPFAP" and isinstance(node[1], list) and node[1][0] == "PLAM":
        prop = node[1][1]
        closed = prop
        # innermost binder first, so wrap in reverse
        for kind, payload in reversed(binders):
            closed = ["ALL", payload, closed] if kind == "tm" else ["IMP", payload, closed]
        out.append(closed)
        # the justification sits in the same context
        collect_haves(node[2], binders, out)
        # the continuation gains the assumption
        collect_haves(node[1][2], binders + [("pf", prop)], out)
        return

    if tag == "TLAM":
        collect_haves(node[2], binders + [("tm", node[1])], out); return
    if tag == "PLAM":
        collect_haves(node[2], binders + [("pf", node[1])], out); return
    for child in node[1:]:
        collect_haves(child, binders, out)


_prover = None
_decls = None
_h2n = None
_p2n = None


_init_lock = threading.Lock()


def _init():
    global _prover, _decls, _h2n, _p2n
    with _init_lock:
        if _prover is not None:
            return
        _init_locked()


def _init_locked():
    global _prover, _decls, _h2n, _p2n
    _decls = load(CORPUS)
    _prover = Prover(_decls, CORPUS, load_statements())
    _h2n = {d.hash: d.name for d in _decls if d.hash}
    _p2n = {d.index: d.name for d in _decls if d.kind == "PRIM"}


class Hop:
    """A stepping stone, dressed up as something Prover.prove can take.

    Search reads `stmt_syms` (the constants the statement mentions) and
    `feats` (its structural features) off the goal, so both are derived
    from the lifted proposition exactly as library.load derives them for a
    real declaration -- otherwise the hop gets ranked against nothing."""
    __slots__ = ("name", "index", "stmt", "kind", "stmt_syms", "feats",
                 "proof_deps", "body", "hash")

    def __init__(self, name, index, stmt, h2n, p2n):
        self.name, self.index, self.stmt, self.kind = name, index, stmt, "THM"
        self.body, self.hash, self.proof_deps = None, "", set()
        syms = set()
        _collect(stmt, h2n, p2n, syms)
        self.stmt_syms = syms
        self.feats = _features(stmt, h2n)


def _prove_hop(hop):
    """Prover.prove, but with the hop guard."""
    sets, defs, vstatus = _prover.premise_sets(hop)
    cands = candidate_tactics(sets[0], defs, _prover.goal_defs(hop))
    for j, alt in enumerate(sets[1:], start=2):
        cands += [(f"{lbl}#{j}", s) for lbl, s in
                  candidate_tactics(alt, defs, _prover.goal_defs(hop))
                  if lbl.startswith(("prem-", "solve_by_elim", "goal-unfold"))]
    for lbl, ok, why in _prover.attempt_batch(hop, cands, guard=_HOP_GUARD):
        if ok:
            return {"proved_by": lbl}
    return {"proved_by": None}


def _run(task):
    goal_name, goal_index, hops = task
    out = {"goal": goal_name, "hops": len(hops), "closed": 0, "detail": []}
    for i, prop in enumerate(hops):
        hname = f"{goal_name}__hop{i}"
        try:
            ctx = build_ctx(_decls)
            lean = T.tm_to_lean(prop, ctx)
        except Exception as exc:
            out["detail"].append([hname, False, f"translate: {exc}"]); continue
        # the hop is attempted in the parent's position, so Search keeps its
        # leak discipline: only declarations before the parent goal are visible
        hop = Hop(hname, goal_index, prop, _h2n, _p2n)
        _prover.sigs[hname] = f" : {lean}"
        try:
            res = _prove_hop(hop)
            ok = bool(res.get("proved_by"))
        except Exception as exc:
            ok, res = False, {"proved_by": None, "err": str(exc)[:120]}
        out["detail"].append([hname, ok, res.get("proved_by") or res.get("err")])
        if ok:
            out["closed"] += 1
    out["all_closed"] = out["hops"] > 0 and out["closed"] == out["hops"]
    return out


def main():
    run, workers, dest = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    resume = "--resume" in sys.argv
    rest = [a for a in sys.argv[4:] if not a.startswith("--")]
    limit = int(rest[0]) if rest else None

    decls = load(CORPUS)
    by = {d.name: d for d in decls}
    rows = [json.loads(l) for l in open(run) if l.strip()]
    failed = [r["goal"] for r in rows if not r.get("proved_by")]

    tasks = []
    for g in failed:
        d = by.get(g)
        if not d or d.kind != "THM" or d.body is None:
            continue
        hops = []
        collect_haves(d.body, [], hops)
        if hops:
            tasks.append((g, d.index, hops))
    if limit:
        tasks = tasks[:limit]

    # Resume: keep whatever finished, attempt only the rest. A goal is either
    # fully recorded or absent, so there is no partial state to repair.
    done_goals = set()
    if resume and os.path.exists(dest):
        kept = []
        for line in open(dest):
            try:
                kept.append(json.loads(line))
            except json.JSONDecodeError:
                pass          # a line cut off mid-write: redo that goal
        with open(dest, "w") as fh:
            fh.writelines(json.dumps(r) + "\n" for r in kept)
        done_goals = {r["goal"] for r in kept}
        tasks = [t for t in tasks if t[0] not in done_goals]
        print(f"resuming: {len(done_goals)} goals already done", flush=True)

    print(f"{len(failed)} failed goals; {len(tasks) + len(done_goals)} have "
          f"stepping stones; {len(tasks)} still to try "
          f"({sum(len(t[2]) for t in tasks)} hops)", flush=True)

    done = goals_closed = hops_closed = hops_total = 0
    with ThreadPoolExecutor(max_workers=workers, initializer=_init) as ex, \
            open(dest, "a" if resume else "w") as fh:
        for r in ex.map(_run, tasks):
            fh.write(json.dumps(r) + "\n"); fh.flush()
            done += 1
            hops_total += r["hops"]; hops_closed += r["closed"]
            goals_closed += bool(r["all_closed"])
            print(f"{done}/{len(tasks)} {r['goal'][:34]:34s} "
                  f"hops {r['closed']}/{r['hops']}"
                  f"{'  ALL CLOSED' if r['all_closed'] else ''}", flush=True)
    print(f"\nhops closed      : {hops_closed}/{hops_total}")
    print(f"goals fully closed: {goals_closed}/{len(tasks)}")


if __name__ == "__main__":
    main()
