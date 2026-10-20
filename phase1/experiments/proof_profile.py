"""How replayable are our Vampire proofs?

Before writing a proof-term emitter it is worth knowing what it would have to
support. This runs Vampire on goals it already solves, parses the refutation
(vampire_proof.py) and tallies the inference rules actually used, the number
of steps, and how many goals stay inside the rule set that published
replay work covers.

The ITP-2026 "Lean on Vampire Proofs" work reconstructs first-order proofs:
clausification, resolution, superposition, demodulation, AVATAR. Our corpus
is higher-order (THF), so the interesting question is how much of our proof
traffic uses HOL-only rules that no existing replay tool handles.

Usage: python3 proof_profile.py <run.jsonl> <workers> <limit> <out.json>
"""
import json
import sys
import threading
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover
from vampire_proof import run_with_proof

CORPUS = "../data/corpus.sexpr"

# What published first-order replay work covers (ITP-2026, Sect. 3).
FIRST_ORDER = {
    "file", "introduced", "negated_conjecture", "rectify", "flattening",
    "ennf_transformation", "nnf_transformation", "cnf_transformation",
    "skolemisation", "resolution", "subsumption_resolution",
    "forward_subsumption_resolution", "backward_subsumption_resolution",
    "superposition", "forward_demodulation", "backward_demodulation",
    "demodulation", "equality_resolution", "equality_factoring", "factoring",
    "trivial_inequality_removal", "duplicate_literal_removal",
    "avatar_definition", "avatar_component_clause", "avatar_split_clause",
    "avatar_contradiction_clause", "avatar_sat_refutation", "sat_conversion",
    "rat", "definition_unfolding", "definition_folding", "evaluation",
    "unused_predicate_definition_removal", "pure_predicate_removal",
}

_prover = None
_lock = threading.Lock()


def _init():
    global _prover
    with _lock:
        if _prover is None:
            _prover = Prover(load(CORPUS), CORPUS, load_statements())
    return _prover


def _slice_of(vstatus):
    """The smallest premise slice Vampire solved this goal at -- cheapest to
    reproduce, and the proof it yields is the one the prover already used."""
    try:
        return int(str(vstatus).split("@")[1].split(",")[0])
    except Exception:
        return 64


def _run(row):
    p = _init()
    g = p.by_name[row["goal"]]
    k = _slice_of(row.get("vampire"))
    ranked = [n for n, _ in p.search.rank(g.index, limit=max(k, 16), goal_obj=g)]
    try:
        text, ids, _ = p.thf.problem(g, ranked[:k])
    except Exception as e:
        return {"goal": g.name, "status": f"unsupported: {type(e).__name__}"}
    st, steps, _ = run_with_proof(text, timeout=30)
    rules = Counter(s.rule for s in steps)
    return {"goal": g.name, "status": st, "steps": len(steps),
            "rules": dict(rules),
            "hol_only": sorted(r for r in rules if r not in FIRST_ORDER)}


def main():
    src, workers, limit, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    rows = [json.loads(l) for l in open(src)]
    rows = [r for r in rows if str(r.get("vampire", "")).startswith("Theorem")][:limit]
    print(f"{len(rows)} goals Vampire already solves, {workers} workers", flush=True)
    _init()
    res = []
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for i, r in enumerate(ex.map(_run, rows), 1):
            res.append(r)
            print(f"{i}/{len(rows)} {r['goal'][:34]:<34} {r['status']:<10} "
                  f"steps={r.get('steps','-')} hol={','.join(r.get('hol_only',[])) or '-'}",
                  flush=True)
    json.dump(res, open(out, "w"), indent=1)

    ok = [r for r in res if r["status"] == "Theorem"]
    allrules = Counter()
    for r in ok:
        allrules.update(r["rules"])
    print(f"\n=== {len(ok)} refutations parsed ===")
    steps = sorted(r["steps"] for r in ok)
    if steps:
        print(f"steps per proof: median {steps[len(steps)//2]}, max {steps[-1]}")
    clean = sum(1 for r in ok if not r["hol_only"])
    print(f"proofs using ONLY first-order-replayable rules: {clean}/{len(ok)}")
    print("\nrule frequency (* = no published Lean replay support):")
    for rule, n in allrules.most_common(30):
        mark = " " if rule in FIRST_ORDER else "*"
        print(f" {mark} {rule:<36}{n}")


if __name__ == "__main__":
    main()
