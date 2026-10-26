"""Recover the earlier-experiment proofs whose scripts were not stored.

build_bundle.py lists them. Each came from a special experiment, so each is
proved again with that experiment's own settings, keeping the script this
time; a recovered proof is checked with the full guard before it is added to
results/proof_bundle.jsonl.

  * v1 run (phase1_full_v1.jsonl): the stored strategy and premises, built
    with today's battery;
  * try_induction_hard.py: induction with 30 s of Vampire per case and
    Lean trying cases Vampire could not do (--lean-anyway);
  * try_duper_hard.py: Duper with a long time allowance.

  python3 recover_earlier.py [workers]
"""
import json
import sys
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import (Prover, apply_tactics, candidate_tactics, duper_tactics,
                    followup_tactics)

CORPUS = "../data/corpus.sexpr"
BUNDLE = "../results/proof_bundle.jsonl"
decls = load(CORPUS)
by = {d.name: d for d in decls}
p = Prover(decls, CORPUS, load_statements())



def battery_script(goal, label, premise_sets, defs):
    """The script the deterministic battery builds for a strategy label
    (as in build_bundle.py)."""
    base, _, j = label.partition("#")
    premises = premise_sets[int(j) - 1] if j else premise_sets[0]
    gd = p.goal_defs(by[goal])
    table = dict(candidate_tactics(premises, defs, gd))
    table.update(followup_tactics(premises, defs, gd))
    table.update(apply_tactics(premises, defs))
    table.update(duper_tactics(premises, defs))
    return table.get(base)


earlier = json.load(open("../results/phase1_final_summary.json"))["earlier_experiments"]
bundle = {r["goal"]: r for r in map(json.loads, open(BUNDLE))}
todo = [g for g in earlier if g not in bundle]
v1 = {r["goal"]: r for r in map(json.loads, open("../results/phase1_full_v1.jsonl"))
      if r["goal"] in todo and r.get("proved_by")}
hard_ind = {r["goal"]: r for r in map(json.loads, open("../results/induction_hard.jsonl"))
            if r["goal"] in todo and r.get("proved_by")}
hard_duper = {r["goal"] for r in map(json.loads, open("../results/duper_hard.jsonl"))
              if r["goal"] in todo and r.get("proved_by")}


def verified(goal, script, prelude="", duper=False):
    (_, ok, why), = p.attempt_batch(by[goal], [("recover", script)], prelude=prelude,
                                    duper=duper, timeout=2400 if duper else 600,
                                    single_timeout=2400 if duper else 600,
                                    heartbeats=4000000 if duper else 400000)
    return ok, why


def recover(goal):
    g = by[goal]
    if goal in v1:
        r = v1[goal]
        s = battery_script(goal, r["proved_by"], [r["premises"]], r["defs"])
        if s:
            ok, why = verified(goal, s)
            if ok:
                return goal, {"goal": goal, "origin": "earlier v1, rebuilt now",
                              "script": s, "prelude": "", "duper": False}, "ok"
            return goal, None, why[:120]
        return goal, None, "strategy no longer in the battery"
    if goal in hard_ind:
        ranked = [n for n, _ in p.search.rank(g.index, limit=256, goal_obj=g)]
        for pname, xi, gi, cases in p.inductor.splits(g):
            if pname != hard_ind[goal]["split"]:
                continue
            used = []
            for c in cases:
                u = p._vampire_case(c, ranked, (16, 32, 64, 128, 256), timeout=30)
                used.append(u if u is not None else
                            [n for n in ranked if by[n].kind in ("THM", "AXIOM")][:8])
            ok, why, script = p.induction_lean(g, {"principle": pname, "x": xi, "guard": gi,
                                                   "case_premises": used})
            if ok:
                ok2, why2 = verified(goal, script)
                if ok2:
                    return goal, {"goal": goal, "origin": "earlier induction_hard, proved again now",
                                  "script": script, "prelude": "", "duper": False}, "ok"
                return goal, None, "recheck: " + why2[:100]
        return goal, None, "induction split not closed now"
    if goal in hard_duper:
        sets, defs, _ = p.premise_sets(g)
        for k, premises in enumerate(sets, 1):
            s = dict(duper_tactics(premises, defs)).get("duper-unfold")
            if s:
                ok, why = verified(goal, s, duper=True)
                if ok:
                    return goal, {"goal": goal, "origin": f"earlier duper_hard, proved again now (set {k})",
                                  "script": s, "prelude": "", "duper": True}, "ok"
        return goal, None, "Duper did not close it now"
    return goal, None, "no stored record of how it was proved"


print(f"{len(todo)} to recover: {todo}", flush=True)
with ThreadPoolExecutor(int(sys.argv[1]) if len(sys.argv) > 1 else 4) as ex:
    for goal, row, why in ex.map(recover, todo):
        print(f"  {goal}: {'RECOVERED' if row else 'not recovered: ' + why}", flush=True)
        if row:
            bundle[goal] = row
with open(BUNDLE, "w") as fh:
    for d in decls:
        if d.name in bundle:
            fh.write(json.dumps(bundle[d.name]) + "\n")
lost = [g for g in earlier if g not in bundle]
print(f"\n{len(bundle)} proofs in the bundle; earlier results still not recovered: {len(lost)} {lost}")
