"""Collect every proof the AI mathematician found into one replayable file.

results/proof_bundle.jsonl has one row per proved theorem with the exact
proof script (plus any helper lemmas it needs, and whether it needs Duper)
and where it came from. From then on the record is the script itself, not a
recipe for rebuilding it. replay.py checks every row from scratch.

Sources, in order of preference for each theorem:
  * the 212 LLM proofs: their stored scripts;
  * the 640 pipeline proofs of the v4 run: the deterministic battery
    rebuilds the winning script from the stored strategy label, premise set
    and definitions (as recheck_full.py does);
  * the 25 results from earlier experiments: a stored script, else the
    stored recipe, else proved again now by the current pipeline (no LLM).
Theorems that cannot be recovered are listed, not dropped silently.

  python3 build_bundle.py [workers]
"""
import glob
import json
import sys
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import (Prover, apply_tactics, candidate_tactics, duper_tactics,
                    followup_tactics)

CORPUS = "../data/corpus.sexpr"
OUT = "../results/proof_bundle.jsonl"
decls = load(CORPUS)
by = {d.name: d for d in decls}
prover = Prover(decls, CORPUS, load_statements())


def battery_script(goal, label, premise_sets, defs):
    """The script the deterministic battery builds for a strategy label."""
    base, _, j = label.partition("#")
    premises = premise_sets[int(j) - 1] if j else premise_sets[0]
    gd = prover.goal_defs(by[goal])
    table = dict(candidate_tactics(premises, defs, gd))
    table.update(followup_tactics(premises, defs, gd))
    table.update(apply_tactics(premises, defs))
    table.update(duper_tactics(premises, defs))
    return table.get(base)


def row(goal, origin, script, prelude="", duper=False):
    return {"goal": goal, "origin": origin, "script": script,
            "prelude": prelude or "", "duper": bool(duper)}


def from_run_row(r, origin):
    """A bundle row from a pipeline result row, or None."""
    label = str(r.get("proved_by") or "")
    if not label:
        return None
    if r.get("script"):  # induction and hybrid proofs store theirs
        return row(r["goal"], origin, r["script"], r.get("prelude", ""),
                   r.get("duper") or label.startswith("duper"))
    if r.get("premise_sets"):
        s = battery_script(r["goal"], label, r["premise_sets"], r.get("defs", []))
        if s:
            return row(r["goal"], origin, s, duper=label.startswith("duper"))
    return None


bundle = {}

# 1. the LLM proofs
for f, origin in [("llm_proofs_verified.json", "llm v5"), ("v6v7_verified.json", "llm v6-v7"),
                  ("v8v9_verified.json", "llm v8-v9")]:
    for goal, r in json.load(open(f"../results/{f}"))["verified"].items():
        bundle[goal] = row(goal, origin, r["script"], r.get("prelude", ""))

# 2. the v4 pipeline proofs
for r in map(json.loads, open("../results/phase1_full_v4.jsonl")):
    if r.get("proved_by") and r["goal"] not in bundle:
        b = from_run_row(r, "pipeline v4")
        if b:
            bundle[r["goal"]] = b

# 3. the earlier experiments: stored script or recipe anywhere in results/
earlier = json.load(open("../results/phase1_final_summary.json"))["earlier_experiments"]
missing = [g for g in earlier if g not in bundle]
for f in sorted(glob.glob("../results/*.jsonl")):
    if "ledger" in f or f.endswith("proof_bundle.jsonl"):
        continue
    for line in open(f):
        try:
            r = json.loads(line)
        except ValueError:
            continue
        g = r.get("goal")
        if g in missing and g not in bundle:
            won = r.get("proved_by") or r.get("proved") is True
            if not won:
                continue
            if r.get("script"):
                bundle[g] = row(g, "earlier: " + f.split("/")[-1], r["script"],
                                r.get("prelude", ""), r.get("duper"))
            else:
                b = from_run_row(r, "earlier: " + f.split("/")[-1])
                if b:
                    bundle[g] = b

# ...else prove it again now with the current pipeline (deterministic, no LLM)
again = [g for g in earlier if g not in bundle]
print(f"{len(again)} earlier results have no stored script or recipe; proving again: {again}",
      flush=True)


def reprove(g):
    r = prover.prove(by[g])
    r["goal"] = g
    return g, from_run_row(r, "earlier, proved again now")


workers = int(sys.argv[1]) if len(sys.argv) > 1 else 4
with ThreadPoolExecutor(workers) as ex:
    for g, b in ex.map(reprove, again):
        print(f"  {g}: {'recovered' if b else 'NOT recovered'}", flush=True)
        if b:
            bundle[g] = b

with open(OUT, "w") as fh:
    for d in decls:  # library order
        if d.name in bundle:
            fh.write(json.dumps(bundle[d.name]) + "\n")
lost = [g for g in earlier if g not in bundle]
print(f"\n{len(bundle)} proofs -> {OUT}")
print(f"earlier results not recovered: {len(lost)} {lost}")
