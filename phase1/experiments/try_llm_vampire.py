"""LLM feedback loop with Vampire's PROOF in the prompt, not just the names
of the facts it used. The model is asked to translate the refutation into
a direct Lean proof; Lean checks it exactly as every other candidate
(kernel + statement check + leak guard).

  python3 try_llm_vampire.py add_nat_1_1_2[,name2,...] [model] [rounds]
      --no-proof     same facts and defs, but without the proof (A/B baseline)
      --show-prompt  print the first prompt sent to the model
"""
import json
import sys

from library import load
from itp import load_statements
from prover import Prover
from llm import llm_rounds, build_prompt, goal_state, LeanContext, DEFAULT_MODEL
from vampire_proof import proof_for_llm

args = [a for a in sys.argv[1:] if not a.startswith("--")]
names = args[0].split(",")
model = args[1] if len(args) > 1 else DEFAULT_MODEL
rounds = int(args[2]) if len(args) > 2 else 3
with_proof = "--no-proof" not in sys.argv

decls = load("../data/corpus.sexpr")
p = Prover(decls, "../data/corpus.sexpr", load_statements())
by = {d.name: d for d in decls}
won = 0
OUT = "../results/llm_vampire_proof.jsonl"
for name in names:
    g = by[name]
    got = proof_for_llm(p, g)
    if got is None:
        print(f"{name}: Vampire found no proof -- skipped")
        continue
    proof, facts, vdefs, k = got
    defs = sorted(set(vdefs) | set(p.goal_defs(g)))
    print(f"{name}  (Vampire proof at k={k}: {len(facts)} facts, defs={defs}, "
          f"{len(proof)} chars; proof in prompt={with_proof}; model={model})")
    if "--show-prompt" in sys.argv:
        ctx = LeanContext()
        p._lean_ctx = ctx
        print("-" * 70)
        print(build_prompt(ctx, g.name, p.sigs[g.name], defs, facts,
                           goal_state(p, g), proof if with_proof else None))
        print("-" * 70)
    label, tr = llm_rounds(p, g, facts, defs, rounds=rounds, model=model,
                           log=print, atp_proof=proof if with_proof else None)
    won += bool(label)
    with open(OUT, "a") as fh:
        fh.write(json.dumps({"goal": name, "with_proof": with_proof, "model": model,
                             "k": k, "proved": label, "transcript": tr}) + "\n")
    print(f"  => {'PROVED by ' + label if label else 'failed'}")
    if label:
        print("  script:\n" + "\n".join("     " + l for l in tr[-1]["script"].splitlines()))
print(f"\nLLM proved {won}/{len(names)}")
