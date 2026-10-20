"""Try the LLM feedback loop on specific theorems the deterministic pipeline
failed. Every success reported here passed Lean's kernel, the statement
check, and the leak guard -- same bar as everything else."""
import sys

from library import load
from itp import load_statements
from prover import Prover
from llm import llm_rounds, DEFAULT_MODEL

names = sys.argv[1].split(",")
model = sys.argv[2] if len(sys.argv) > 2 else DEFAULT_MODEL
rounds = int(sys.argv[3]) if len(sys.argv) > 3 else 3

decls = load("../data/corpus.sexpr")
p = Prover(decls, "../data/corpus.sexpr", load_statements())
by = {d.name: d for d in decls}
won = 0
for name in names:
    g = by[name]
    premises, defs, vstat = p.hints(g)
    if not vstat.startswith("Theorem"):
        # no Vampire proof: give the model Search's broader top facts
        premises = [n for n, _ in p.search.rank(g.index, limit=24)
                    if by[n].kind in ("THM", "AXIOM")][:16]
    print(f"{name}  (vampire={vstat}, {len(premises)} facts, model={model})")
    label, tr = llm_rounds(p, g, premises, defs, rounds=rounds, model=model,
                           log=print)
    won += bool(label)
    print(f"  => {'PROVED by ' + label if label else 'failed'}")
    if label:
        print("  script:\n" + "\n".join("     " + l for l in tr[-1]["script"].splitlines()))
print(f"\nLLM proved {won}/{len(names)}")
