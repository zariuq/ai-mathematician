"""Higher-order walkthrough: why `grind` is not enough and Duper is.

A HIGHER-ORDER statement quantifies over a predicate or a function, not just
over sets -- `forall P : set -> Prop, ...`. Megalodon's logic is higher-order
throughout (that is how it defines induction), and this is exactly where
Lean's general-purpose automation runs out: `grind` does not do higher-order
unification. Duper -- a superposition prover running inside Lean -- does.

This runs the same four stages as demo.py but shows the reconstruction lines
one at a time, so the hand-off from `grind` to Duper is visible.

Usage: python3 demo_ho.py [theorem]      default: int_SNo_cases
"""
import re
import sys
import time

from library import load
from itp import load_statements
from prover import Prover, candidate_tactics, duper_tactics

CORPUS = "../data/corpus.sexpr"
BAR = "=" * 78
HO_BINDER = re.compile(r"forall (\w+) : \(((?:set|Prop)[^)]*->[^)]*)\)")

EXAMPLES = [
    ("int_SNo_cases", "quantifies over a PREDICATE  (set -> Prop)"),
    ("If_ii_1",       "quantifies over FUNCTIONS    (set -> set)"),
    ("If_iii_1",      "quantifies over 2-arg functions"),
]


def main():
    if "--list" in sys.argv:
        for n, d in EXAMPLES:
            print(f"  {n:<18}{d}")
        return
    name = sys.argv[1] if len(sys.argv) > 1 else "int_SNo_cases"

    decls = load(CORPUS)
    p = Prover(decls, CORPUS, load_statements())
    g = p.by_name[name]
    sig = p.sigs[name].strip()

    print(BAR)
    print(f"HIGHER-ORDER DEMO  --  {name}")
    print(BAR)

    print("\n[0] WHY THIS IS HIGHER-ORDER")
    for var, ty in HO_BINDER.findall(sig):
        print(f"    forall {var} : ({ty})")
        print(f"      ^^ the quantifier ranges over {'PREDICATES' if 'Prop' in ty else 'FUNCTIONS'},")
        print(f"         not over sets. First-order logic cannot say this.")
    print(f"\n    full statement:\n      {sig[:300]}")

    print("\n" + BAR)
    print("[1+2] SEARCH -> VAMPIRE")
    print(BAR)
    t = time.time()
    sets, defs, vstatus = p.premise_sets(g)
    print(f"    Vampire: {vstatus}   ({time.time()-t:.0f}s)")
    print(f"    facts its proof used ({len(sets[0])}): {sets[0]}")

    print("\n" + BAR)
    print("[3] LEAN, LINE BY LINE  -- watch where grind stops")
    print(BAR)

    print("\n  LINE 1-3: the `grind` battery (no higher-order unification)")
    cands = candidate_tactics(sets[0], defs, p.goal_defs(g))
    t = time.time()
    res = p.attempt_batch(g, cands)
    win = next((lbl for lbl, ok, _ in res if ok), None)
    print(f"    tried {len(cands)} scripts in {time.time()-t:.0f}s -> "
          f"{'PROVED by ' + win if win else 'ALL FAILED'}")
    if not win:
        for lbl, ok, why in res[:3]:
            print(f"      {lbl:<20} {str(why)[:62]}")

    if win:
        print("\n    (this one did not need Duper; try --list for others)")
        return

    print("\n  LINE 4: Duper -- superposition INSIDE Lean, higher-order capable")
    for lbl, script in duper_tactics(sets[0], defs):
        t = time.time()
        r = p.attempt_batch(g, [(lbl, script)], timeout=330, single_timeout=300,
                            max_retry_secs=0, heartbeats=1000000, duper=True)
        lab, ok, why = r[0]
        print(f"    {lab:<16} {'*** PROVED' if ok else str(why)[:52]}  ({time.time()-t:.0f}s)")
        if ok:
            print("\n    the winning script:")
            for line in script.splitlines():
                print(f"        {line}")
            win = lab
            break

    print("\n" + BAR)
    print("[4] GUARD: statement identity + no sorryAx + no leak")
    print(f"    VERDICT: {'PROVED and kernel-checked' if win else 'not proved'}")
    print(BAR)


if __name__ == "__main__":
    main()
