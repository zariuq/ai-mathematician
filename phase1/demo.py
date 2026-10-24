"""Live walkthrough of the Phase 1 pipeline on one theorem.

Prints each stage with its real output, so the whole chain
    statement -> Search -> Vampire -> Lean -> kernel guard
can be watched end to end rather than described.

Usage:
    python3 demo.py                      # default example: 1 + 1 = 2
    python3 demo.py <theorem_name>
    python3 demo.py --list               # a few good examples to try
    python3 demo.py <theorem> --full     # stage 3 runs ALL FOUR Lean lines
                                         # (grind, follow-ups, apply, Duper)
                                         # live -- can take ~20 min on a hard goal
    python3 demo.py <theorem> --record   # same full picture, replayed instantly
                                         # from the saved v4 run (no Lean, no
                                         # Vampire): what was tried, by stage
"""
import json
import os
import sys
import time

from library import load
from itp import load_statements
from prover import Prover, candidate_tactics

CORPUS = "../data/corpus.sexpr"
BAR = "=" * 78
RECORD = "../results/phase1_full_v4.jsonl"

# Prover.prove's four reconstruction lines, in the order it tries them
STAGES = {1: "battery    -- 8 grind / solve_by_elim templates",
          2: "follow-ups -- bigger grind budgets, simp_all, 2nd premise set",
          3: "apply      -- one backward step with each fact, then grind",
          4: "Duper      -- superposition prover inside Lean, own process each",
          5: "induction  -- only when Vampire found no proof"}
_BATTERY = {"intro-grind", "unfold-grind", "prem-grind", "prem-unfold-grind",
            "solve_by_elim", "goal-unfold-grind", "goal-unfold-sbe", "ext-grind"}


def stage_of(label):
    base, _, pset = label.partition("#")
    if base.startswith("duper"):
        return 4
    if base.startswith("apply"):
        return 3
    if base.startswith("induction"):
        return 5
    if base in _BATTERY and pset in ("", "1"):
        return 1
    return 2


def print_attempts(results, secs=None):
    """Every attempt Prover.prove made, grouped by the line it came from."""
    by = {}
    for lbl, ok, why in results:
        by.setdefault(stage_of(lbl), []).append((lbl, ok, why))
    for st in sorted(by):
        rows = by[st]
        won = sum(ok for _, ok, _ in rows)
        print(f"\n    line {st}: {STAGES[st]}")
        print(f"      {len(rows)} attempts, {won} succeeded")
        for lbl, ok, why in rows:
            first = " ".join(str(why).split())[:58]
            print(f"        {'OK ' if ok else '-- '}{lbl:<26}{'' if ok else first}")
    if secs is not None:
        print(f"\n    total time on this goal: {secs:.0f}s")

EXAMPLES = [
    ("add_nat_1_1_2", "1 + 1 = 2  -- the clean end-to-end case"),
    ("andEL",         "A and B implies A  -- pure logic, proved from definitions"),
    ("binunion_idl",  "empty union X = X  -- Vampire proves it, Lean cannot rebuild"),
    ("In_irref",      "no set contains itself  -- same failure mode"),
    ("nat_p_UnivOf_Empty", "needs INDUCTION -- the line that was starved of time"),
]


def main():
    if "--list" in sys.argv:
        print("Examples:\n")
        for n, d in EXAMPLES:
            print(f"  {n:<24}{d}")
        return
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    name = args[0] if args else "add_nat_1_1_2"
    full, record = "--full" in sys.argv, "--record" in sys.argv

    print(BAR)
    print(f"PHASE 1 PIPELINE DEMO  --  theorem: {name}")
    print(BAR)

    decls = load(CORPUS)
    p = Prover(decls, CORPUS, load_statements())
    if name not in p.by_name:
        import difflib
        near = difflib.get_close_matches(name, p.by_name, n=6, cutoff=0.4)
        print(f"\n  '{name}' is not in the corpus.")
        if near:
            print("  Did you mean:  " + ", ".join(near))
        print(f"\n  The corpus has {sum(1 for d in decls if d.kind=='THM')} theorems.")
        print("  Try:  python3 demo.py --list")
        print("  Or search: python3 -c \"from library import load;"
              " print([d.name for d in load('../data/corpus.sexpr')"
              " if 'YOURWORD' in d.name][:20])\"")
        return
    g = p.by_name[name]
    sig = p.sigs[name]

    # ---------------------------------------------------------- the input
    print("\n[0] THE INPUT -- the statement, and nothing else")
    print(f"    position in library : #{g.index} of {len(decls)}")
    print(f"    statement           : {sig.strip()[:150]}")
    print(f"    the human's proof   : {len(str(g.body))} characters -- NEVER SHOWN to the prover")

    pool = [d for d in decls[:g.index] if d.kind in ("THM", "AXIOM")]
    print(f"\n    facts it may use    : {len(pool)} (everything BEFORE #{g.index})")
    print(f"    facts it may not    : everything after -- this is the leak guard")

    # ---------------------------------------------------- stage 1: Search
    print("\n" + BAR)
    print("[1] SEARCH  (phase1/search.py)  -- which facts are worth trying?")
    print(BAR)
    t = time.time()
    ranked = [n for n, _ in p.search.rank(g.index, limit=512, goal_obj=g)]
    facts = [n for n in ranked if p.by_name[n].kind in ("THM", "AXIOM")]
    print(f"    ranked {len(facts)} facts in {time.time()-t:.2f}s")
    print("    signals: IDF symbol overlap + k-nearest-neighbour + naive Bayes\n")
    for i, n in enumerate(facts[:8], 1):
        print(f"      #{i}  {n}")

    # --------------------------------------------------- stage 2: Vampire
    print("\n" + BAR)
    print("[2] VAMPIRE  (phase1/atp.py)  -- an external prover; Lean checks its result")
    print(BAR)
    rec = None
    if record:
        rec = next((json.loads(l) for l in open(RECORD)
                    if json.loads(l)["goal"] == name), None) \
            if os.path.exists(RECORD) else None
        if rec is None:
            print(f"    no saved record for {name} in {RECORD}; run with --full instead")
            return
        sets, defs, vstatus = rec["premise_sets"], rec["defs"], rec["vampire"]
        print(f"    (replayed from the saved v4 run: {RECORD})")
    else:
        t = time.time()
        sets, defs, vstatus = p.premise_sets(g)
        print(f"    tried premise slices k = 16,32,64,128,256,512   ({time.time()-t:.0f}s)")
    print(f"    status: {vstatus}")
    if vstatus.startswith("Theorem"):
        print(f"\n    Vampire's proof used only these facts:")
        for n in sets[0]:
            print(f"      - {n}")
        print(f"\n    We keep ONLY this list. Vampire's proof itself is discarded.")
    else:
        print("    Vampire found nothing -- this goal falls through to induction.")

    # ------------------------------------------------------ stage 3: Lean
    print("\n" + BAR)
    print("[3] LEAN 4  (phase1/prover.py)  -- rebuild the proof, TRUSTED")
    print(BAR)
    if full or record:
        if record:
            res, secs, script = rec["results"], rec.get("secs"), None
            print("    the full record: every attempt Prover.prove made, by line")
        else:
            print("    running Prover.prove: all four lines, stopping at the first proof")
            print("    (this re-runs Vampire, and can take ~20 min when every line fails)")
            t = time.time()
            r = p.prove(g)
            res, secs, script = r["results"], time.time() - t, r.get("script")
        print_attempts(res, secs)
        win = next((lbl for lbl, ok, _ in res if ok), None)
        if win and script:
            print(f"\n    WINNER: {win}\n")
            for line in script.splitlines():
                print(f"        {line}")
        elif not win:
            print("\n    every line failed -- a reconstruction failure, with the record")
        cands = []
    else:
        cands = candidate_tactics(sets[0], defs, p.goal_defs(g))
        print(f"    built {len(cands)} candidate tactic scripts from those facts")
        print("    (line 1 of 4 only; --full runs all four, --record replays them)")
        t = time.time()
        res = p.attempt_batch(g, cands)
        win = next((lbl for lbl, ok, _ in res if ok), None)
        print(f"    checked all of them in {time.time()-t:.0f}s\n")
    if win and cands:
        script = dict(cands)[win]
        print(f"    WINNER: {win}\n")
        for line in script.splitlines():
            print(f"        {line}")
    elif not (full or record):
        print("    none succeeded on line 1 -- the real pipeline continues with")
        print("    follow-ups, apply and Duper: see --full / --record")
        for lbl, ok, why in res[:3]:
            print(f"      {lbl:<22}{str(why)[:60]}")

    # ------------------------------------------------------- stage 4: guard
    print("\n" + BAR)
    print("[4] THE GUARD  (phase1/itp.py)  -- what makes the result mean something")
    print(BAR)
    print("    1. statement identity : proved type must EQUAL the library's declaration")
    print("    2. no sorryAx         : no holes left in the proof")
    print("    3. leak check         : nothing cited at index >= this theorem's")
    print(f"\n    VERDICT: {'PROVED and kernel-checked' if win else 'not proved'}")
    print(BAR)


if __name__ == "__main__":
    main()
