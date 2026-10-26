"""Build the Phase 1 report (.docx). Numbers are read from the result files
where possible, so the document cannot drift from the data.

Usage: python3 make_report.py <out.docx> [categories.json]
  categories.json: theorem -> category, from the translator's per-category
  output files (see megalodon-lean4 sexprinfo-prototype).
"""
import json
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "phase1"))
from docx_writer import Doc  # noqa: E402

R = os.path.join(os.path.dirname(__file__), "..", "results")
out_path = sys.argv[1]
cat_path = sys.argv[2] if len(sys.argv) > 2 else os.path.join(os.path.dirname(__file__), "categories.json")


def rows(name):
    return [json.loads(l) for l in open(os.path.join(R, name))]


v1 = {r["goal"]: r for r in rows("phase1_full_v1.jsonl")}
v2 = {r["goal"]: r for r in rows("phase1_full_v2.jsonl")}
v3 = {r["goal"]: r for r in rows("phase1_full_v3.jsonl")}
v4 = {r["goal"]: r for r in rows("phase1_full_v4.jsonl")}
P1 = {g for g, r in v1.items() if r["proved_by"]}
P2 = {g for g, r in v2.items() if r["proved_by"]}
P3 = {g for g, r in v3.items() if r["proved_by"]}
P4 = {g for g, r in v4.items() if r["proved_by"]}


def verified(name):
    """Goals whose LLM proof passed the from-scratch re-check, mapped to the
    result file each proof came from."""
    return {g: v["source"] for g, v in
            json.load(open(os.path.join(R, name)))["verified"].items()}


summary = json.load(open(os.path.join(R, "phase1_final_summary.json")))
EARLIER = set(summary["earlier_experiments"])   # induction etc., no LLM
NOLLM = P4 | EARLIER
L5 = set(verified("llm_proofs_verified.json"))
L67 = verified("v6v7_verified.json")
L89 = verified("v8v9_verified.json")
L7 = {g for g, src in L67.items() if os.path.basename(src).startswith("v7")}
L6 = set(L67) - L7
L8 = {g for g, src in L89.items() if os.path.basename(src).startswith("v8")}
L9 = set(L89) - L8
LLM_ALL = L5 | set(L67) | set(L89)
FINAL = NOLLM | LLM_ALL
recheck4 = rows("recheck_v4.jsonl")
rc4_ok = sum(bool(x.get("ok")) for x in recheck4)
llm = {r["goal"] for f in ("llm140_gptoss.jsonl", "llm140_deepseek.jsonl")
       for r in rows(f) if r["proved_by"]}
cat = json.load(open(cat_path))
CATS = [("prop_logic", "Propositional logic"), ("set_theory", "Set theory"),
        ("nat_arith", "Natural numbers"), ("ordinals", "Ordinals"),
        ("surreals", "Surreal numbers")]
recheck = rows("recheck_v3.jsonl") if os.path.exists(os.path.join(R, "recheck_v3.jsonl")) else []
rc_ok = sum(r["ok"] for r in recheck)
dsp = rows("llm_dsp.jsonl") if os.path.exists(os.path.join(R, "llm_dsp.jsonl")) else []


def pct(a, b):
    return f"{a / b:.1%}"


first = Counter()
for r in v4.values():
    if r["proved_by"]:
        lbl = r["proved_by"]
        first["induction" if lbl.startswith("induction") else lbl.split("#")[0]] += 1
ind = Counter(r["proved_by"].split(":")[1] for r in v4.values()
              if r["proved_by"] and r["proved_by"].startswith("induction"))
unproved = [r for r in v4.values() if not r["proved_by"]]
secs_p = sorted(r["secs"] for r in v4.values() if r["proved_by"])
secs_f = sorted(r["secs"] for r in unproved)
unproved_vamp = sum(r["vampire"].startswith("Theorem") for r in unproved)

d = Doc("AI Mathematician: Phase 1 Report", "yenat")
d.heading("AI Mathematician — Phase 1 Report", 0)
d.para("Search · ATP (Vampire) · ITP (Lean 4) · LLM proposer, evaluated on the "
       "999-theorem Megalodon reference library. October 2026.")

# ------------------------------------------------------------------ summary
d.heading("1. Summary", 1)
d.bullets([
    f"**{len(FINAL)} / 999 theorems ({pct(len(FINAL), 999)}) proved**, each "
    "held out and proved only from facts that precede it in the library.",
    f"**{len(NOLLM)}** without any LLM ({len(P4)} in the v4 pipeline run, "
    f"{len(EARLIER)} more from induction and earlier runs), and **{len(LLM_ALL)}** "
    "by the LLM loop, all on theorems the pipeline had attempted and failed.",
    "Every proof is checked by Lean 4's kernel, with the proof's statement "
    "compared to the original as elaborated terms and a leak guard rejecting any "
    "use of the target or later facts. "
    f"All {len(recheck4)} v4 proofs were re-verified in fresh Lean processes "
    f"({rc4_ok} / {len(recheck4)}), and every LLM proof was re-verified from "
    f"scratch ({len(LLM_ALL)} / {len(LLM_ALL)}).",
    "Vampire and the LLM only propose proofs; every proof is verified by Lean.",
    "The decisive finding for the LLM: its failures were mostly about missing "
    "lemmas, not reasoning. Showing it 96 to 160 facts instead of 24 added "
    "about 100 proofs (Section 6.3).",
    f"Progression: {len(P1)} → {len(P2)} → {len(P3)} → {len(P4)} without an LLM "
    f"(v1–v4), then {len(NOLLM | L5)} → {len(NOLLM | L5 | L6)} → "
    f"{len(NOLLM | L5 | L6 | L7)} → {len(NOLLM | L5 | L6 | L7 | L8)} → "
    f"{len(FINAL)} with the LLM loop (v5–v9).",
])

# ------------------------------------------------------------------ scope
d.heading("2. Phase 1 scope and status", 1)
d.para("Phase 1 of the design sketch: an LLM proves a lemma and formalizes the "
       "proof, guiding an ITP that checks it with the help of an ATP, fed by "
       "Search + Download. Mapping to what is built:")
d.table([
    ["Sketch component", "Implementation", "Status"],
    ["Search + Download", "Premise selection over the Megalodon library "
     "(symbol overlap, naive Bayes learned from earlier proofs, k-NN, recency)",
     "Done; Download = retrieval from the library (external sources: later)"],
    ["ATP", "Vampire 5.1.0, higher-order TPTP (THF)", "Done"],
    ["ITP", "Lean 4.34.0 over the verified Megalodon→Lean 4 translation "
     "(999/999 theorems)", "Done"],
    ["LLM guiding the ITP", "LLM writes Lean tactic scripts; Lean's errors fed "
     "back for up to 7 rounds", f"Done: {len(LLM_ALL)} theorems (Section 6)"],
    ["LLM proving lemma → formalizing", "Draft–Sketch–Prove: informal proof → "
     "Lean outline with gaps → ATP/ITP tactics fill gaps",
     "Done" + (", evaluated (Section 6)" if dsp else "; evaluation pending")],
], widths=[2200, 4600, 2200])

# ------------------------------------------------------------------ method
d.heading("3. Evaluation setting", 1)
d.para("**Library.** Megalodon's `100thms_12.mg` (1,158 declarations: 999 "
       "theorems, 139 definitions, 13 axioms, 6 primitives, 1 parameter), "
       "exported from Megalodon's checked proof terms and translated to Lean 4. "
       "The translation is verified: all 999 original proofs compile, using only "
       "Megalodon's 17 foundational axioms. No Mathlib; Megalodon's own "
       "higher-order set theory with Church-encoded logic.")
d.para("**Held-out protocol.** Each theorem is attempted in turn with its proof "
       "hidden. The prover may use only declarations with a smaller index "
       "(earlier in the library). Search, premise-selection training and "
       "induction principles are all restricted accordingly.")
d.para("**Acceptance.** A proof counts only if all of the following hold:")
d.numbered([
    "Lean's kernel accepts it.",
    "Its statement is identical to the original theorem's, compared as "
    "elaborated Lean expressions (not text).",
    "The leak guard passes: the transitive closure of constants used by the "
    "proof term (through auxiliary definitions, with theorem bodies unfolded) "
    "contains no library constant at or after the target's index.",
    "No `sorryAx`.",
])
d.para("The compiled library contains all 999 theorems, so without (3) a proof "
       "could cite its own answer or a later equivalent. The guard is tested "
       "both ways: citing the target, or a later theorem with an identical "
       "statement, must be rejected; a genuine proof, or citing an earlier "
       "identical theorem, must be accepted. The first guard version passed "
       "cheating proofs (Lean hides theorem bodies unless asked with "
       "`allowOpaque`); these tests caught it.")

# ------------------------------------------------------------------ pipeline
d.heading("4. Pipeline", 1)
d.code("goal ─► Search ─► earlier facts ─► Vampire (16–512 facts, 30 s)\n"
       "                                     │ proof            │ no proof\n"
       "                                     ▼                  ▼\n"
       "                          facts it used      induction split,\n"
       "                                     │       Vampire per case\n"
       "                                     ▼                  │\n"
       "          Lean: battery → follow-ups → apply → Duper ◄──┘\n"
       "                   (kernel + statement check + leak guard)\n"
       "                                     │ all fail\n"
       "                                     ▼\n"
       "   LLM (Search's top 160 facts) proposes ─► Lean ─► error back to LLM")
d.heading("4.1 Search (premise selection)", 2)
d.para("Ranks the facts preceding the goal by a sum of: IDF-weighted symbol "
       "overlap (MePo-style); k-NN votes from the dependencies of the most "
       "similar earlier theorems; a recency term; and a naive Bayes score in the "
       "style of MaSh, trained on which facts earlier proofs used, over "
       "statement features that include shape (e.g. conclusion head, "
       "head–argument pairs, hypothesis heads), not only symbols. Name "
       "similarity is deliberately off: a newly conjectured lemma has no "
       "descriptive human name, so using it would inflate the benchmark.")
d.table([
    ["Recall: all facts the original proof cited are in the top k", "old @32",
     "new @32", "old @64", "new @64"],
    ["Second half of library (not used for tuning)", "31.9%", "36.2%", "46.4%", "51.8%"],
    ["327 non-induction theorems Vampire failed on (v1)", "12.2%", "19.6%", "22.6%", "33.0%"],
], widths=[4000, 1250, 1250, 1250, 1250])
d.heading("4.2 ATP: Vampire", 2)
d.para("Goal and ranked facts are rendered as THF; Megalodon's encoded "
       "connectives (`and`, `or`, `iff`, `ex`, Leibniz `eq`, …) map to native "
       "ones, and definitions are included transitively (depth 3). Vampire runs "
       "in portfolio mode for 30 s on the top 16, 32, 64, 128, 256 and 512 facts "
       "(v2 used 5 s on 16/32/64; v4 added 256 and 512). Its proof is "
       "not reused directly: the facts it used become the premise hints for "
       "Lean. Vampire proofs are not unique, and the facts of one proof may suit "
       "Lean better than another's, so every distinct premise set is kept.")
d.heading("4.3 ITP: Lean reconstruction", 2)
d.para("Kernel-checked bridge lemmas (`b_and`, `b_or`, `b_ex`, `b_eq`, …) turn "
       "the encoded logic into Lean's native logic so `grind` applies. A "
       "deterministic battery of tactic scripts is built from the hints: intro/"
       "unfold then `grind`; premises introduced as hypotheses then `grind`; "
       "`solve_by_elim`; unfolding only the goal's own definitions; set "
       "extensionality. The last two were distilled from the proofs the LLM "
       "found in v1. If the whole battery fails, a slower second line runs "
       "(v3): premises as `grind` e-matching lemmas, higher `grind` effort, and "
       "`simp_all` with premises and definitions. v4 added a third line of "
       "`apply` strategies and a fourth, Duper, a superposition prover running "
       "inside Lean that handles the higher-order instances `grind` cannot.")
d.table([["Strategy (first success)", "Theorems"]] +
        [[k, str(v)] for k, v in first.most_common()], widths=[4500, 2000])
d.heading("4.4 Automatic induction", 2)
d.para("Vampire does not invent induction predicates: given exactly the facts "
       "the original proof cited, it proved only 2 of 40 sampled induction "
       "theorems. When Vampire finds no proof, the pipeline reads the goal as "
       "P(x) for each variable x with a matching guard, instantiates each "
       "available principle (nat_ind, nat_complete_ind, ordinal_ind, "
       "SNoLev_ind, finite_ind, In_ind; only those proved before the goal), and "
       "sends each case to Vampire separately. In Lean: introduce, revert all "
       "but x and its guard, `apply` the principle (the motive is found by "
       "higher-order pattern unification), and prove each case with the "
       "battery. Each case is first tried as its own declaration, since Lean's "
       "heartbeat budget is per declaration.")
d.para(f"In the full run, induction proved {sum(ind.values())} theorems "
       f"({', '.join(f'{k} {v}' for k, v in ind.most_common())}), including "
       "commutativity of addition and of multiplication and associativity of "
       "addition on the naturals.")

# ------------------------------------------------------------------ results
d.heading("5. Results without an LLM", 1)
d.table([
    ["Run", "Proved", "Rate"],
    ["v1: Search (overlap, k-NN, recency) + Vampire + battery", str(len(P1)), pct(len(P1), 999)],
    ["v2: + learned Search, induction, distilled strategies, all Vampire proofs",
     str(len(P2)), pct(len(P2), 999)],
    ["v3: + Vampire 30 s with a 128-fact slice, second-line Lean strategies",
     str(len(P3)), pct(len(P3), 999)],
    ["**v4: + Duper, 256/512-fact slices, `apply` strategies**",
     f"**{len(P4)}**", f"**{pct(len(P4), 999)}**"],
    ["v4 + induction and earlier runs (no LLM)", str(len(NOLLM)), pct(len(NOLLM), 999)],
], widths=[6000, 1500, 1500])
rows_c = [["Category", "Theorems", "v1", "v3", "v4", "Final (with LLM)"]]
for c, label in CATS:
    tot = sum(1 for g in cat if cat[g] == c)
    cells = [label, str(tot)]
    for P in (P1, P3, P4, FINAL):
        a = sum(1 for g in cat if cat[g] == c and g in P)
        cells.append(f"{a} ({a / tot:.0%})")
    rows_c.append(cells)
d.table(rows_c, widths=[2400, 1200, 1400, 1400, 1400, 1700])
d.caption("Categories from the translator's vocabulary heuristic; approximate.")
d.para(f"v2 against v1: {len(P2 - P1)} theorems gained, {len(P1 - P2)} lost. "
       f"v3 against v2: {len(P3 - P2)} gained, {len(P2 - P3)} lost; v4 against v3: "
       f"{len(P4 - P3)} gained, {len(P3 - P4)} lost. The losses are "
       "borderline goals where Vampire found a different proof, or none within "
       "its time limit; the pipeline has run-to-run variation on such goals.")
d.para(f"Unproved by v4: {len(unproved)}. For {unproved_vamp} of them Vampire found a "
       f"proof that the Lean battery could not rebuild; for "
       f"{len(unproved) - unproved_vamp} Vampire found none.")
d.para("**How v3 was chosen.** Two targeted experiments on the v2 failures, "
       "before the v3 run: (1) on the 395 goals with no Vampire proof, Vampire "
       "with 30 s and a 128-fact slice found 66 proofs (most only at 128 facts), "
       "of which Lean rebuilt 32; a larger budget for the induction cases helped "
       "little (1 of 42 sampled). (2) On the 90 goals with a Vampire proof but no "
       "reconstruction, the second-line strategies rebuilt 6. Both were then "
       "built into the pipeline and measured by the single v3 run above.")
d.para("The typical remaining reconstruction failure needs a higher-order "
       "instance of a premise (e.g. the choice axiom `Eps_i_ax` at a specific "
       "predicate), which Vampire finds and `grind` does not.")
d.para(f"**Time per goal** (one goal at a time, as in use): in v4, proved goals "
       f"take a median of {secs_p[len(secs_p) // 2]:.0f} s, 90% within "
       f"{secs_p[int(len(secs_p) * .9)]:.0f} s; unproved goals are abandoned after a "
       f"median of {secs_f[len(secs_f) // 2]:.0f} s.")

# ------------------------------------------------------------------ LLM
d.heading("6. The LLM loop", 1)
d.para("The LLM sees the goal, Lean's goal state, the definitions used and the "
       "selected earlier facts, never the original proof or anything after the "
       "goal. Everything it writes goes through the same acceptance checks. "
       "Models are served through an OpenAI-compatible endpoint.")
d.heading("6.1 First evaluation: direct Lean with error feedback (v1)", 2)
d.para("Target: the 140 theorems where Vampire found a proof but the v1 battery "
       "could not rebuild it, with the same Vampire premise sets for every "
       "model. Up to 3 rounds, Lean's error returned each round.")
d.table([
    ["Model (28-theorem sample)", "Proved", "Avg time / theorem"],
    ["deepseek/deepseek-v4-flash", "11 / 28", "127 s"],
    ["openai/gpt-oss-120b", "9 / 28", "46 s"],
    ["minimax/minimax-m3", "7 / 28", "496 s (10 API timeouts)"],
    ["qwen/qwen3.8-27b", "2 / 28", "550 s (26 API timeouts; inconclusive)"],
], widths=[4000, 1800, 3200])
d.para(f"Cascade on all 140: gpt-oss-120b proved 41, then deepseek-v4-flash 10 "
       f"of the remaining 99: **51 / 140 (36%)**, all re-verified in fresh Lean "
       f"runs. {len(llm & P3)} of these 51 are now proved by v3 without an LLM, "
       "because the strategies distilled from them generalise.")
d.heading("6.2 Draft, sketch, prove (v3)", 2)
d.para("The sketch's \"LLM proving lemma → LLM formalizing proof\" path, in the "
       "style of Draft, Sketch, and Prove (Jiang et al., ICLR 2023):")
d.numbered([
    "**Draft** (1 call): the model writes an informal numbered proof, naming "
    "the facts each step uses and, for induction, the principle and predicate.",
    "**Sketch** (1 call): it formalizes that proof as a Lean outline of "
    "intermediate `have` steps, leaving any routine step as `sorry`.",
    "**Prove** (no LLM): each `sorry` is replaced by the automatic tactics "
    "(`grind`, `solve_by_elim` over the selected facts); Lean checks the whole.",
    "**Repair** (1 call): on failure, Lean's error goes back once; the model "
    "revises the outline. A script rejected only because it continues after "
    "the goal is closed is retried with trailing lines removed (no call).",
])
if dsp:
    from llm import usage_summary
    won = [r for r in dsp if r["proved_by"]]
    u = usage_summary(os.path.join(R, "llm_usage_dsp.jsonl"))
    d.para(f"**Budgeted run.** Hard cap of 100 calls on gpt-oss-120b. Sample: "
           f"every 15th of the {sum(1 for r in v2.values() if not r['proved_by'])} theorems the v2 pipeline did not "
           f"prove (33 theorems, not hand-picked). The first was a live test; "
           f"it failed on a script that continued after the proof was complete, "
           f"which motivated the trimming step. Its stored reply passes after "
           f"trimming but is **not counted**. The remaining {len(dsp)} were run "
           f"with the final code.")
    d.para(f"**Result: {len(won)} / {len(dsp)} proved** "
           f"({pct(len(won), len(dsp))}) under the same acceptance checks as "
           f"every other proof. API usage for the whole pass: {u['calls']} calls, "
           f"{u['prompt_tokens']:,} prompt and {u['completion_tokens']:,} "
           f"completion tokens.")
    d.table([["Final failure reason", "Theorems"],
             ["Lean heartbeat budget exhausted while filling gaps", "13"],
             ["Encoded logic / opaque sets treated as Lean-native", "11"],
             ["Type mismatch", "3"],
             ["Wrong number of intro steps", "2"],
             ["Other", "3"]], widths=[6000, 2000])
    d.para("**Post-hoc check (no API calls).** All 64 stored outlines were "
           "re-checked with 5× the heartbeat budget: 0 / 64 pass, and the same "
           "20 time out at the same points. The gaps the model leaves are too "
           "coarse for the automatic tactics, rather than cut short by the budget.")
    d.para("**Reading.** The path works end to end, but on this hard remainder "
           "(only 4 of the 32 had a Vampire proof) a general-purpose model with 3 "
           "calls does not produce usable outlines in Megalodon's encoding. The "
           "clearest levers: few-shot examples drawn from the 51 successful "
           f"direct-mode proofs and the {len(P3)} pipeline proofs, finer outlines (more, "
           "smaller `have` steps), and per-gap checking so that each gap is "
           "reported back to the model individually.")
    if won:
        d.table([["Theorem proved", "Round", "Gaps filled by automation"]] +
                [[f"`{r['goal']}`", r["proved_by"].replace("dsp-r", ""),
                  str(next(t.get("gaps", 0) for t in r["transcript"] if t.get("ok")))]
                 for r in won], widths=[4500, 1500, 3000])
else:
    d.para("[Results of the budgeted run to be added.]")

d.heading("6.3 The fixed LLM loop (v5–v9)", 2)
d.para("From v5 the LLM loop runs over every theorem the pipeline leaves "
       "unproved: up to 7 rounds per theorem, each round a Lean check whose "
       "error goes back to the model. Model: deepseek/deepseek-v4-flash, served "
       "through the SingularityNET gateway.")
d.table([
    ["Version", "What changed", "Proved", "Gain"],
    ["v4 + earlier", "No LLM", str(len(NOLLM)), "—"],
    ["v5", "Hidden failures fixed (73% of replies were empty: the model used "
     "the gateway's 8,192-token reply limit on thinking); free repairs "
     "(indentation, `eq` bridge, finishing leftover goals); few-shot examples",
     str(len(NOLLM | L5)), f"+{len(L5)}"],
    ["v6", "Real feedback: in 49% of failed attempts the model had been shown "
     "a misleading indentation error; scripts are normalized before checking",
     str(len(NOLLM | L5 | L6)), f"+{len(L6)}"],
    ["v7", "96 facts per theorem instead of 24", str(len(NOLLM | L5 | L6 | L7)), f"+{len(L7)}"],
    ["v8", "160 facts, 7 rounds", str(len(NOLLM | L5 | L6 | L7 | L8)), f"+{len(L8)}"],
    ["**v9**", "Lemmas shown as Lean prints them; a misapplied lemma is "
     "answered with its signature", f"**{len(FINAL)}**", f"+{len(L9)}"],
], widths=[1200, 5300, 1300, 1200])
d.para("**Missing lemmas, not reasoning.** On the 257 hardest theorems the "
       "human proofs cite a median of 13 earlier lemmas. Search's top 24 facts "
       "contained all of them for only 7 theorems; the top 96 for 66 (recall "
       "0.45 at 24, 0.79 at 96, 0.87 at 160). Raising the facts shown from 24 to "
       "96 added 77 proofs in one run, many in the first rounds, including "
       "theorems that hours of decomposition had failed on.")
d.para("**What did not help.** Showing the model Vampire's whole proof (34 / 51 "
       "with it, 34 / 51 without, same facts); planning a proof as an outline "
       "whose steps are proved as separate lemmas (most steps proved, a hard "
       "core step stayed open: 0 / 3 theorems); embedding-based fact retrieval "
       "(recall 0.48 at 96 facts against Search's 0.79); and other models on the "
       "hardest theorems: gpt-oss-120b, gemma-4-31b, minimax-m3, asi1 and "
       "qwen3.8 proved none of the goals tried, including goals "
       "deepseek-v4-flash proves.")
d.para("**Cost and stopping.** The LLM work used about 11,800 calls (162 M "
       "input and 59 M output tokens). New proofs cost about 26 calls each in "
       "v7 and about 74 in v9, as the remaining theorems grow harder; Phase 1 "
       f"stops at {len(FINAL)}, with {999 - len(FINAL)} theorems unproved, mostly "
       "long surreal-number and integer-arithmetic proofs.")

# ------------------------------------------------------------------ limits
d.heading("7. Limitations", 1)
d.bullets([
    "One library (999 theorems) in one foundation; results may not transfer "
    "unchanged to other libraries or to Mathlib-style Lean.",
    "Download is retrieval from this library only; no external sources yet.",
    "Run-to-run variation on borderline goals (Vampire's time limit, LLM "
    f"sampling): for example, {len(P3 - P4)} v3 successes were not reproduced in v4.",
    "Category figures use a vocabulary heuristic.",
    "The LLM results depend on one model (deepseek-v4-flash) on one gateway, "
    "whose response time was the main bottleneck.",
    "Speed was not optimised: each Lean check starts a fresh process and "
    "reloads the library, and a batch finishes every candidate even after one "
    "succeeds.",
])

# ------------------------------------------------------------------ next
d.heading("8. Next steps", 1)
d.numbered([
    f"Phase 1 is closed at {len(FINAL)} / 999.",
    "Phase 2: Hyperon drives Lean. A MeTTa inference controller decides each "
    "proof step (automation, a lemma to apply, an LLM suggestion, a split) and "
    "Lean checks it; the library and the proved theorems move into a Math "
    "Atomspace, so lemmas are retrieved from memory rather than re-proved. "
    "Step-by-step Lean is feasible: through the Lean REPL the library loads in "
    "0.2 s and each step takes under 0.01 s.",
    "Phase 3: PLN feeding the inference controller.",
])

# ------------------------------------------------------------------ appendix
d.heading("Appendix: reproducing", 1)
d.code("cd phase1\n"
       "python3 test_guard.py                                 # leak-guard controls\n"
       "python3 experiment.py 1 6 ../results/phase1_full_v4.jsonl   # full run, no LLM\n"
       "python3 recheck_full.py ../results/phase1_full_v4.jsonl 6 ../results/recheck_v4.jsonl\n"
       "# LLM loop over every theorem still unproved, then re-verification\n"
       "PYTHONPATH=. python3 experiments/try_llm_vampire_sweep.py prep-search ../results/rest.jsonl --facts 160\n"
       "PYTHONPATH=. python3 experiments/try_llm_vampire_sweep.py run ../results/rest.jsonl ../results/out.jsonl noproof \\\n"
       "    --rounds 7 --workers 4 --examples 3 --model deepseek/deepseek-v4-flash-0731\n"
       "PYTHONPATH=. python3 experiments/verify_vp_final.py ../results/verified.json ../results/out.jsonl")
d.para("Repositories: ai-mathematician (this system) and megalodon-lean4 (the "
       "verified Megalodon → Lean 4 translator).")

d.save(out_path)
print("wrote", out_path)
