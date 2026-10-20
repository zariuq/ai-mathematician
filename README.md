# AI Mathematician

A system for proving mathematical lemmas by combining automated search,
automated theorem proving, language models, and a proof checker, where
**nothing counts as proved unless Lean 4's kernel accepts it.**

Built phase by phase:

| Phase | Components | Status |
|---|---|---|
| 1 | Search + Download · ATP (Vampire) · ITP (Lean 4) · LLM proposer with Lean-error feedback · LLM informal proof → formal outline | Built and benchmarked; Download = retrieval from the library (external sources later) |
| 2 | Inference controller (LLM + Hyperon) · Math Atomspace working memory / long-term memory · research papers → long-term memory | Not started |
| 3 | PLN (probabilistic logic networks) feeding the inference controller | Not started |

## Phase 1 result

On the 999-theorem reference library (Megalodon's `100thms_12.mg`,
translated to Lean 4 by the companion
[megalodon-lean4](https://github.com/yenat/megalodon-lean4) translator):

| Version | What changed | Proved | Gain |
|---|---|---|---|
| v1 | Search + Vampire + Lean `grind` (no LLM) | 418 | baseline |
| v2 | Learned Search, distilled tactics, automatic induction | 514 | +96 |
| v3 | Vampire with a 128-fact slice, second-line Lean strategies | 563 | +49 |
| v4 | Duper (Lean-native prover), 256/512-fact slices, `apply` strategies | 640 | +77 |
| v4 + earlier experiments | Hybrid induction, 300 s Vampire, older versions' extras | 665 | +25 |
| v5 | Testing the LLM with Vampire's whole proof exposed 73% empty LLM replies. Fixes: rescue cut-off replies, free repairs (indentation, `eq` bridge, finish leftover goals), 5 rounds, few-shot examples | 742 | +77 |
| v6 | The model now gets real errors (49% of feedback had been bogus), closest real lemma names suggested for invented ones, every network error retried, deepseek only | 755 | +13 |
| v7 | 96 facts instead of 24. The measurement showed only 7 of 257 goals had every needed lemma in the old 24 | **832** | +77 |
| v8 (running) | 160 facts, 7 rounds | 842 so far | +10 (27 of 167 goals done) |

Every one kernel-checked; **all 640 v4 proofs were re-verified independently
in fresh Lean runs (`recheck_v4.jsonl`: 640 / 640)**, as were the 563 v3
proofs and the 51 LLM-found proofs. The LLM proofs of v5 were re-verified
from scratch (`results/llm_proofs_verified.json`: 77 / 77), as were those of
v6 and v7 (`results/v6v7_verified.json`: 90 / 90). The 25 from earlier
experiments (automatic induction, theorems earlier versions proved) were
verified when found (`results/phase1_v5_summary.json` lists them). v8's
proofs are re-verified the same way when its run ends.

Where v4's +77 came from, by proof line (v4 vs v3):

| line | v4 | v3 | change |
|---|---:|---:|---:|
| `duper` (Lean-native superposition) | 44 | 0 | **+44** |
| `prem-grind` | 302 | 287 | +15 |
| `prem-unfold-grind` | 133 | 122 | +11 |
| `apply` | 7 | 0 | +7 |
| `solve_by_elim` | 40 | 37 | +3 |
| others | — | — | −3 net |

The single largest gain in v4 is Duper, a classical symbolic prover with no
machine learning in it. The run cost 79 core-hours.

### v5: the LLM loop, fixed

Up to v4 the LLM contributed least of the five stages. Testing whether it
does better when shown Vampire's whole proof, not just the facts it used,
exposed why: **about 73% of LLM replies were empty**. The gateway caps a
reply at 8,192 tokens and the model spent them all thinking. Many of the
remaining scripts had the right argument but failed on indentation, or
stopped one step short. Under load, a 180 s timeout also discarded whole
goals. Fixes, all in `phase1/llm.py`:

- **Rescue:** a reply that runs out while thinking is re-asked with its own
  notes and thinking switched off.
- **Free repairs** (no LLM call, every result still fully checked): fix
  indentation, insert the bridge before the last step, and close leftover
  goals with the pipeline's own `grind` / `solve_by_elim`.
- 5 rounds instead of 3, a 600 s timeout, and few-shot examples: accepted
  proofs of similar *earlier* theorems only.

With the fixes the LLM found 77 proofs, all re-verified. They include 47 of
the 59 goals Vampire proves but Lean could not rebuild. In the final sweep
over every goal still unproved, deepseek-v4-flash proved 27 and gpt-oss-120b
8. Once the empty replies were fixed, showing the LLM Vampire's proof made
no measurable difference (34 / 51 with it, 34 / 51 without, same facts).

The informal→formal pass (`experiments/dsp.py`) returned 1 / 32 on the
hardest residual goals before these fixes; it has not been re-run since.

Details: `results/phase1_baseline_v1.md` (baseline, failure
analysis), `results/phase1_llm_v1.md` (model comparison, cascade),
`results/phase1_v2.md` (v2 and v3 runs), `results/phase1_llm_dsp.md` (LLM
informal→formal pass). Phase 1 report: `report/Phase1_Report_DRAFT.docx`.

### What "proved" means here

Each theorem is held out in turn. The prover sees only its statement plus
declarations that come *before* it in the library. A proof counts only if:

1. Lean 4's kernel accepts it;
2. its statement is identical to the original theorem's (compared as
   elaborated Lean expressions, not text);
3. the **leak guard** confirms the proof term uses no library fact at or
   after the target. The compiled library contains all 999 theorems, so
   without this a proof could quietly cite the answer.

The guard is itself tested in both directions (`phase1/test_guard.py`):
citing the target, or a later theorem with the same statement, must be
rejected; a genuine proof, or citing an earlier identical theorem, must be
accepted. The first version of the guard passed cheating proofs; these
tests caught it.

Vampire and the LLM are **untrusted**: they only propose. Lean decides.

## How it works (Phase 1)

```
goal ──> Search ──> ranked facts ──> Vampire (untrusted) ──> premises that worked
                                                                  │
                        LLM (untrusted, optional) ── proposes ────┤
                                  ▲                               ▼
                                  └── Lean's error ◄── Lean 4 (trusted) + statement check + leak guard
```

- `phase1/library.py`: loads every declaration from Megalodon's typed
  export, in order, with the symbols each mentions.
- `phase1/search.py`: ranks earlier facts for a goal (rare shared
  concepts, what similar earlier proofs used, recency). No LLM.
- `phase1/atp.py`: goal + facts → higher-order TPTP → Vampire, tried at
  several premise-slice sizes. Megalodon's encoded logic is mapped to
  native connectives for Vampire.
- `lib/Bridge.lean`: kernel-checked lemmas converting Megalodon's encoded
  logic (`and`, `or`, `ex`, Leibniz `eq`, …) to Lean's native logic, so
  Lean's `grind` automation can work on it.
- `phase1/itp.py`, `phase1/prover.py`: build Lean proof attempts, check
  them, apply the statement check and leak guard.
- `phase1/llm.py`: LLM proposes a Lean tactic script, sees Lean's
  error on failure, retries (the feedback loop from the design sketch),
  with the rescue and free repairs described above.
  `experiments/try_llm_vampire_sweep.py` runs it over many goals;
  `recheck.py` and `experiments/verify_vp_final.py` independently
  re-verify every LLM-found proof.
- `phase1/vampire_proof.py`: parses Vampire's refutation and rewrites it
  for an LLM prompt (library names, bookkeeping steps collapsed).
- `phase1/experiments/`: one-off experiment drivers, kept so every number
  here can be reproduced (see its README).

## Setup

Requires Python 3.8+ (standard library only), Lean 4.34.0, and Vampire.

```bash
# 1. Vampire 5.1.0 (prebuilt binary)
mkdir -p tools data && cd tools
wget https://github.com/vprover/vampire/releases/download/v5.1.0/vampire-Linux-X64.zip
unzip vampire-Linux-X64.zip && chmod +x vampire && cd ..

# 2. Library data: Megalodon's typed export of the reference corpus,
#    produced by the patched Megalodon in megalodon-lean4's
#    sexprinfo-prototype/ (see its README):
#      megalodon -sexprinfo 100thms_12.mg > data/corpus.sexpr

# 3. Compile the Lean library once (a few minutes)
cd lib
lean --root=. -o MegLib.olean MegLib.lean
LEAN_PATH=. lean -o Bridge.olean Bridge.lean
cd ..
```

Set `LEAN_BIN` if `lean` isn't at the default path in `phase1/itp.py`.

```bash
# 4. Optional: Duper (Lean-native superposition prover used to rebuild
#    Vampire proofs that grind cannot; the prover uses it when present)
mkdir -p tools/duper-env && cd tools/duper-env
echo 'leanprover/lean4:v4.34.0' > lean-toolchain
printf 'name = "duperenv"\n\n[[require]]\nname = "Duper"\ngit = "https://github.com/leanprover-community/duper.git"\nrev = "v4.34.0"\n' > lakefile.toml
lake update && lake build Duper
# lean-auto downloads the zipperposition binary with curl during the build;
# without curl, place zipperposition.exe in .lake/packages/auto/.lake/build/
cd ../..
```

For the LLM plug-in only: create `.env` in the repo root (git-ignored)
with `LLM_API_KEY=...` and `LLM_BASE_URL=...` (an OpenAI-compatible
endpoint).

## Running

```bash
cd phase1
python3 test_guard.py                 # leak-guard controls: must all pass
python3 search.py ../data/corpus.sexpr   # Search recall vs. real proofs
python3 experiment.py 33 6 out.jsonl  # sample: every 33rd theorem, 6 workers
python3 experiment.py 1 6 out.jsonl   # full benchmark (~7h on 6 workers)
PYTHONPATH=. python3 experiments/try_llm.py <thm1,thm2> openai/gpt-oss-120b 4   # LLM loop, experimental

# the v5 LLM sweep over every goal no run has proved yet, then re-verification
PYTHONPATH=. python3 experiments/try_llm_vampire_sweep.py prep-search ../results/rest.jsonl
LLM_LEDGER=../results/rest_ledger.jsonl LLM_CALL_CAP=4000 PYTHONPATH=. \
  python3 experiments/try_llm_vampire_sweep.py run ../results/rest.jsonl ../results/rest_out.jsonl noproof \
  --rounds 5 --workers 3 --examples 3 --model deepseek/deepseek-v4-flash-0731
PYTHONPATH=. python3 experiments/verify_vp_final.py ../results/verified.json ../results/rest_out.jsonl
```

## Known limits

- The library uses Megalodon's own foundations inside Lean (no Mathlib),
  so Lean's automation only works well after the bridge rewrite.
- 257 theorems remain unproved. Most need a long multi-step argument
  (surreal-number arithmetic above all): the LLM fails there on the
  argument itself, not on formatting. Borderline goals vary between runs
  because of Vampire's time limit and LLM sampling.
- On the LLM gateway, deepseek-v4-flash is the stronger model but is
  heavily loaded (minutes per reply); gpt-oss-120b answers in seconds.
- Category percentages use a vocabulary heuristic and are approximate.
