# Phase 1 — what it does, what worked, what didn't

**Status: 877 / 999 theorems (87.8%), every one kernel-checked.**
665 come from the pipeline without any LLM, 212 from the LLM loop (§5).

The system is given *only a theorem's statement* — never the human's proof — and
must produce a proof that Lean's kernel accepts.

---

## 1. The pipeline, in four stages

```
statement  →  [1] SEARCH  →  [2] VAMPIRE  →  [3] LEAN  →  [4] GUARD  →  proved
              rank facts      find which      rebuild      verify
                              facts matter    the proof
                   │
                   └──────→  [5] LLM loop (when 2–3 fail): proposes a proof, sees Lean's error, retries
```

| stage | file | what it does |
|---|---|---|
| 1. Search | `phase1/search.py` | ranks the facts declared *before* this theorem: IDF symbol overlap + k-nearest-neighbour + naive Bayes over past proof citations |
| 2. ATP | `phase1/atp.py` | writes a TPTP/THF problem, runs **Vampire** at premise slices k=16…512, keeps *only the list of facts its proof used* |
| 3. ITP | `phase1/prover.py` | builds tactic scripts from those facts and checks them in Lean 4. Four lines: battery → follow-ups → `apply` → **Duper** |
| 4. Guard | `phase1/itp.py` | statement identity, no `sorryAx`, no leak |
| 5. LLM loop | `phase1/llm.py` | for goals stages 2–3 cannot prove: the LLM writes a Lean proof from Search's top 160 facts, sees Lean's error, retries (§5) |

Vampire and the LLM only propose proofs; every proof is verified by Lean
and the guard.

**The guard is what makes the number mean something:**
1. **statement identity** — the proved type must equal the library's declaration
2. **no `sorryAx`** — no holes
3. **leak check** — nothing cited at an index ≥ the goal's

### Run it live

```bash
cd phase1
python3 demo.py                # 1 + 1 = 2, full trace, ~10 s
python3 demo.py --list         # other examples
python3 demo.py binunion_idl   # a reconstruction FAILURE, same trace
```

---

## 2. Where the failures actually are

| | count | share |
|---|---|---|
| Vampire **finds** a proof | 680 | 68% |
| → of those, Lean rebuilds | **621** | **91%** |
| Vampire **finds nothing** | **319** | **32%** |

**Lean's reconstruction is the strong link (91%).** The dominant failure is the
ATP finding nothing at all. This corrects an earlier claim of ours that had it
the other way round.

And the reason is not higher-order weakness — it is **induction**:

| | proof cites an induction principle |
|---|---|
| the 319 ATP failures | **39%** |
| the 640 successes | **7%** |

Saturation provers (Vampire, Zipperposition, E, Satallax) work by refutation:
negate the goal, derive a contradiction. **Induction is not a refutation step** —
it requires inventing an induction hypothesis, which no saturation calculus
generates. No change of prover fixes this.

---

## 3. What we tried — what helped and what didn't

| attempt | code | result | verdict |
|---|---|---|---|
| **Longer ATP budget** (30 s → 300 s) | `experiments/try_vampire_budget.py` | 12 new ATP proofs → **+5** theorems | **helped** |
| **LLM loop**, fixed and given more facts | `phase1/llm.py`, `experiments/try_llm_vampire_sweep.py` | **+212** theorems over v5–v9 (§5) | **helped most** |
| **Induction, unstarved** | `experiments/try_induction_hard.py`, `experiments/hybrid_induction.py` | **+4** and **+7** theorems | **helped** |
| Incremental proof search | `experiments/incremental.py` | 5/359 after 73,393 partial scripts | marginal |
| Duper with throttles removed | `experiments/try_duper_hard.py`, `experiments/duper2.py` | 1/51 | **no** — it was already working at full strength |
| **Zipperposition** (2nd ATP) | `experiments/zipper.py`, `experiments/try_zipper.py` | **1/300**, four modes, all zero | **no** — see §2 |
| Depth-2 backward chaining | `experiments/try_apply2.py` | 1/40 | no |
| Vampire proof replay | `vampire_proof.py`, `experiments/proof_profile.py` | only **2/40** refutations use rules any published Lean replay tool supports | not viable (higher-order) |
| Vampire's proof shown to the LLM | `experiments/try_llm_vampire_sweep.py` | 34/51 with it, 34/51 without (same facts) | **no** |
| Planning: LLM outline, each step a lemma | `experiments/dsp.py`, `experiments/decompose.py` | most steps proved, a hard core step stays open; 0/3 goals | **no** |
| Embedding-based fact retrieval | `experiments/embed_search.py` | recall 0.48 at 96 facts vs Search's 0.79 | **no** |

### Duper — the honest account

Duper is a superposition prover that runs **inside** Lean and handles
higher-order unification, which `grind` cannot. It is the **4th and strongest
reconstruction line** and earned its place: **51 of 109** goals every other
tactic failed on.

We suspected it was being throttled (900 s cap, only 2 premise sets) and removed
the limits. **Gain: 1 theorem.** So Duper matters — but it was already working at
full strength, and the throttle was not the problem.

### Zipperposition — the decisive negative

Zipperposition wins the CASC **higher-order** division, exactly where Vampire is
weakest. Installed, integrated, and **validated 10/10 on goals we already prove**
— so the plumbing is correct.

Run on all 300 goals Vampire fails, in four configurations
(`default`, `ho-competitive`, `ho-pragmatic`, `ho-comb-complete`): **1 theorem.**

Two state-of-the-art higher-order provers with different calculi fail on the
same goals. That closes the question — the blocker is induction, not the prover.

---

## 4. The induction finding

The induction module (`phase1/induction.py`) recognises a goal shaped
`forall x, guard x -> … -> conclusion` and splits it into base and step cases.

**When it engages, Lean closes the proof 70% of the time (14 / 20).**
It was engaging on only 20 of 319 goals.

**Why:** `Prover.induction_split` accepts a split only if Vampire proves *every*
case — and gave it **5 seconds** at slices 16/32/64, while the rest of the
pipeline uses **30 seconds** and up to **512** facts. Good splits were being
discarded on the clock.

The recogniser proposes a valid split for **87 of 88** goals needing a principle
it already knows. Re-running with the normal budget:

```bash
PYTHONPATH=. python3 experiments/try_induction_hard.py ../results/ind_target.jsonl 3 out.jsonl \
        --timeout 30 --slices 16,32,64,128,256 --lean-anyway
```

**+4 in the first 21 goals**, including three `In_rec` theorems nothing else
has touched.

---

## 5. The LLM loop (v5–v9): from 665 to 877

The LLM (DeepSeek-V4-Flash) writes a Lean proof, Lean checks it, and the LLM
sees the error and tries again, up to 7 rounds. Three changes made it work:

1. **Fixing hidden failures.** About 73% of replies were empty: the model
   spent the gateway's 8,192-token reply limit thinking and was cut off before
   answering. Such replies are now re-asked with the model's own notes and
   thinking switched off. And in 49% of failed attempts the model had been
   shown a misleading error, caused by indentation (Lean read the next lines
   of its proof as part of the first); scripts are now normalized before
   checking, so the model sees the real error.
2. **Giving it the right lemmas.** On the hardest 257 theorems, the human
   proofs cite a median of 13 earlier lemmas. Search's top 24 facts held all
   of them for only 7 theorems; the top 96 for 66. Showing 96, then 160 facts
   instead of 24 added about 100 proofs — the largest single gain.
3. **Showing lemmas clearly.** With the right lemmas present, the commonest
   remaining error was a lemma applied with its arguments in the wrong order.
   Lemmas are now shown as Lean prints them (`phase1/lean_sigs.py`), and a
   misapplied lemma is answered with its signature.

Only DeepSeek proved these goals; GPT-OSS-120B, Gemma, MiniMax, ASI1 and Qwen
did not. Every LLM proof was re-verified from scratch in fresh Lean runs
(`results/llm_proofs_verified.json`, `v6v7_verified.json`,
`v8v9_verified.json`: 212 / 212). The remaining 122 theorems are mostly long
surreal-number and integer-arithmetic proofs; each further pass found fewer
proofs, and Phase 1 stops at 877.

---

## 6. Reproducing any of it

```bash
cd phase1
python3 demo.py <theorem>                 # one theorem, full trace
python3 experiment.py 1 4 out.jsonl       # the full 999-theorem run
python3 recheck.py <run.jsonl> 4 out.jsonl  # re-verify in fresh Lean processes
```

All 640 of the v4 run were independently re-proved in fresh Lean processes:
`results/recheck_v4.jsonl` — **640 / 640**. The 212 LLM proofs were re-verified
the same way (§5).
