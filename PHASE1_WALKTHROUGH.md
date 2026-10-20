# Phase 1 — what it does, what worked, what didn't

**Status: 662 / 999 theorems (66.3%), every one kernel-checked.**

The system is given *only a theorem's statement* — never the human's proof — and
must produce a proof that Lean's kernel accepts.

---

## 1. The pipeline, in four stages

```
statement  →  [1] SEARCH  →  [2] VAMPIRE  →  [3] LEAN  →  [4] GUARD  →  proved
              rank facts      find which      rebuild      verify
                              facts matter    the proof
```

| stage | file | what it does | trusted? |
|---|---|---|---|
| 1. Search | `phase1/search.py` | ranks the facts declared *before* this theorem: IDF symbol overlap + k-nearest-neighbour + naive Bayes over past proof citations | n/a |
| 2. ATP | `phase1/atp.py` | writes a TPTP/THF problem, runs **Vampire** at premise slices k=16…512, keeps *only the list of facts its proof used* | **no** — its proof is discarded |
| 3. ITP | `phase1/prover.py` | builds tactic scripts from those facts and checks them in Lean 4. Four lines: battery → follow-ups → `apply` → **Duper** | **yes** |
| 4. Guard | `phase1/itp.py` | statement identity, no `sorryAx`, no leak | **yes** |

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
| **LLM proposer** w/ Lean-error feedback | `experiments/try_llm_sweep.py` | 7/59 on the hardest subset, 185 calls | **helped** |
| **Induction, unstarved** | `experiments/try_induction_hard.py` | **+4 so far**, run in progress | **helping — best lead** |
| Incremental proof search | `experiments/incremental.py` | 5/359 after 73,393 partial scripts | marginal |
| Duper with throttles removed | `experiments/try_duper_hard.py`, `experiments/duper2.py` | 1/51 | **no** — it was already working at full strength |
| **Zipperposition** (2nd ATP) | `experiments/zipper.py`, `experiments/try_zipper.py` | **1/300**, four modes, all zero | **no** — see §2 |
| Depth-2 backward chaining | `experiments/try_apply2.py` | 1/40 | no |
| Vampire proof replay | `vampire_proof.py`, `experiments/proof_profile.py` | only **2/40** refutations use rules any published Lean replay tool supports | not viable (higher-order) |

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

## 4. The induction finding (the current work)

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

## 5. Reproducing any of it

```bash
cd phase1
python3 demo.py <theorem>                 # one theorem, full trace
python3 experiment.py 1 4 out.jsonl       # the full 999-theorem run
python3 recheck.py <run.jsonl> 4 out.jsonl  # re-verify in fresh Lean processes
```

All 640 of the v4 run were independently re-proved in fresh Lean processes:
`results/recheck_v4.jsonl` — **640 / 640**.
