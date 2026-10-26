# Phase 1 with LLM intervention — v1

Run: 2026-09-24/25. Builds on `phase1_baseline_v1.md` (418/999, no LLM).

## Setting

The LLM is a proposer inside a feedback loop: it writes a Lean
tactic script, Lean checks it, and on failure the model sees Lean's actual
error and tries again (up to 3 rounds). It is shown only the goal, Lean's
goal state after `intros`, the definitions the goal uses, and premises
drawn strictly from before the goal — never the original proof. Every
proof must pass the same bar as the baseline: Lean kernel, statement
identity, and the leak guard.

Target set: the **140 theorems where Vampire found a proof but the
deterministic Lean reconstruction failed.** Each model received the same
Vampire premise set from the baseline run.

## Model comparison (fixed 28-theorem sample of the 140)

| Model | Proved | Avg time / theorem | Notes |
|---|---|---|---|
| deepseek/deepseek-v4-flash-0731 | 11 / 28 | 127s | no API errors |
| openai/gpt-oss-120b | 9 / 28 | 46s | no API errors |
| minimax/minimax-m3 | 7 / 28 | 496s | 10/28 cut short by API timeouts (180s) — underestimate |
| qwen/qwen3.8-27b | 2 / 28 | 550s | 26/28 cut short by API timeouts — **inconclusive** |

Union of all four: 13/28. The two reliable models largely solve the same
theorems (8 in common; union 12).

## Full run: cascade on all 140

Stage 1, gpt-oss-120b (fast): **41 / 140**.
Stage 2, deepseek-v4-flash on the 99 left: **10 / 99**.

**LLM stage recovered 51 / 140 (36%).** All 51 proofs were independently
re-verified in fresh Lean runs (`phase1/recheck.py`): 51/51.

## Overall

| | Proved | Rate |
|---|---|---|
| Baseline (no LLM) | 418 / 999 | 41.8% |
| + LLM cascade on reconstruction failures | **469 / 999** | **46.9%** |

## Not yet attempted

- The 441 theorems where Vampire found **no** proof. On a 6-theorem probe
  of the hardest of these the LLM proved 1; they are dominated by
  induction-style proofs.
- Qwen and MiniMax with longer API timeouts, for a complete comparison.
