# Experiments

One-off experiment drivers and the helper modules only they use. The
system itself (Search, Vampire, Lean, the LLM loop) is in `phase1/`; these
scripts are kept so every number in the README and the walkthrough can be
reproduced.

Run them from `phase1/`, with `phase1/` on the path (they read
`../data/corpus.sexpr` relative to it):

    cd phase1
    PYTHONPATH=. python3 experiments/<script>.py ...

| Area | Scripts |
|---|---|
| Vampire budgets and rebuilds | `try_vampire_budget.py`, `try_t300_rebuild.py`, `rerun_vampire.py`, `try_rebuild.py`, `rebuild_hits.py`, `rebuild_failures.py`, `rebuild_induction.py` |
| Induction | `try_induction.py`, `try_induction_budget.py`, `try_induction_hard.py`, `hybrid_induction.py`, `recheck_hybrid.py`, `oracle_haves.py`, `chain_prove.py` |
| Other provers | `try_duper.py`, `try_duper2.py`, `try_duper_hard.py`, `try_duper_search.py`, `duper2.py`, `zipper.py`, `try_zipper.py`, `try_atp.py` |
| Lean-side search | `incremental.py`, `try_incremental.py`, `try_apply.py`, `try_apply2.py`, `prop_synth.py`, `try_prop_synth.py`, `try_diverse.py` |
| LLM | `try_llm.py`, `try_llm_sweep.py`, `llm_experiment.py`, `dsp.py`, `try_llm_vampire.py`, `try_llm_vampire_sweep.py` (the v5 sweep), `recheck_vp_repairs.py`, `verify_vp_final.py` (re-verification) |
| Analysis | `eval_search.py`, `proof_profile.py`, `witness_audit.py`, `oracle_v3.py`, `embed_search.py` (embedding retrieval: lower recall than Search, negative result) |
