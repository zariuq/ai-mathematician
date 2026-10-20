"""Synthesise -> translate -> kernel-check, with no search anywhere in Lean.

For each propositional theorem: build a Megalodon proof term (prop_synth),
render it to a Lean term with the existing translator (sexpr_translate), and
hand Lean `exact <term>`. `exact` type-checks; it does not search. The result
goes through the ordinary guard -- statement identity against the library
declaration, no sorryAx, no leak -- so a pass here means exactly what a pass
means for the 640.

Usage: python3 try_prop_synth.py <workers> <out.jsonl>
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

import sexpr_translate as T
from library import load
from itp import load_statements
from prop_synth import Synth
from prover import Prover, _lean_name

CORPUS = "../data/corpus.sexpr"
PROP = {"and", "or", "not", "iff", "False", "True", "ex"}


def make_ctx(decls):
    ctx = T.Ctx()
    for d in decls:
        if d.hash:
            ctx.hash_to_name[d.hash] = _lean_name(d.name)
    for d in decls:
        if d.kind == "PRIM":
            ctx.prim_to_name[d.index] = _lean_name(d.name)
    return ctx


def main():
    workers, out = int(sys.argv[1]), sys.argv[2]
    decls = load(CORPUS)
    prover = Prover(decls, CORPUS, load_statements())
    targets = [d for d in decls
               if d.kind == "THM" and set(d.stmt_syms) <= PROP]
    synth = Synth(decls, max_depth=14)

    built = []
    for d in targets:
        try:
            pf = synth.prove(d.stmt)
        except RecursionError:
            pf = None
        if pf is None:
            built.append((d, None, "no proof term synthesised"))
            continue
        ctx = make_ctx(decls)
        try:
            term = T.pf_to_lean(pf, ctx)
        except Exception as e:
            built.append((d, None, f"render failed: {type(e).__name__}: {e}"))
            continue
        built.append((d, term, None))

    print(f"{len(targets)} propositional theorems, "
          f"{sum(1 for _, t, _ in built if t)} proof terms synthesised",
          flush=True)

    def check(item):
        d, term, why = item
        if term is None:
            return {"goal": d.name, "ok": False, "why": why, "term": None}
        t0 = time.time()
        res = prover.attempt_batch(d, [("synth", f"exact {term}")],
                                   timeout=120, single_timeout=120,
                                   max_retry_secs=0)
        lbl, ok, why = res[0]
        return {"goal": d.name, "ok": bool(ok), "why": why,
                "term_chars": len(term), "term": term,
                "secs": round(time.time() - t0, 1)}

    n = ok = 0
    with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
        for r in ex.map(check, built):
            n += 1
            ok += r["ok"]
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            print(f"{'VERIFIED' if r['ok'] else 'failed  '} {r['goal']:<28} "
                  f"{'' if r['ok'] else r['why'][:70]}", flush=True)
    print(f"\nkernel-checked {ok}/{n} with no Lean search", flush=True)


if __name__ == "__main__":
    main()
