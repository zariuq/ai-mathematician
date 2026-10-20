"""Duper variants that give it FEWER, better premises -- and its own knobs.

`duper_tactics` in prover.py builds `have hp0 := ...` for every premise and
then calls `duper [*]`, i.e. everything in scope. That is the same mistake
the Vampire slices taught us to avoid: a superposition prover degrades on
irrelevant premises as badly as it does on missing ones, and `[*]` also drags
in the goal's own hypotheses after `intros`.

These variants name the facts explicitly, normalise the encoded connectives
first, and use Duper's own options (`portfolioInstance`, `preprocessing`),
which the installed build accepts.
"""
from itp import BRIDGE
from prover import _lean_name


def duper2_tactics(premises, defs, goal_defs=None):
    P = [_lean_name(p) for p in premises]
    allp = ", ".join(P)
    G = [_lean_name(d) for d in (goal_defs if goal_defs is not None else defs)]
    unfold = ", ".join([BRIDGE] + G) if G else BRIDGE
    if not P:
        return []
    out = [
        # the facts Vampire's proof used, named explicitly and nothing else
        ("d2-exact", f"intros\nduper [{allp}]"),
        ("d2-norm", f"intros\ntry simp only [{BRIDGE}] at *\nduper [{allp}]"),
        ("d2-unfold", f"intros\ntry simp only [{unfold}] at *\nduper [{allp}]"),
        # let Duper do the quantifiers itself rather than intro-ing first
        ("d2-raw", f"duper [{allp}]"),
        # Duper's own preprocessing, which does more definitional work
        ("d2-full", f"intros\ntry simp only [{BRIDGE}] at *\n"
                    f"duper [{allp}] {{preprocessing := full}}"),
        # a different portfolio strategy
        ("d2-p1", f"intros\ntry simp only [{BRIDGE}] at *\n"
                  f"duper [{allp}] {{portfolioInstance := 1}}"),
    ]
    # the first two facts alone: the minimal set is often enough and is
    # dramatically faster for a saturation prover
    if len(P) > 2:
        few = ", ".join(P[:2])
        out.append(("d2-few", f"intros\ntry simp only [{BRIDGE}] at *\nduper [{few}]"))
    return out
