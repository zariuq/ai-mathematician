"""How much term synthesis do the proofs we miss actually need?

The incremental search explores tactic *scripts*. It can apply a lemma, but
it cannot invent the term to apply it at. In Megalodon a proof instantiates a
universal with `(PTMAP d m)`, and `m` is a term the human wrote. If the terms
the missed proofs need cannot be read off the goal, no amount of tactic-level
search will find them, and the search result is explained rather than merely
disappointing.

Each PTMAP argument is classified as
  atomic     a variable or a named constant -- `intro`/unification territory
  in-goal    a compound term that already occurs in the statement
  synthesized a compound term that does not -- the human built it

Usage: python3 witness_audit.py <run.jsonl>
"""
import json
import sys
from collections import Counter

from library import load

CORPUS = "../data/corpus.sexpr"
_ATOMIC = {"DB", "TPVAR", "TMH", "PRIM", "HYP", "KNOWN", "PROP", "SET"}


def _key(node):
    """Canonical string for a term, so subterms can be compared."""
    if isinstance(node, str):
        return node
    return "(" + " ".join(_key(c) for c in node) + ")"


def _subterms(node, out):
    if isinstance(node, str) or not node:
        return
    out.add(_key(node))
    for c in node:
        if not isinstance(c, str):
            _subterms(c, out)


def _ptmap_args(node, out):
    if isinstance(node, str) or not node:
        return
    if node[0] == "PTMAP" and len(node) >= 3:
        out.append(node[2])
    for c in node:
        if not isinstance(c, str):
            _ptmap_args(c, out)


def _size(node):
    if isinstance(node, str):
        return 1
    return 1 + sum(_size(c) for c in node)


def classify(goal):
    """Counter over the three classes for one declaration's own proof."""
    c = Counter()
    if goal.body is None:
        return c, 0, 0
    args = []
    _ptmap_args(goal.body, args)
    goal_sub = set()
    _subterms(goal.stmt, goal_sub)
    for m in args:
        tag = m[0] if not isinstance(m, str) else m
        if tag in _ATOMIC and (isinstance(m, str) or len(m) <= 2):
            c["atomic"] += 1
        elif _key(m) in goal_sub:
            c["in-goal"] += 1
        else:
            c["synthesized"] += 1
    big = max((_size(m) for m in args), default=0)
    return c, big, _size(goal.body)


def main():
    rows = [json.loads(l) for l in open(sys.argv[1])]
    decls = load(CORPUS)
    by_name = {d.name: d for d in decls}
    groups = {"proved": [], "failed": []}
    for r in rows:
        g = by_name.get(r["goal"])
        if g is None:
            continue
        key = "proved" if (r.get("proved") or r.get("proved_by")) else "failed"
        groups[key].append(classify(g))

    for key, rs in groups.items():
        if not rs:
            continue
        tot = Counter()
        for c, _, _ in rs:
            tot += c
        n = len(rs)
        any_syn = sum(1 for c, _, _ in rs if c["synthesized"])
        biggest = sorted((b for _, b, _ in rs), reverse=True)
        # failed theorems have longer proofs, so a raw count of
        # instantiations would say little more than that; the rate per
        # proof node, and the size of the largest term, do not depend on
        # how long the proof is
        nodes = sum(n for _, _, n in rs)
        rates = sorted(sum(c.values()) / max(1, n) for c, _, n in rs)
        syn_rate = sorted(c["synthesized"] / max(1, n) for c, _, n in rs)
        print(f"\n=== {key}: {n} theorems ===")
        print(f"  instantiations per theorem: "
              f"{sum(tot.values()) / n:.1f}")
        for cls in ("atomic", "in-goal", "synthesized"):
            print(f"    {cls:<12} {tot[cls]:>6}  "
                  f"({100 * tot[cls] / max(1, sum(tot.values())):.0f}%)")
        print(f"  theorems needing >=1 synthesized term: "
              f"{any_syn}/{n} ({100 * any_syn / n:.0f}%)")
        print(f"  median largest instantiated term (nodes): "
              f"{biggest[len(biggest) // 2] if biggest else 0}")
        print(f"  median proof size (nodes): "
              f"{sorted(n for _, _, n in rs)[len(rs) // 2]}")
        print(f"  instantiations per 100 proof nodes (median): "
              f"{100 * rates[len(rates) // 2]:.1f}")
        print(f"  synthesized per 100 proof nodes (median): "
              f"{100 * syn_rate[len(syn_rate) // 2]:.1f}")


if __name__ == "__main__":
    main()
