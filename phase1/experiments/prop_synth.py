"""Synthesise Megalodon proof terms for the propositional fragment, then let
the existing translator turn them into Lean terms that Lean only type-checks.

This is the "build, don't search" path, end to end and without Vampire:

    statement (s-expr)  ->  our synthesiser  ->  Megalodon proof term (s-expr)
                        ->  sexpr_translate.pf_to_lean  ->  Lean term
                        ->  Lean kernel type-checks it

No `grind`, no tactic search, no premise selection. Lean is handed a finished
term and does the one thing it cannot fail at ambiguously: check it.

Why the propositional fragment works. Megalodon encodes the connectives
impredicatively -- `and A B` is `forall p, (A -> B -> p) -> p`, `False` is
`forall p, p`, `not A` is `A -> False` -- so once definitions are unfolded,
every one of these theorems is a statement in implication and universal
quantification over Prop alone, and proving it is lambda-term synthesis. The
one heuristic that makes it tractable is the standard trick for impredicative
encodings: when a hypothesis begins `forall p, ...`, instantiate `p` with the
goal being proved.
"""
import sys

# ------------------------------------------------------------------ terms
def shift(node, d, cutoff=0):
    """Raise DB indices >= cutoff by d."""
    if isinstance(node, str):
        return node
    tag = node[0]
    if tag == "DB":
        i = int(node[1])
        return ["DB", str(i + d)] if i >= cutoff else node
    if tag in ("ALL", "LAM"):
        return [tag, node[1], shift(node[2], d, cutoff + 1)]
    return [tag] + [shift(c, d, cutoff) for c in node[1:]]


def subst(node, j, repl):
    """node[DB j := repl]."""
    if isinstance(node, str):
        return node
    tag = node[0]
    if tag == "DB":
        i = int(node[1])
        if i == j:
            return shift(repl, j)
        return ["DB", str(i - 1)] if i > j else node
    if tag in ("ALL", "LAM"):
        return [tag, node[1], subst(node[2], j + 1, repl)]
    return [tag] + [subst(c, j, repl) for c in node[1:]]


class Unfolder:
    def __init__(self, decls):
        self.by_hash = {d.hash: d for d in decls if d.hash}

    def whnf(self, node):
        """Unfold definitions and beta-reduce at the head, enough to expose
        whether the formula is an ALL, an IMP, or atomic."""
        for _ in range(200):
            if isinstance(node, str) or not node:
                return node
            tag = node[0]
            if tag == "TMH":
                d = self.by_hash.get(node[1])
                if d is not None and d.kind == "DEF" and d.body is not None:
                    node = d.body
                    continue
                return node
            if tag == "AP":
                f = self.whnf(node[1])
                if not isinstance(f, str) and f and f[0] == "LAM":
                    node = subst(f[2], 0, node[2])
                    continue
                return ["AP", f] + node[2:]
            return node
        return node


def eq(a, b):
    """Structural equality of two s-expressions."""
    if isinstance(a, str) or isinstance(b, str):
        return a == b
    return len(a) == len(b) and all(eq(x, y) for x, y in zip(a, b))


# --------------------------------------------------------------- synthesis
class Synth:
    def __init__(self, decls, max_depth=10):
        self.u = Unfolder(decls)
        self.max_depth = max_depth

    def prove(self, goal, hyps=(), depth=0):
        """A proof s-expr for `goal` under `hyps` (index 0 = innermost PLAM),
        or None. `hyps` holds the hypothesis *types* in the current DB scope."""
        if depth > self.max_depth:
            return None
        g = self.u.whnf(goal)
        tag = g[0] if not isinstance(g, str) else g

        if tag == "ALL":                      # forall-introduction
            inner = self.prove(g[2], tuple(shift(h, 1) for h in hyps), depth + 1)
            return ["TLAM", g[1], inner] if inner else None

        if tag == "IMP":                      # implication-introduction
            inner = self.prove(g[2], (g[1],) + tuple(hyps), depth + 1)
            return ["PLAM", g[1], inner] if inner else None

        # atomic goal: find a hypothesis whose spine ends in it
        for i, h in enumerate(hyps):
            pf = self._use(h, ["HYP", str(i)], g, hyps, depth)
            if pf is not None:
                return pf
        return None

    def _use(self, ty, pf, goal, hyps, depth, fuel=6):
        """Eliminate `ty` (proved by `pf`) down to `goal`, collecting the
        subgoals its implications demand."""
        pending = []
        cur = ty
        for _ in range(fuel):
            cur = self.u.whnf(cur)
            if eq(cur, goal):
                break
            t = cur[0] if not isinstance(cur, str) else cur
            if t == "ALL":
                # the impredicative trick: instantiate the quantifier with
                # the goal. `and A B` used to prove G becomes
                # `(A -> B -> G) -> G`, which is exactly what we want.
                pf = ["PTMAP", pf, goal]
                cur = subst(cur[2], 0, goal)
                continue
            if t == "IMP":
                pending.append(cur[1])
                pf = ["PPFAP", pf, None]      # filled in below
                cur = cur[2]
                continue
            return None
        else:
            return None
        if not eq(self.u.whnf(cur), self.u.whnf(goal)):
            return None
        # discharge the collected subgoals, innermost application first
        spine = []
        node = pf
        while not isinstance(node, str) and node[0] in ("PPFAP", "PTMAP"):
            spine.append(node)
            node = node[1]
        spine.reverse()
        args = [n for n in spine if n[0] == "PPFAP"]
        if len(args) != len(pending):
            return None
        for n, sub in zip(args, pending):
            sp = self.prove(sub, hyps, depth + 1)
            if sp is None:
                return None
            n[2] = sp
        return pf
