"""Phase 1 Search: given a goal, rank the facts available before it.

Deterministic, no LLM. Two signals, combined:

  1. Symbol overlap (in the spirit of Sledgehammer's MePo filter): a fact is
     relevant if it mentions the goal's constants, weighted by how rare each
     constant is -- sharing `SNoLev` says much more than sharing `and`.

  2. Learned from earlier proofs (in the spirit of MaSh k-NN): find earlier
     theorems whose statements resemble the goal, and vote for the facts
     THEIR proofs actually cited. Trained strictly on theorems before the
     goal, so the goal's own proof is never seen.

  3. Recency: 23% of the facts real proofs cite were proved within the 30
     declarations before the goal. In the agent setting this corresponds to
     "lemmas just proved" -- the Phase 2 working-memory idea -- so it is a
     legitimate signal, not an artifact of the benchmark.

Deliberately OFF by default: similarity to the goal's human-chosen NAME
(`name_w`). It adds ~2-3 points of recall here, but a genuinely new lemma
the system conjectures won't come with a descriptive human name, so using
it would inflate the benchmark relative to real use.

Leak discipline: `rank(goal_index, ...)` only ever considers declarations
with index < goal_index.
"""
import math
from collections import defaultdict

from library import LOGICAL


class Search:
    def __init__(self, decls):
        self.decls = decls
        # document frequency of each symbol across all statements, for IDF
        # weights. Using the whole corpus's statement vocabulary is fine: it
        # is statement-level, not proof-level, information.
        df = defaultdict(int)
        for d in decls:
            for s in d.stmt_syms:
                df[s] += 1
        n = len(decls)
        self.idf = {s: math.log((n + 1) / (c + 1)) + 1.0 for s, c in df.items()}
        for s in LOGICAL:
            if s in self.idf:
                self.idf[s] *= 0.2
        # name tokens (`add_SNo_minus_Lt1` -> add, SNo, minus, Lt1): 41% of
        # the facts real proofs cite share a token with the goal's name.
        # IDF-weighted so ubiquitous tokens (SNo, nat) carry little weight.
        tdf = defaultdict(int)
        for d in decls:
            for t in self._toks(d.name):
                tdf[t] += 1
        self.tidf = {t: math.log((n + 1) / (c + 1)) for t, c in tdf.items()}
        fdf = defaultdict(int)
        for d in decls:
            for f in d.feats:
                fdf[f] += 1
        self.fidf = {f: math.log((n + 1) / (c + 1)) for f, c in fdf.items()}

    @staticmethod
    def _toks(name):
        return {t for t in name.split("_") if t}

    def _name_sim(self, a, b):
        ta, tb = self._toks(a), self._toks(b)
        inter = sum(self.tidf.get(t, 0) for t in ta & tb)
        union = sum(self.tidf.get(t, 0) for t in ta | tb)
        return inter / union if union else 0.0

    def _w(self, sym):
        return self.idf.get(sym, 1.0)

    def _overlap(self, goal_syms, fact):
        """Weighted fraction of the fact's symbols that the goal shares.
        Favors facts that are 'about' the goal's concepts."""
        fs = fact.stmt_syms | {fact.name}
        if not fs:
            return 0.0
        shared = sum(self._w(s) for s in fs & goal_syms)
        total = sum(self._w(s) for s in fs)
        return shared / total if total else 0.0

    def _knn(self, goal_syms, goal_index, k=24):
        """Vote for premises cited by the proofs of the k earlier theorems
        whose statements are most similar to the goal (weighted Jaccard)."""
        sims = []
        for d in self.decls[:goal_index]:
            if d.kind != "THM":
                continue
            inter = sum(self._w(s) for s in goal_syms & d.stmt_syms)
            if inter == 0:
                continue
            union = sum(self._w(s) for s in goal_syms | d.stmt_syms)
            sims.append((inter / union, d))
        sims.sort(key=lambda t: -t[0])
        votes = defaultdict(float)
        for sim, d in sims[:k]:
            votes[d.name] += sim            # the similar theorem itself
            for p in d.proof_deps:
                votes[p] += sim             # and whatever its proof used
        return votes

    def _nb(self, goal, goal_index, sigma=10.0, penalty=-4.0, self_w=1.0):
        """Naive Bayes premise selection (Sledgehammer's MaSh): how likely is
        fact p to be used, given the goal's features, judging from which
        facts the proofs of EARLIER theorems used and what those theorems
        looked like. Each fact also counts as one example of itself (a
        fact is 'about' its own features).

          score(p) = ln t_p + sum_{f in goal} w_f * ( ln(sigma * s_pf / t_p)
                                                      if s_pf > 0 else penalty )
        where t_p = examples using p, s_pf = those with feature f."""
        t = defaultdict(float)
        s = defaultdict(lambda: defaultdict(float))
        for d in self.decls[:goal_index]:
            if d.kind in ("THM", "AXIOM"):
                t[d.name] += self_w
                for f in d.feats:
                    s[d.name][f] += self_w
            if d.kind == "THM":
                for p in d.proof_deps:
                    t[p] += 1
                    sp = s[p]
                    for f in d.feats:
                        sp[f] += 1
        F = [(f, self._fw(f)) for f in goal.feats]
        out = {}
        for p, tp in t.items():
            sp = s[p]
            sc = math.log(tp)
            for f, w in F:
                v = sp.get(f)
                sc += w * (math.log(sigma * v / tp) if v else penalty)
            out[p] = sc
        return out

    def _fw(self, f):
        return self.fidf.get(f, 1.0)

    def rank(self, goal_index, limit=32, name_w=0.0, recency_w=1.0,
             knn_w=1.5, nb_w=3.0, nb_decay=8.0, nb_args=None, goal_obj=None):
        """Return up to `limit` (name, score) pairs, best first, drawn only
        from declarations strictly before the goal.

        `goal_obj` lets a caller rank for a statement that is not itself a
        declaration -- an intermediate lemma lifted out of a proof, say --
        while still cutting the candidate pool at `goal_index`, so the leak
        discipline is unchanged. Omitted, it is the declaration at that
        index, which is the ordinary case."""
        goal = goal_obj if goal_obj is not None else self.decls[goal_index]
        goal_syms = set(goal.stmt_syms)
        # Definitions of the goal's own symbols are always relevant: a proof
        # usually has to unfold at least one of them.
        scores = defaultdict(float)
        for d in self.decls[:goal_index]:
            if d.kind == "DEF" and d.name in goal_syms:
                scores[d.name] += 2.0
            o = self._overlap(goal_syms, d)
            if o > 0:
                scores[d.name] += o
            if d.kind in ("THM", "AXIOM"):
                if name_w:
                    scores[d.name] += name_w * self._name_sim(goal.name, d.name)
                if recency_w:
                    gap = goal_index - d.index
                    scores[d.name] += recency_w / (1.0 + gap / 10.0)
        knn = self._knn(goal_syms, goal_index)
        top = max(knn.values(), default=0.0)
        if top > 0:
            for name, v in knn.items():
                scores[name] += knn_w * v / top
        if nb_w:
            # rank-based bonus: naive Bayes scores are log-odds on their own
            # scale, so blend by position rather than raw value
            nb = sorted(self._nb(goal, goal_index, **(nb_args or {})).items(),
                        key=lambda t: -t[1])
            for r, (name, _) in enumerate(nb):
                scores[name] += nb_w / (1.0 + r / nb_decay)
        allowed = {d.name for d in self.decls[:goal_index]}
        ranked = sorted(((n, s) for n, s in scores.items() if n in allowed),
                        key=lambda t: -t[1])
        return ranked[:limit]


    def diverse_slices(self, goal_index, k=24, nn=4):
        """Small premise sets from DIFFERENT signals, rather than prefixes of
        one blended ranking (as Sledgehammer runs its MePo and MaSh filters
        separately): a fact deep in the blend can be near the top of one
        signal. Only facts before the goal, as everywhere.
          nb   : top k by the naive Bayes score alone
          knn  : facts cited by the proofs of the nn most similar earlier
                 theorems (plus those theorems themselves)
          sym  : top k facts by IDF symbol overlap alone
        Returns {name: [fact, ...]}."""
        goal = self.decls[goal_index]
        allowed = {d.name for d in self.decls[:goal_index]
                   if d.kind in ("THM", "AXIOM")}
        nb = sorted(((n, v) for n, v in self._nb(goal, goal_index).items()
                     if n in allowed), key=lambda t: -t[1])
        out = {"nb": [n for n, _ in nb[:k]]}
        gs = set(goal.stmt_syms)
        sims = []
        for d in self.decls[:goal_index]:
            if d.kind != "THM":
                continue
            inter = sum(self._w(x) for x in gs & d.stmt_syms)
            if inter:
                union = sum(self._w(x) for x in gs | d.stmt_syms)
                sims.append((inter / union, d))
        sims.sort(key=lambda t: -t[0])
        knn = []
        for _, d in sims[:nn]:
            for p in [d.name] + sorted(d.proof_deps):
                if p in allowed and p not in knn:
                    knn.append(p)
        out["knn"] = knn[:2 * k]
        sym = sorted(((d.name, self._overlap(gs, d)) for d in self.decls[:goal_index]
                      if d.name in allowed), key=lambda t: -t[1])
        out["sym"] = [n for n, v in sym[:k] if v > 0]
        return out

def evaluate_recall(decls, ks=(8, 16, 32, 64)):
    """How often does Search surface the facts a real proof used?
    For every theorem with at least one cited fact, measure the fraction of
    its true cited facts that appear in Search's top-k."""
    s = Search(decls)
    per_k = {k: [] for k in ks}
    full = {k: 0 for k in ks}
    n = 0
    for d in decls:
        if d.kind != "THM" or not d.proof_deps:
            continue
        n += 1
        ranked = [name for name, _ in s.rank(d.index, limit=max(ks))]
        for k in ks:
            got = set(ranked[:k]) & d.proof_deps
            per_k[k].append(len(got) / len(d.proof_deps))
            if got == d.proof_deps:
                full[k] += 1
    print(f"theorems with cited facts: {n}")
    for k in ks:
        avg = sum(per_k[k]) / len(per_k[k])
        print(f"  top-{k:<3d} avg recall {avg:6.1%}   "
              f"all premises found: {full[k]:4d}/{n} ({full[k]/n:.1%})")


if __name__ == "__main__":
    import sys
    from library import load
    decls = load(sys.argv[1] if len(sys.argv) > 1 else "data/corpus.sexpr")
    evaluate_recall(decls)
