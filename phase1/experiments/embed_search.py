"""Semantic premise retrieval: embeddings of library statements, fused with
Search's symbol-overlap ranking.

v7 showed the hard goals fail mainly for lack of the right lemma: with
Search's top 24 facts, all the lemmas a human proof cites were present for
7 of 257 goals. Search ranks by shared (IDF-weighted) symbols; an embedding
ranks by meaning, including the lemma's NAME (`SNo_recip_pos` says what it
is about). Fusing the two rankings recovers lemmas either one misses.

Leak discipline is Search's: only declarations strictly before the goal are
ever returned.

The embedding models are served by the same gateway as the LLMs
(LLM_BASE_URL/embeddings). Vectors are cached in results/emb_<model>.json.
"""
import json
import math
import os
import re
import urllib.request

from llm import _env, LeanContext

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
MODEL = "WhereIsAI/UAE-Large-V1"


def _text(name, ctx):
    """What gets embedded: the name as words, then the Lean statement with
    bound-variable noise removed."""
    stmt = ctx.text.get(name, "")
    stmt = re.sub(r"^(theorem|axiom|noncomputable def)\s+\S+\s*", "", stmt)
    stmt = re.sub(r"x\d+", "x", stmt)
    return name.replace("_", " ") + " : " + stmt[:1500]


def _embed(texts, model):
    env = _env()
    body = json.dumps({"model": model, "input": texts}).encode()
    req = urllib.request.Request(
        env["LLM_BASE_URL"].rstrip("/") + "/embeddings", data=body,
        headers={"Authorization": f"Bearer {env['LLM_API_KEY']}",
                 "Content-Type": "application/json"})
    data = json.load(urllib.request.urlopen(req, timeout=120))["data"]
    return [d["embedding"] for d in sorted(data, key=lambda d: d["index"])]


def _norm(v):
    n = math.sqrt(sum(x * x for x in v)) or 1.0
    return [x / n for x in v]


class EmbedSearch:
    def __init__(self, decls, model=MODEL, batch=64):
        self.decls, self.model = decls, model
        self.by_name = {d.name: d for d in decls}
        path = os.path.join(ROOT, "results", f"emb_{model.split('/')[-1]}.json")
        cache = json.load(open(path)) if os.path.exists(path) else {}
        ctx = LeanContext()
        todo = [d.name for d in decls if d.name not in cache and d.name in ctx.text]
        for i in range(0, len(todo), batch):
            chunk = todo[i:i + batch]
            for n, v in zip(chunk, _embed([_text(n, ctx) for n in chunk], model)):
                cache[n] = v
        if todo:
            json.dump(cache, open(path, "w"))
        self.vec = {n: _norm(v) for n, v in cache.items()}

    def rank(self, goal, limit=96, kinds=("THM", "AXIOM")):
        """Earlier declarations by cosine similarity to the goal."""
        q = self.vec.get(goal.name)
        if q is None:
            return []
        scored = []
        for d in self.decls[:goal.index]:
            if d.kind in kinds and d.name in self.vec:
                v = self.vec[d.name]
                scored.append((sum(a * b for a, b in zip(q, v)), d.name))
        scored.sort(reverse=True)
        return [n for _, n in scored[:limit]]


def fuse(*rankings, limit=96, k=60):
    """Reciprocal-rank fusion: a lemma ranked high by either list rises."""
    score = {}
    for r in rankings:
        for i, n in enumerate(r):
            score[n] = score.get(n, 0.0) + 1.0 / (k + i + 1)
    return [n for n, _ in sorted(score.items(), key=lambda kv: -kv[1])[:limit]]
