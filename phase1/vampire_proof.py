"""Parse Vampire's refutation into a proof DAG.

The pipeline currently runs Vampire with `--proof tptp`, which prints the
whole refutation, and then throws it away -- `run_vampire` keeps only the
names of the axioms it used, via a regex over `file(...)`. Lean is then asked
to re-derive from those axioms what Vampire already derived, which is where
the 1535 `grind` failures come from.

This module keeps the proof instead. Each line of the refutation is

    thf(ID, ROLE, FORMULA, inference(RULE, [status], [PARENTS])).
    thf(ID, axiom, FORMULA, file('problem.p', AXIOM_NAME)).
    thf(ID, definition, FORMULA, introduced(RULE, [...], [...])).

so the refutation is a DAG over small steps, each derived from one or two
parents. That is the shape a proof term wants: one `have` per step, justified
only from its parents, rather than one search from eight premises.
"""
import os
import re
import subprocess
import tempfile
from dataclasses import dataclass, field

from atp import VAMPIRE

# A record spans several lines and ends with ")."  -- the outer paren of
# `thf(...)`.  Splitting on lines that *start* a record is far safer than one
# regex over the whole block: formulas contain "))." freely, and a greedy or
# lazy match either swallows neighbouring records or eats the justification's
# own closing paren.
_START = re.compile(r"^(?:thf|tff|fof|cnf)\(")
# rule names are not all \w+: `beta-eta_normalization`,
# `iff_proxy_clausification_(simplifying)`
_INFERENCE = re.compile(r"inference\(\s*([^,\[]+?)\s*,\s*\[[^\]]*\]\s*,\s*\[([^\]]*)\]\s*\)\s*$", re.S)
_FILE = re.compile(r"file\(\s*'[^']*'\s*,\s*'?([^'\),]+)'?\s*\)\s*$", re.S)
_INTRO = re.compile(r"introduced\(\s*(\w+)\s*,", re.S)


@dataclass
class Step:
    id: str
    role: str          # axiom / negated_conjecture / plain / definition ...
    formula: str
    rule: str          # the inference rule, or "file" / "introduced"
    parents: list = field(default_factory=list)
    axiom: str = None  # for `file(...)` steps: the problem's name for it

    @property
    def is_input(self):
        return self.axiom is not None


def _records(body):
    cur = []
    for line in body.splitlines():
        if line.startswith("%"):
            continue
        if _START.match(line):
            if cur:
                yield "\n".join(cur)
            cur = [line]
        elif cur:
            cur.append(line)
    if cur:
        yield "\n".join(cur)


def parse_proof(out):
    """Steps of the refutation inside Vampire's SZS Proof block, in order."""
    m = re.search(r"SZS output start Proof.*?\n(.*?)% SZS output end Proof",
                  out, re.S)
    body = m.group(1) if m else out
    steps = []
    for rec in _records(body):
        t = rec.strip()
        if not t.endswith(")."):
            continue
        inner = t[t.index("(") + 1:-2]          # drop `thf(` and the final `).`
        parts = inner.split(",", 2)
        if len(parts) < 3:
            continue
        sid, role, rest = parts[0].strip(), parts[1].strip(), parts[2].strip()
        mi = _INFERENCE.search(rest)
        mf = _FILE.search(rest)
        mn = _INTRO.search(rest)
        if mi:
            parents = [x.strip() for x in mi.group(2).split(",") if x.strip()]
            steps.append(Step(sid, role, rest[:mi.start()].rstrip().rstrip(",").strip(),
                              mi.group(1), parents))
        elif mf:
            steps.append(Step(sid, role, rest[:mf.start()].rstrip().rstrip(",").strip(),
                              "file", [], mf.group(1)))
        elif mn:
            steps.append(Step(sid, role, rest[:mn.start()].rstrip().rstrip(",").strip(),
                              "introduced", []))
    return steps


def run_with_proof(problem_text, timeout=30, mode="portfolio"):
    """(status, steps, raw). Same Vampire invocation the prover already uses,
    but the refutation is parsed rather than discarded."""
    with tempfile.NamedTemporaryFile("w", suffix=".p", delete=False) as fh:
        fh.write(problem_text)
        path = fh.name
    try:
        out = subprocess.run(
            [VAMPIRE, "--mode", mode, "-t", str(timeout), "--proof", "tptp", path],
            capture_output=True, text=True, timeout=timeout + 20).stdout
    except subprocess.TimeoutExpired:
        return "Timeout", [], ""
    finally:
        os.unlink(path)
    m = re.search(r"SZS status (\w+)", out)
    status = m.group(1) if m else "Unknown"
    return status, (parse_proof(out) if status == "Theorem" else []), out


# ------------------------------------------------------ proof for the LLM
# The refutation, rewritten for a model that has to turn it into Lean:
# library names instead of `c_` identifiers, no type declarations or file
# paths, one line per step with its rule and parents.
_FORMAT_NOTE = """\
How to read it: Vampire proves by REFUTATION -- it assumes the negated goal
and derives $false. Each line is `id [rule parents]: formula`.
  [fact X]         a library fact you may use (by name X)
  [definition X]   the definition of X (unfold it)
  [goal]           the theorem being proved; [negated_conjecture] its negation
  `@` is application, `^[x:T]: b` is fun, `!` / `!!` is forall, `?` is exists,
  `$true` / `$false` are True / False, `=>` is ->, `|` is or, `&` is and.
  sK1, sK2, ... are Skolem functions; spl0_N are case-split labels (AVATAR).
  Pure bookkeeping steps (clause normal form, renaming, the SAT reasoning
  over spl0_N) are omitted; parents point to the nearest step shown.
Use it as a guide to the mathematical argument (which facts, instantiated
how, in what order), then write a DIRECT Lean proof -- not a refutation.
IMPORTANT: Vampire's `=`, `~`, `|`, `&`, `?` are NATIVE, but the library's
facts and the goal use the ENCODED Megalodon.eq / not / or / and / ex. So
instantiate facts with `have`, then bridge everything before rewriting:
  have h1 := add_nat_SR a b hb
  simp only [b_eq, b_and, b_or, b_not, b_ex, b_iff, b_True, b_False, b_neq] at *
  rw [h1]"""


def _names(prover):
    from atp import ident
    m = {}
    for d in prover.decls:
        m[ident(d.name)] = d.name
        m[ident(d.name) + "_def"] = d.name + "_def"
    return m


# Steps that only reshape a clause (normal forms, renaming, AVATAR/SAT
# bookkeeping) carry no mathematics; most of a refutation's length is these.
# They are dropped and their children re-pointed at the nearest kept steps.
_BOOKKEEPING = {
    "rectify", "flattening", "fool_elimination", "ennf_transformation",
    "nnf_transformation", "cnf_transformation", "duplicate_literal_removal",
    "trivial_inequality_removal", "beta-eta_normalization", "true_and_false_elimination",
    "pure_predicate_removal", "avatar_component_clause", "avatar_split_clause",
    "avatar_contradiction_clause", "sat_conversion", "rat", "avatar_sat_refutation",
}


def _collapse(steps):
    by_id = {s.id: s for s in steps}
    memo = {}

    def kept(sid):
        """Nearest ancestors of `sid` (itself included) that are not
        bookkeeping."""
        if sid not in memo:
            s = by_id.get(sid)
            if s is None or s.rule not in _BOOKKEEPING:
                memo[sid] = [sid]
            else:
                memo[sid] = list(dict.fromkeys(
                    a for p in s.parents for a in kept(p)))
        return memo[sid]

    out = []
    for s in steps:
        if s.rule in _BOOKKEEPING:
            continue
        parents = list(dict.fromkeys(a for p in s.parents for a in kept(p)))
        out.append(Step(s.id, s.role, s.formula, s.rule, parents, s.axiom))
    return out


def format_for_llm(steps, prover, max_chars=12000):
    names = _names(prover)
    ren = lambda s: re.sub(r"\bc_\w+", lambda m: names.get(m.group(), m.group()), s)
    lines = []
    for s in _collapse(steps):
        if s.is_input:
            if s.axiom == "goal":
                tag = "goal"
            elif s.axiom.endswith("_def") and s.axiom in names:
                tag = "definition " + names[s.axiom][:-4]
            else:
                tag = "fact " + names.get(s.axiom, s.axiom)
        elif s.rule == "introduced":
            tag = "introduced"
        else:
            tag = " ".join([s.rule] + s.parents)
        formula = re.sub(r"\s+", " ", ren(s.formula))
        lines.append(f"{s.id} [{tag}]: {formula}")
    text = "\n".join(lines)
    if len(text) > max_chars:
        # keep the inputs (head) and the closing argument (tail)
        head, tail = text[:max_chars // 3], text[-(2 * max_chars) // 3:]
        text = (head[:head.rfind("\n")] + "\n... (middle of proof omitted) ...\n"
                + tail[tail.find("\n") + 1:])
    return text


def proof_for_llm(prover, goal, slices=(16, 32, 64, 128, 256, 512), timeout=30):
    """First Vampire proof over growing premise slices (smaller slice ->
    smaller, more readable proof). Returns (text, facts, defs, k) or None.
    The problem holds only facts before the goal, so the proof cannot leak."""
    from atp import Unsupported
    ranked = [n for n, _ in prover.search.rank(goal.index, limit=max(slices))]
    for k in slices:
        try:
            text, ids, _ = prover.thf.problem(goal, ranked[:k])
        except Unsupported:
            return None
        status, steps, _ = run_with_proof(text, timeout=timeout)
        if status != "Theorem" or not steps:
            continue
        used = [s.axiom for s in steps if s.is_input]
        facts = [ids[u] for u in used if u in ids]
        defs = sorted({prover._def_of(u) for u in used} - {None})
        return _FORMAT_NOTE + "\n\n" + format_for_llm(steps, prover), facts, defs, k
    return None
