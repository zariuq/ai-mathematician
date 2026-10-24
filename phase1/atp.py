"""Phase 1 ATP bridge: goal + selected facts -> TPTP THF -> Vampire.

Vampire only proposes here, exactly like the LLM does. Its job
is to say "this goal follows from these particular facts". Only Lean's
kernel (itp.py) decides whether anything is actually proved. That lets the
translation below favour what helps Vampire search, rather than mirroring
Megalodon's encoding exactly:

  * Megalodon defines its logic inside the theory (Church-encoded `and`,
    `or`, `not`, `iff`, `ex`, Leibniz `eq`). These are mapped onto THF's
    native connectives, which Vampire's calculus handles natively. In
    classical HOL with extensionality -- which Megalodon assumes via
    prop_ext/func_ext -- the encodings and the natives are equivalent.
  * Other definitions become THF `definition`s, so Vampire can unfold them.
  * Polymorphic declarations other than the logical ones above are left
    out for now (rare in this corpus; reported, not hidden).
"""
import os
import re
import subprocess
import tempfile

VAMPIRE = os.path.join(os.path.dirname(__file__), "..", "tools", "vampire")

# Megalodon constant -> (arity, THF rendering of a full application)
_BIN = {"and": "&", "or": "|", "iff": "<=>"}


class Unsupported(Exception):
    pass


def ident(name):
    """TPTP functors must match [a-z][A-Za-z0-9_]*; Megalodon names can start
    upper-case or contain primes."""
    return "c_" + re.sub(r"[^A-Za-z0-9_]", lambda m: f"_{ord(m.group())}_", name)


class THF:
    def __init__(self, decls):
        self.decls = decls
        self.by_name = {d.name: d for d in decls}
        self.hash_to_name = {d.hash: d.name for d in decls}
        self._prim_idx = {}   # filled by attach_prim_indices()

    # -------------------------------------------------------------- types
    def tp(self, node, tvars):
        tag = node[0]
        if tag == "SET":
            return "set"
        if tag == "PROP":
            return "$o"
        if tag == "AR":
            return f"({self.tp(node[1], tvars)} > {self.tp(node[2], tvars)})"
        if tag == "TPVAR":
            i = int(node[1])
            if i >= len(tvars):
                raise Unsupported("free type variable")
            return tvars[-(i + 1)]
        raise Unsupported(f"type {tag}")

    # -------------------------------------------------------------- terms
    def tm(self, node, env, tvars, used):
        """Render a term. env is the De Bruijn stack of bound variable
        names; `used` collects every non-logical constant mentioned."""
        tag = node[0]
        if tag == "DB":
            return env[-(int(node[1]) + 1)]
        if tag == "LAM":
            v = f"X{len(env)}"
            ty = self.tp(node[1], tvars)
            body = self.tm(node[2], env + [v], tvars, used)
            return f"(^[{v}:{ty}]: {body})"
        if tag == "ALL":
            v = f"X{len(env)}"
            ty = self.tp(node[1], tvars)
            body = self.tm(node[2], env + [v], tvars, used)
            return f"(![{v}:{ty}]: {body})"
        if tag == "IMP":
            return (f"({self.tm(node[1], env, tvars, used)} => "
                    f"{self.tm(node[2], env, tvars, used)})")
        if tag == "AP":
            return self._app(node, env, tvars, used)
        if tag in ("TMH", "PRIM", "TPAP"):
            return self._head(node, env, tvars, used)
        raise Unsupported(f"term {tag}")

    def _name_of(self, node):
        if node[0] == "TMH":
            return self.hash_to_name.get(node[1])
        if node[0] == "PRIM":
            return self._prim_idx.get(int(node[1]))
        return None

    def _head(self, node, env, tvars, used):
        """A constant (possibly type-instantiated) in non-applied position."""
        tyargs = []
        while node[0] == "TPAP":
            tyargs.insert(0, self.tp(node[2], tvars))
            node = node[1]
        name = self._name_of(node)
        if name is None:
            raise Unsupported("unresolved constant")
        if name == "True":
            return "$true"
        if name == "False":
            return "$false"
        if name == "not":
            return "(^[A:$o]: ~A)"
        if name in _BIN:
            return f"(^[A:$o,B:$o]: (A {_BIN[name]} B))"
        if name in ("eq", "neq") and len(tyargs) == 1:
            op = "=" if name == "eq" else "!="
            return f"(^[A:{tyargs[0]},B:{tyargs[0]}]: (A {op} B))"
        if name == "ex" and len(tyargs) == 1:
            t = tyargs[0]
            return f"(^[P:({t} > $o)]: (?[Z:{t}]: (P @ Z)))"
        if tyargs:
            raise Unsupported(f"polymorphic constant {name}")
        used.add(name)
        return ident(name)

    def _app(self, node, env, tvars, used):
        # flatten the application spine
        args = []
        while node[0] == "AP":
            args.insert(0, node[2])
            node = node[1]
        head = node
        hname = None
        h = head
        tyargs = []
        while h[0] == "TPAP":
            tyargs.insert(0, h[2])
            h = h[1]
        if h[0] in ("TMH", "PRIM"):
            hname = self._name_of(h)
        rargs = [self.tm(a, env, tvars, used) for a in args]
        # native renderings of fully applied logical constants
        if hname == "not" and len(rargs) == 1:
            return f"(~ {rargs[0]})"
        if hname in _BIN and len(rargs) == 2:
            return f"({rargs[0]} {_BIN[hname]} {rargs[1]})"
        if hname in ("eq", "neq") and len(rargs) == 2 and len(tyargs) == 1:
            op = "=" if hname == "eq" else "!="
            return f"({rargs[0]} {op} {rargs[1]})"
        if hname == "ex" and len(rargs) == 1 and len(tyargs) == 1:
            t = self.tp(tyargs[0], tvars)
            return f"(?[Z{len(env)}:{t}]: ({rargs[0]} @ Z{len(env)}))"
        f = self.tm(head, env, tvars, used)
        return "(" + " @ ".join([f] + rargs) + ")"

    # ------------------------------------------------------------ problem
    def problem(self, goal, premises, max_def_depth=3):
        """Build a THF problem: conjecture = goal statement, axioms = the
        selected premise statements, plus type declarations and the
        definitions of every non-logical constant they mention (transitively,
        up to max_def_depth). Returns (tptp_text, premise_ids, skipped)."""
        lines, used, axioms, skipped = [], set(), [], []

        def stmt(d):
            u = set()
            s = self.tm(d.stmt, [], [], u)
            used.update(u)
            return s

        if goal.kind != "THM":
            raise Unsupported("goal is not a theorem")
        goal_txt = stmt(goal)  # raises Unsupported for polymorphic goals

        ids = {}
        for p in premises:
            d = self.by_name.get(p)
            if d is None or d.kind not in ("AXIOM", "THM"):
                continue
            try:
                ids[ident(d.name)] = d.name
                axioms.append(f"thf({ident(d.name)}, axiom, {stmt(d)}).")
            except Unsupported:
                skipped.append(d.name)
                ids.pop(ident(d.name), None)

        # definitions, followed transitively
        defs, frontier, depth = [], set(used), 0
        seen = set()
        while frontier and depth <= max_def_depth:
            nxt = set()
            for name in sorted(frontier):
                if name in seen:
                    continue
                seen.add(name)
                d = self.by_name.get(name)
                if d is None or d.kind != "DEF":
                    continue
                try:
                    u = set()
                    body = self.tm(d.body, [], [], u)
                    defs.append(f"thf({ident(name)}_def, definition, "
                                f"{ident(name)} = {body}).")
                    nxt |= u
                    used.update(u)
                except Unsupported:
                    skipped.append(name)
            frontier = nxt - seen
            depth += 1

        types = ["thf(set_type, type, set: $tType)."]
        for name in sorted(used):
            d = self.by_name.get(name)
            if d is None:
                continue
            try:
                if d.kind in ("PARAM", "PRIM", "DEF"):
                    types.append(f"thf({ident(name)}_type, type, "
                                 f"{ident(name)}: {self.tp(d.stmt, [])}).")
            except Unsupported:
                skipped.append(name)

        lines = types + defs + axioms + [f"thf(goal, conjecture, {goal_txt})."]
        return "\n".join(lines) + "\n", ids, skipped


def attach_prim_indices(thf, corpus_path):
    """library.load keeps PRIM names but not their numeric index; recover the
    index->name map from the raw export so PRIM references resolve."""
    from sexpr_translate import parse_toplevel_forms
    for f in parse_toplevel_forms(open(corpus_path, encoding="utf-8").read()):
        if f[0] == "PRIM":
            thf._prim_idx[int(f[1])] = f[2]


def run_vampire(problem_text, timeout=10):
    """Run Vampire on a THF problem. Returns (status, used_axiom_ids)."""
    with tempfile.NamedTemporaryFile("w", suffix=".p", delete=False) as fh:
        fh.write(problem_text)
        path = fh.name
    try:
        out = subprocess.run(
            [VAMPIRE, "--mode", "portfolio", "-t", str(timeout),
             "--proof", "tptp", path],
            capture_output=True, text=True, timeout=timeout + 15).stdout
    except subprocess.TimeoutExpired:
        return "Timeout", set()
    finally:
        os.unlink(path)
    m = re.search(r"SZS status (\w+)", out)
    status = m.group(1) if m else "Unknown"
    used = set(re.findall(r"file\('[^']*',\s*'?(c_\w+)'?\)", out))
    return status, used
