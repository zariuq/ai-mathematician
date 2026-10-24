"""Vampire's own induction on Megalodon goals, higher-order ones included.

Vampire has structural induction (-ind struct) but it fires only on
DATATYPES, which it accepts only in SMT-LIB. Megalodon is set theory: there
is one sort, and "natural number" is the predicate nat_p, not a type. So
on our THF problems the option is a silent no-op (measured: 0 induction
inferences, every configuration).

This module makes it fire, in two steps.

1. A bridge datatype.  Nat ::= zero | succ Nat, with an embedding e : Nat ->
   Set and the facts
       e zero = Empty,   e (succ n) = ordsucc (e n),   nat_p (e n),
       nat_p x -> exists n. x = e n.
   All four are true in the library once nat_ind is (the last one IS
   nat_ind, repackaged), and Vampire only proposes anyway: Lean
   re-checks the final proof against the real statement. The goal is
   rewritten so the chosen variable ranges over Nat directly:
       forall x. ... nat_p x -> phi(x)   ~>   forall n:Nat. ... phi(e n).
   Clausifying `nat_p x` into `x = e(sk)` instead does NOT work: Vampire
   orients the equation e(sk) -> x and the datatype term disappears before
   induction can see it.

2. A higher-order -> many-sorted first-order encoding (the Sledgehammer
   recipe), so the bridge reaches higher-order goals too, which SMT-LIB
   cannot state directly:
     * every function type a -> b becomes an uninterpreted sort Fn_a_b,
       applied through an explicit app_Fn_a_b;
     * a constant is a first-order function when fully applied, and a
       value c__v of its function sort (with the defining equation
       app(...app(c__v, x1)..., xn) = c(x1..xn)) when it is not;
     * every lambda is lifted to a fresh constant over the variables in
       scope, with its beta equation as an axiom;
     * quantifiers over predicates/functions quantify over those sorts.
   The encoding is incomplete (no comprehension beyond the lifted
   lambdas) but it need not be complete: it only has to let Vampire find
   WHICH variable to induct on and WHICH facts each case needs. Duper and
   Lean do the higher-order replay.

Only one variable is bridged per problem. With the others left as nat_p-
guarded sets there is nothing else of datatype sort, so a proof found means
"induction on THIS variable works, from these facts" -- exactly the choice
the inductor needs made for it.
"""
import os
import re
import subprocess
import tempfile

from atp import VAMPIRE, Unsupported, ident
from induction import to_named, to_db, subst

_BIN = {"and": "and", "or": "or", "iff": "="}


def _sort(tp):
    tag = tp[0]
    if tag == "SET":
        return "Set"
    if tag == "PROP":
        return "Bool"
    if tag == "NAT":
        return "Nat"
    if tag == "AR":
        return f"Fn_{_sort(tp[1])}_{_sort(tp[2])}"
    raise Unsupported(f"type {tag}")


def _arity(tp):
    args = []
    while tp[0] == "AR":
        args.append(tp[1])
        tp = tp[2]
    return args, tp


SET, PROP, NAT = ["SET"], ["PROP"], ["NAT"]


class SMT:
    def __init__(self, decls, prim_idx):
        self.by_name = {d.name: d for d in decls}
        self.hash_to_name = {d.hash: d.name for d in decls}
        self.prim_idx = prim_idx
        self.nat_p_hash = self.by_name["nat_p"].hash
        # nat_p's definition is its Church encoding; the bridge says what
        # Vampire needs to know about it
        self.no_unfold = {"nat_p"}

    # ---------------------------------------------------------------- state
    def _reset(self):
        self.sorts = set()       # Fn_* sort names
        self.apps = {}           # sort name -> (arg sort, result sort)
        self.consts = set()      # constant names used (non-logical)
        self.values = set()      # constants used as values (c__v)
        self.lams = {}           # body key -> (name, decl, axiom)

    def _use_sort(self, tp):
        if tp[0] == "AR":
            self._use_sort(tp[1])
            self._use_sort(tp[2])
            s = _sort(tp)
            self.sorts.add(s)
            self.apps[s] = (_sort(tp[1]), _sort(tp[2]))
        return _sort(tp)

    def _name_of(self, node):
        if node[0] == "TMH":
            return self.hash_to_name.get(node[1])
        if node[0] == "PRIM":
            return self.prim_idx.get(int(node[1]))
        return None

    def _ctype(self, name):
        d = self.by_name[name]
        if d.kind not in ("PARAM", "PRIM", "DEF"):
            raise Unsupported(f"constant kind {d.kind}")
        return d.stmt

    # ---------------------------------------------------------------- terms
    def tm(self, node, env):
        """Render `node` under env (list of (var name, Megalodon type,
        bridged?)), returning (smt text, Megalodon type of the result)."""
        tag = node[0]
        if tag == "DB":
            v, tp, bridged = env[-(int(node[1]) + 1)]
            return (f"(e {v})", SET) if bridged else (v, tp)
        if tag == "ALL":
            return self._forall(node, env), PROP
        if tag == "IMP":
            a, _ = self.tm(node[1], env)
            b, _ = self.tm(node[2], env)
            return f"(=> {a} {b})", PROP
        if tag == "LAM":
            return self._lift(node, env)
        if tag in ("AP", "TMH", "PRIM", "TPAP"):
            return self._app(node, env)
        raise Unsupported(f"term {tag}")

    def _forall(self, node, env, bridge_this=False):
        v = f"X{len(env)}"
        tp = node[1]
        s = "Nat" if bridge_this else self._use_sort(tp)
        body, _ = self.tm(node[2], env + [(v, tp, bridge_this)])
        return f"(forall (({v} {s})) {body})"

    def _lift(self, node, env):
        """Lambda-lift: lam_k(env vars) of sort Fn_a_b, with
        forall env, x. app(lam_k(env), x) = body."""
        tp = node[1]
        v = f"X{len(env)}"
        body, btp = self.tm(node[2], env + [(v, tp, False)])
        ftp = ["AR", tp, btp]
        fs = self._use_sort(ftp)
        params = [(n, "Nat" if br else _sort(t)) for n, t, br in env]
        key = (fs, tuple(params), body)
        if key not in self.lams:
            name = f"lam{len(self.lams)}"
            decl = f"(declare-fun {name} ({' '.join(s for _, s in params)}) {fs})"
            call = f"({name} {' '.join(n for n, _ in params)})" if params else name
            binders = " ".join(f"({n} {s})" for n, s in params + [(v, _sort(tp))])
            ax = (f"(assert (forall ({binders}) "
                  f"(= (app_{fs} {call} {v}) {body})))")
            self.lams[key] = (name, decl, ax)
        name = self.lams[key][0]
        return (f"({name} {' '.join(n for n, _ in params)})" if params else name), ftp

    def _apply(self, f, ftp, args):
        """Apply a function-sorted value through app_*."""
        for a, _ in args:
            if ftp[0] != "AR":
                raise Unsupported("over-application")
            s = self._use_sort(ftp)
            f, ftp = f"(app_{s} {f} {a})", ftp[2]
        return f, ftp

    def _app(self, node, env):
        args = []
        while node[0] == "AP":
            args.insert(0, node[2])
            node = node[1]
        tyargs = []
        while node[0] == "TPAP":
            tyargs.insert(0, node[2])
            node = node[1]
        rargs = [self.tm(a, env) for a in args]

        if node[0] not in ("TMH", "PRIM"):
            f, ftp = self.tm(node, env)
            return self._apply(f, ftp, rargs)
        name = self._name_of(node)
        if name is None:
            raise Unsupported("unresolved constant")

        # logical constants, natively
        if name == "True" and not rargs:
            return "true", PROP
        if name == "False" and not rargs:
            return "false", PROP
        if name == "not" and len(rargs) == 1:
            return f"(not {rargs[0][0]})", PROP
        if name in _BIN and len(rargs) == 2:
            return f"({_BIN[name]} {rargs[0][0]} {rargs[1][0]})", PROP
        if name in ("eq", "neq") and len(tyargs) == 1 and len(rargs) == 2:
            e = f"(= {rargs[0][0]} {rargs[1][0]})"
            return (e if name == "eq" else f"(not {e})"), PROP
        if name == "ex" and len(tyargs) == 1 and len(rargs) == 1:
            t = tyargs[0]
            if args[0][0] == "LAM":
                v = f"X{len(env)}"
                body, _ = self.tm(args[0][2], env + [(v, t, False)])
                return f"(exists (({v} {self._use_sort(t)})) {body})", PROP
            v = f"Z{len(env)}"
            ap, _ = self._apply(rargs[0][0], ["AR", t, PROP],
                                [(v, t)])
            return f"(exists (({v} {self._use_sort(t)})) {ap})", PROP
        if tyargs or name in ("True", "False", "not", "and", "or", "iff",
                              "eq", "neq", "ex"):
            raise Unsupported(f"polymorphic/partial logical constant {name}")

        ctp = self._ctype(name)
        params, res = _arity(ctp)
        self.consts.add(name)
        c = ident(name)
        if len(rargs) >= len(params):
            full = rargs[:len(params)]
            t = f"({c} {' '.join(a for a, _ in full)})" if full else c
            return self._apply(t, res, rargs[len(params):])
        self.values.add(name)
        return self._apply(f"{c}__v", ctp, rargs)

    # -------------------------------------------------------------- goal
    def _goal(self, stmt, bridge_pos):
        """Render the goal with the bridge_pos-th prefix binder over Nat and
        its nat_p guard dropped."""
        if bridge_pos is None:
            return self.tm(stmt, [])[0]
        # walk the prefix, rendering by hand so we can intervene
        return self._prefix(stmt, [], 0, bridge_pos, None)

    def _prefix(self, node, env, k, bpos, bvar_depth):
        if node[0] == "ALL":
            br = (k == bpos)
            if br and node[1] != SET:
                raise Unsupported("bridge variable is not a set")
            v = f"X{len(env)}"
            s = "Nat" if br else self._use_sort(node[1])
            body = self._prefix(node[2], env + [(v, node[1], br)], k + 1, bpos,
                                len(env) if br else bvar_depth)
            return f"(forall (({v} {s})) {body})"
        if node[0] == "IMP":
            hyp = node[1]
            if (bvar_depth is not None and hyp[0] == "AP"
                    and hyp[1] == ["TMH", self.nat_p_hash] and hyp[2][0] == "DB"
                    and len(env) - 1 - int(hyp[2][1]) == bvar_depth):
                # the bridged variable's own guard: nat_p (e n) holds
                return self._prefix(node[2], env, k + 1, bpos, bvar_depth)
            a, _ = self.tm(hyp, env)
            return f"(=> {a} {self._prefix(node[2], env, k + 1, bpos, bvar_depth)})"
        return self.tm(node, env)[0]

    # ----------------------------------------------------------- motive
    def _motive(self, goal, x_pos, g_pos):
        """The inductor's motive as a closed statement  forall x. P(x):
        the goal with x moved to the front, its guard dropped, and every
        other binder and hypothesis kept in order (induction.Inductor.splits
        builds the same P). Keeping them is what makes the induction
        hypothesis strong enough; Vampire on its own inducts on a single
        literal and loses them."""
        node, prefix = to_named(goal.stmt), []
        while isinstance(node, list) and node[0] in ("ALL", "IMP"):
            prefix.append(("ALL", node[1], node[3]) if node[0] == "ALL"
                          else ("IMP", node[1]))
            node = node[2]
        x = prefix[x_pos][2]
        out = node
        for j in reversed(range(len(prefix))):
            if j in (x_pos, g_pos):
                continue
            it = prefix[j]
            out = (["ALL", it[1], out, it[2]] if it[0] == "ALL"
                   else ["IMP", it[1], out])
        return to_db(["ALL", ["SET"], out, x])

    # ---------------------------------------------------------- problem
    def problem(self, goal, premises, bridge_pos, guard_pos=None, motive=False,
                max_def_depth=3):
        """SMT-LIB text for: premises + definitions + bridge |- goal with the
        bridge_pos-th binder ranging over Nat. With `motive`, the goal is
        restated as  forall n:Nat. M(n)  for a fresh predicate M defined as
        the inductor's motive, so Vampire's literal-level induction inducts
        on the whole motive. Returns (text, ids)."""
        self._reset()
        motive_ax = []
        if motive:
            body = self._motive(goal, bridge_pos, guard_pos)[2]
            btxt, _ = self.tm(body, [("X0", SET, True)])
            motive_ax = ["(declare-fun motive (Nat) Bool)",
                         f"(assert (forall ((X0 Nat)) (= (motive X0) {btxt})))"]
            goal_txt = "(forall ((X0 Nat)) (motive X0))"
        else:
            goal_txt = self._goal(goal.stmt, bridge_pos)
        axioms, ids = [], {}
        for p in premises:
            d = self.by_name.get(p)
            if d is None or d.kind not in ("AXIOM", "THM"):
                continue
            try:
                snap = (set(self.consts), set(self.values), dict(self.lams),
                        set(self.sorts), dict(self.apps))
                s = self.tm(d.stmt, [])[0]
            except Unsupported:
                (self.consts, self.values, self.lams,
                 self.sorts, self.apps) = snap
                continue
            ids[ident(d.name)] = d.name
            axioms.append(f"(assert (! {s} :named {ident(d.name)}))")

        defs, seen, frontier, depth = [], set(), set(self.consts), 0
        while frontier and depth <= max_def_depth:
            for name in sorted(frontier):
                seen.add(name)
                d = self.by_name.get(name)
                if d is None or d.kind != "DEF" or d.body is None:
                    continue
                snap = (set(self.consts), set(self.values), dict(self.lams),
                        set(self.sorts), dict(self.apps))
                try:
                    txt = self._definition(name, d)
                except Unsupported:
                    txt = None
                # Only shallow first-order PREDICATE definitions (Subq, nIn,
                # ...). Unfolding a set-valued one (ordsucc = binunion .., Pi_nat
                # = nat_primrec ..) rewrites every occurrence into recursion
                # internals the library lemmas are not stated over, and the
                # lambdas it drags in swamp the search: on Pi_nat_p's step case
                # Vampire times out with them and proves it in 5 s without.
                if (txt is None or name in self.no_unfold
                        or _arity(d.stmt)[1] != PROP or len(self.lams) > len(snap[2])
                        or len(self.values) > len(snap[1]) or "Fn_" in txt):
                    (self.consts, self.values, self.lams,
                     self.sorts, self.apps) = snap
                    continue
                defs.append(txt)
            frontier = self.consts - seen
            depth += 1

        bridge = [
            "(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))",
            "(declare-fun e (Nat) Set)",
            f"(assert (= (e zero) {ident('Empty')}))",
            f"(assert (forall ((n Nat)) (= (e (succ n)) ({ident('ordsucc')} (e n)))))",
            f"(assert (forall ((n Nat)) ({ident('nat_p')} (e n))))",
            f"(assert (forall ((x Set)) (=> ({ident('nat_p')} x) "
            f"(exists ((n Nat)) (= x (e n))))))",
        ]
        self.consts |= {"Empty", "ordsucc", "nat_p"}

        for name in sorted(self.consts):
            params, res = _arity(self._ctype(name))
            for t in params + [res]:
                self._use_sort(t)
        # constants may introduce function sorts of their own
        out = ["(set-logic ALL)", "(declare-sort Set 0)"]
        out += [f"(declare-sort {s} 0)" for s in sorted(self.sorts, key=len)]
        out += [f"(declare-fun app_{s} ({s} {a}) {b})"
                for s, (a, b) in sorted(self.apps.items(), key=lambda kv: len(kv[0]))]
        out += bridge[:2]
        for name in sorted(self.consts):
            ctp = self._ctype(name)
            params, res = _arity(ctp)
            out.append(f"(declare-fun {ident(name)} "
                       f"({' '.join(_sort(t) for t in params)}) {_sort(res)})")
            if name in self.values:
                out.append(f"(declare-fun {ident(name)}__v () {_sort(ctp)})")
                vs = [(f"Y{i}", t) for i, t in enumerate(params)]
                lhs, _ = self._apply(f"{ident(name)}__v", ctp, vs)
                rhs = f"({ident(name)} {' '.join(v for v, _ in vs)})"
                binders = " ".join(f"({v} {_sort(t)})" for v, t in vs)
                out.append(f"(assert (forall ({binders}) (= {lhs} {rhs})))")
        out += [d for _, d, _ in self.lams.values()]
        out += [a for _, _, a in self.lams.values()]
        out += bridge[2:] + motive_ax
        out += defs + axioms
        out.append(f"(assert (not {goal_txt}))")
        out.append("(check-sat)")
        return "\n".join(out) + "\n", ids

    def _definition(self, name, d):
        """forall xs. c(xs) = body xs: peel the body's lambdas, and apply
        whatever is left (an eta-reduced body) to the remaining variables."""
        params, _ = _arity(d.stmt)
        env, body = [], d.body
        while len(env) < len(params) and body[0] == "LAM":
            env.append((f"X{len(env)}", params[len(env)], False))
            body = body[2]
        rhs, rtp = self.tm(body, env)
        extra = [(f"X{k}", params[k]) for k in range(len(env), len(params))]
        rhs, _ = self._apply(rhs, rtp, extra)
        env += [(v, t, False) for v, t in extra]
        self.consts.add(name)
        if not env:
            return f"(assert (= {ident(name)} {rhs}))"
        lhs = f"({ident(name)} {' '.join(v for v, _, _ in env)})"
        binders = " ".join(f"({v} {_sort(t)})" for v, t, _ in env)
        return f"(assert (forall ({binders}) (= {lhs} {rhs})))"


def run(text, timeout=30, extra=("-ind", "struct")):
    """Vampire on an SMT-LIB problem with structural induction. Returns
    (status, used premise ids, number of induction formulas)."""
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as fh:
        fh.write(text)
        path = fh.name
    try:
        out = subprocess.run(
            [VAMPIRE, "--input_syntax", "smtlib2", "-t", str(timeout),
             *extra, "--proof", "tptp", path],
            capture_output=True, text=True, timeout=timeout + 15).stdout
    except subprocess.TimeoutExpired:
        return "Timeout", set(), 0
    finally:
        os.unlink(path)
    if "Refutation found" in out or "SZS status Unsatisfiable" in out:
        status = "Theorem"
    elif "User error" in out or "Parsing error" in out.lower():
        status = "Error: " + next((l for l in out.splitlines()
                                   if "rror" in l), "")[:200]
    else:
        status = "Unknown"
    used = set(re.findall(r"file\('[^']*',\s*'?(c_\w+)'?\)", out))
    n_ind = len(re.findall(r"structural[ _]induction", out))
    return status, used, n_ind
