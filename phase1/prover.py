"""Phase 1 prover: Search -> ATP (Vampire) -> ITP (Lean), no LLM required.

For one goal:
  1. Search ranks the facts available before the goal.
  2. Vampire tries to prove the goal from those facts; if it
     succeeds, the facts its proof used become the premise hint set.
  3. A deterministic battery of Lean tactic scripts is built from the hints
     and checked by Lean (trusted) with the statement-identity check and
     the leak guard. First script that passes wins.

An optional LLM (see llm.py, added later) plugs in between 2 and 3 as one
more source of candidate tactic scripts -- also checked by
Lean and the leak guard in exactly the same way.
"""
import os
import re
import subprocess
import tempfile
import time

from atp import THF, attach_prim_indices, run_vampire, Unsupported, ident
from itp import LEAN, LIB, BRIDGE, _GUARD, leak_free
from search import Search
from induction import Inductor, lean_script

# Duper (Lean-native superposition prover, like Isabelle's Metis), built in
# tools/duper-env for Lean v4.34.0; appended to LEAN_PATH when requested.
_DUPER_PKGS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                           "tools", "duper-env", ".lake", "packages")
DUPER_PATH = "".join(":" + os.path.join(_DUPER_PKGS, p, ".lake", "build", "lib", "lean")
                     for p in ("Duper", "auto", "batteries"))


def _lean_name(name):
    """Megalodon names are valid Lean identifiers except primes-only
    edge cases; wrap everything in «» to be safe."""
    return f"«{name}»"


def candidate_tactics(premises, defs, goal_defs=None):
    """Deterministic battery, cheapest first. Each entry: (label, script).

    The `goal-*` and `ext-*` strategies were distilled from the 51 proofs
    the LLM found for theorems this battery originally missed. They encode
    the three mechanical patterns those proofs kept using:
      * unfold the GOAL's own definitions -- only in the goal, not in the
        premises -- then introduce what that reveals (e.g. `Subq A B`
        unfolds to `forall z, In z A -> In z B`, so intro z and z ∈ A);
      * turn encoded or/and/ex from elimination lemmas native and let
        grind case-split on them;
      * prove set equality through extensionality (`set_ext`).
    Unfolding everything everywhere, as `prem-unfold-grind` does, rewrites
    the premises too, which is what broke these cases before."""
    P = [_lean_name(p) for p in premises]
    D = [_lean_name(d) for d in defs]
    G = [_lean_name(d) for d in (goal_defs if goal_defs is not None else defs)]
    haves = "".join(f"have hp{i} := @{p}\n" for i, p in enumerate(P))
    unfold = ", ".join([BRIDGE] + D) if D else BRIDGE
    goal_unfold = (f"try simp only [{', '.join(G)}]\ntry intros\n"
                   f"try simp only [{BRIDGE}] at *\n") if G else ""
    cands = [
        ("intro-grind", f"intros\ntry simp only [{BRIDGE}] at *\ngrind"),
        ("unfold-grind", f"intros\ntry simp only [{unfold}] at *\ngrind"),
    ]
    if P:
        cands += [
            ("prem-grind",
             f"intros\n{haves}try simp only [{BRIDGE}] at *\ngrind"),
            ("prem-unfold-grind",
             f"intros\n{haves}try simp only [{unfold}] at *\ngrind"),
            ("solve_by_elim",
             f"intros\nsolve_by_elim (maxDepth := 8) [{', '.join(P)}]"),
        ]
        if G:
            cands += [
                ("goal-unfold-grind",
                 f"intros\n{haves}try simp only [{BRIDGE}] at *\n{goal_unfold}grind"),
                ("goal-unfold-sbe",
                 f"intros\n{goal_unfold}solve_by_elim (maxDepth := 10) [{', '.join(P)}]"),
            ]
    # set equality by extensionality: eq set X Y  <-  Subq X Y, Subq Y X.
    # One line, each step parenthesised: a multi-line block inside `( )`
    # did not parse (column rules), so this strategy never ran before.
    cands.append(
        ("ext-grind",
         f"intros\n{haves}try simp only [{BRIDGE}] at *\n"
         f"refine (b_eq set _ _).mp (set_ext _ _ ?_ ?_)\n"
         f"all_goals ((try simp only [Subq]); intros; "
         f"(try simp only [{BRIDGE}] at *); grind)"))
    return cands


BIG = "(splits := 24) (ematch := 12) (gen := 12)"


def followup_tactics(premises, defs, goal_defs):
    """Second-line strategies, tried only when the battery fails (they are
    slower): premises as grind e-matching lemmas, more grind effort,
    simp_all with premises and definitions, and `all_goals grind` so a goal
    closed early by simp is not an error. Measured on the 90 v2 goals with a
    Vampire proof but no reconstruction: 6 rebuilt (try_rebuild.py)."""
    L = lambda n: f"«{n}»"  # noqa: E731
    P = [L(p) for p in premises]
    D = [L(d) for d in defs]
    G = [L(d) for d in goal_defs]
    haves = "".join(f"have hp{i} := @{p}\n" for i, p in enumerate(P))
    unfold = ", ".join([BRIDGE] + D)
    c = []
    if P:
        c += [
            # premises as e-matching theorems rather than hypotheses
            ("grind-lemmas", f"intros\n(try simp only [{BRIDGE}] at *)\ngrind [{', '.join(P)}]"),
            ("grind-lemmas-unfold",
             f"intros\n(try simp only [{unfold}] at *)\ngrind [{', '.join(P)}]"),
            # more search effort
            ("prem-grind-big", f"intros\n{haves}(try simp only [{BRIDGE}] at *)\nall_goals grind {BIG}"),
            ("prem-unfold-grind-big",
             f"intros\n{haves}(try simp only [{unfold}] at *)\nall_goals grind {BIG}"),
            # simplifier with everything
            ("simp_all-prem", f"intros\n{haves}simp_all [{unfold}]"),
            # the base battery's grind strategies, tolerant of the goal
            # already being closed by the simp step
            ("prem-grind-ag", f"intros\n{haves}(try simp only [{BRIDGE}] at *)\nall_goals grind"),
            ("prem-unfold-grind-ag", f"intros\n{haves}(try simp only [{unfold}] at *)\nall_goals grind"),
        ]
    c += [
        ("unfold-grind-big", f"intros\n(try simp only [{unfold}] at *)\nall_goals grind {BIG}"),
        ("unfold-grind-ag", f"intros\n(try simp only [{unfold}] at *)\nall_goals grind"),
    ]
    if G:
        gu = f"(try simp only [{', '.join(G)}])\n(try intros)\n(try simp only [{BRIDGE}] at *)\n"
        c.append(("goal-unfold-grind-big", f"intros\n{haves}(try simp only [{BRIDGE}] at *)\n{gu}all_goals grind {BIG}"))
    return c


def apply_tactics(premises, defs):
    """Third line: backward-chain one step with each premise, then grind the
    subgoals. `apply` lets Lean's unifier pick the premise's arguments from
    the goal, which grind cannot do for higher-order or impredicative
    premises, e.g. ReplE_impred (forall p : Prop, (... -> p) -> p): apply
    sets p := goal. The premises are first introduced as hypotheses and
    bridged to native logic, so they unify with the bridged goal."""
    P = [f"«{p}»" for p in premises]
    haves = "".join(f"have hp{i} := @{p}\n" for i, p in enumerate(P))
    unfold = ", ".join([BRIDGE] + [f"«{d}»" for d in defs])
    finish = "all_goals ((try intros); (try simp only [{u}] at *); grind)"
    out = []
    for i in range(len(P)):
        for tag, u in (("", BRIDGE), ("-unfold", unfold)):
            out.append((f"apply{tag}-{i}",
                        f"intros\n{haves}(try simp only [{BRIDGE}] at *)\n"
                        f"apply hp{i}\n" + finish.format(u=u)))
    return out

def apply2_tactics(premises, defs, limit=6):
    """Backward-chain one step, then give each subgoal the full battery
    rather than a single `grind`.

    `apply_tactics` applies a premise and then asks grind to finish every
    resulting subgoal in one shot -- the same single-leap assumption that
    the one-shot strategies make, moved up a level. The measured failures
    are proofs a human did in several steps, so the subgoals left by an
    `apply` are exactly where a second step is needed. Here each subgoal
    gets intros, bridging, grind, and failing that a bounded backward
    search over the whole premise set.

    Only the top `limit` premises are used for the outer apply: the ranked
    list is ordered, and applying a badly-matched premise produces
    subgoals that waste the whole candidate's budget."""
    P = [f"\u00ab{p}\u00bb" for p in premises]
    haves = "".join(f"have hp{i} := @{p}\n" for i, p in enumerate(P))
    unfold = ", ".join([BRIDGE] + [f"\u00ab{d}\u00bb" for d in defs])
    allp = ", ".join(P)
    out = []
    for i in range(min(limit, len(P))):
        for tag, u in (("", BRIDGE), ("-unfold", unfold)):
            finish = (f"all_goals ((try intros); (try simp only [{u}] at *); "
                      f"(first | grind | solve_by_elim (maxDepth := 10) [{allp}]))")
            out.append((f"apply2{tag}-{i}",
                        f"intros\n{haves}(try simp only [{BRIDGE}] at *)\n"
                        f"apply hp{i}\n{finish}"))
    return out


def duper_tactics(premises, defs):
    """Reconstruction with Duper (tools/duper-env), a proof-producing
    superposition prover inside Lean: the Sledgehammer recipe of re-proving
    with Metis from the facts the external ATP used. Unlike grind it does
    higher-order unification, the gap left by the other strategies. Needs
    attempt_batch(..., duper=True)."""
    P = [f"«{p}»" for p in premises]
    haves = "".join(f"have hp{i} := @{p}\n" for i, p in enumerate(P))
    unfold = ", ".join([BRIDGE] + [f"«{d}»" for d in defs])
    return [("duper", f"intros\n{haves}(try simp only [{BRIDGE}] at *)\nduper [*]"),
            ("duper-unfold", f"intros\n{haves}(try simp only [{unfold}] at *)\nduper [*]")]

class Prover:
    def __init__(self, decls, corpus_path, statements):
        self.decls = decls
        self.index_of = {d.name: d.index for d in decls}
        self.by_name = {d.name: d for d in decls}
        self.search = Search(decls)
        self.thf = THF(decls)
        attach_prim_indices(self.thf, corpus_path)
        self.sigs = statements
        self.inductor = Inductor(decls)
        self.use_duper = os.path.exists(DUPER_PATH.split(":")[1])
        # second ATP channel (smt_bridge.py): the same Vampire on a many-
        # sorted SMT-LIB encoding that unfolds only shallow predicate
        # definitions. Off by default, so the v4 numbers are unchanged.
        self.smt = None

    def enable_smt(self):
        from smt_bridge import SMT
        self.smt = SMT(self.decls, self.thf._prim_idx)

    def premise_sets(self, goal, slices=(16, 32, 64, 128, 256, 512), vampire_timeout=30):
        """Return (premise_sets, defs, vampire_status).

        Runs Vampire on several premise-slice sizes: the failure diagnosis
        showed Vampire often fails from too MANY irrelevant premises rather
        than missing ones, so small slices matter as much as large ones.
        Every slice is tried; each proof found contributes the set of facts
        it used. Without any proof, the one set is Search's top facts.

        v4: 256- and 512-fact slices added (15 and 7 further Vampire proofs
        on the goals v3 left without one; vampire256_*/vampire512.jsonl).
        v3 budget: 30 s per slice and a 128-fact slice. v2 used 5 s and
        16/32/64; on the 395 goals v2 found no Vampire proof for, this
        budget found 66 (vampire30_*.jsonl), most at 128 facts."""
        ranked = [n for n, _ in self.search.rank(goal.index, limit=max(slices),
                                                  goal_obj=goal)]
        facts = [n for n in ranked if self.by_name[n].kind in ("THM", "AXIOM")]
        goal_defs = sorted(s for s in goal.stmt_syms
                           if s in self.by_name and self.by_name[s].kind == "DEF"
                           and s not in ("True", "False", "not", "and", "or",
                                         "iff", "eq", "neq", "ex"))
        status, found = "skipped", []
        for k in slices:
            try:
                text, ids, _ = self.thf.problem(goal, ranked[:k])
            except Unsupported:
                status = "unsupported"
                break
            st, used = run_vampire(text, timeout=vampire_timeout)
            if st == "Theorem":
                vf = [ids[u] for u in used if u in ids]
                vdefs = {self._def_of(u) for u in used} - {None}
                found.append((k, vf, vdefs))
            elif not found:
                status = st
        if not found and self.smt is not None:
            # THF found nothing: the SMT channel proved induction step cases
            # THF timed out on (Pi_nat_p's step: THF timeout, SMT at 32 facts)
            from smt_bridge import run as run_smt
            for k in slices[:4]:
                try:
                    text, ids = self.smt.problem(goal, ranked[:k], None)
                except Unsupported:
                    break
                st, used, _ = run_smt(text, timeout=vampire_timeout,
                                      extra=("-updr", "off", "-nm", "0"))
                if st == "Theorem":
                    found.append((k, [ids[u] for u in used if u in ids], set()))
                    status = "smt"
                    break
        if found:
            # Vampire's proof is not unique: different slices can yield
            # different proofs, and the facts one uses may suit Lean's
            # tactics better than another's (6 regressions in a v2 run came
            # from exactly this). Keep every distinct premise set.
            sets, defs = [], set(goal_defs)
            for _, vf, vdefs in found:
                if vf not in sets:
                    sets.append(vf)
                defs |= vdefs
            # A proof from definitions alone (0-1 facts) is often one Lean's
            # tactics cannot replay by unfolding; give them Search's top
            # facts as well (nat_ordsucc, equip_sym).
            if all(len(s) < 2 for s in sets) and facts[:8] not in sets:
                sets.append(facts[:8])
            return sets, sorted(defs), "Theorem@" + ",".join(
                str(k) for k, _, _ in found)
        return [facts[:8]], goal_defs, status

    def hints(self, goal, **kw):
        """(premises, defs, status) with the first premise set only."""
        sets, defs, status = self.premise_sets(goal, **kw)
        return sets[0], defs, status

    def goal_defs(self, goal):
        """Definitions the goal statement itself mentions (not the logical
        connectives, which the bridge lemmas handle)."""
        return sorted(s for s in goal.stmt_syms
                      if s in self.by_name and self.by_name[s].kind == "DEF"
                      and s not in ("True", "False", "not", "and", "or",
                                    "iff", "eq", "neq", "ex"))

    def _def_of(self, vampire_id):
        if not vampire_id.endswith("_def"):
            return None
        for d in self.decls:
            if d.kind == "DEF" and ident(d.name) + "_def" == vampire_id:
                return d.name
        return None

    def attempt_batch(self, goal, cands, timeout=120, single_timeout=60,
                      max_retry_secs=480, heartbeats=200000, duper=False,
                      guard=None, prelude="", err_limit=1200):
        """Check every candidate for one goal in a single Lean process.
        Returns list of (label, ok, reason).

        `guard` overrides the statement-identity check. The default compares
        the attempt's type against the library declaration of the same name,
        which is what stops a proof of something subtly different counting.
        A caller proving a statement that is *not* a library declaration --
        an intermediate lemma lifted out of a proof -- has no such original
        to compare against and supplies its own; the sorryAx and leak checks
        are unaffected either way.

        `prelude` is Lean source placed before the attempts inside
        `namespace Megalodon` -- auxiliary lemmas the attempts cite, such as
        the lifted cases of an induction. The guard's dependency walk goes
        through local constants, so the prelude's own dependencies are leak-
        checked as if they were inlined."""
        sig = self.sigs[goal.name]
        parts = ["import Lean", "import Bridge"] + (["import Duper"] if duper else []) + [
                 "set_option Elab.async false",
                 "set_option maxRecDepth 8000",
                 f"set_option maxHeartbeats {heartbeats}",
                 "set_option linter.unusedVariables false"]
        if prelude:
            parts.append(f"namespace Megalodon\n{prelude.rstrip()}\nend Megalodon")
        att_names = []
        for i, (label, script) in enumerate(cands):
            att = f"attempt__{i}"
            att_names.append((att, label))
            body = "".join(f"  {ln}\n" for ln in script.strip().splitlines())
            parts.append(f"namespace Megalodon\ntheorem {att}{sig} := by\n"
                         f"{body}end Megalodon")
            parts.append((guard or _GUARD).replace("{att}", att)
                         .replace("{orig}", _lean_name(goal.name))
                         .replace("GUARD ", f"GUARD[{att}] "))
        src = "\n".join(parts) + "\n"
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                         dir="/tmp") as fh:
            fh.write(src)
            path = fh.name
        try:
            r = subprocess.run([LEAN, path], capture_output=True, text=True,
                               timeout=timeout,
                               env={**os.environ, "LEAN_PATH": LIB + (DUPER_PATH if duper else "")})
            out = r.stdout + r.stderr
        except subprocess.TimeoutExpired:
            os.unlink(path)
            # One slow candidate used up the whole batch's time, taking the
            # others down with it (43 of 140 baseline reconstruction failures
            # were exactly this). Retry each candidate alone, with its own
            # budget, so a fast proof is never killed by a slow neighbour.
            if len(cands) == 1:
                return [(cands[0][0], False, "timeout")]
            results = []
            deadline = time.time() + max_retry_secs
            for c in cands:
                if time.time() > deadline:
                    # bound the worst case: without this, 20 candidates x
                    # single_timeout could hold one goal for 20+ minutes
                    results += [(c2[0], False, "skipped: retry deadline")
                                for c2 in cands[len(results):]]
                    break
                r1 = self.attempt_batch(goal, [c], timeout=single_timeout,
                                        heartbeats=heartbeats, duper=duper,
                                        guard=guard, prelude=prelude)
                results += r1
                if r1[0][1]:
                    results += [(c2[0], False, "skipped: already proved")
                                for c2 in cands[len(results):]]
                    break
            return results
        else:
            os.unlink(path)

        # map error lines back to the attempt that contains them
        src_lines = src.splitlines()
        owner = {}
        cur = None
        for ln_no, ln in enumerate(src_lines, start=1):
            m = re.match(r"theorem (attempt__\d+)", ln)
            if m:
                cur = m.group(1)
            if ln.startswith("end Megalodon"):
                owner[ln_no] = cur
                cur = None
            elif cur:
                owner[ln_no] = cur
        # collect each attempt's error messages (message + continuation
        # lines), so an LLM can be shown exactly what Lean objected to
        errors = {}
        out_lines = out.splitlines()
        i = 0
        while i < len(out_lines):
            m = re.match(r".*?:(\d+):(\d+): error(?:\([^)]*\))?: ?(.*)", out_lines[i])
            if m:
                a = owner.get(int(m.group(1)))
                block = [m.group(3)]
                j = i + 1
                while j < len(out_lines) and not re.match(r".*?:\d+:\d+: ", out_lines[j]):
                    block.append(out_lines[j])
                    j += 1
                if a:
                    errors.setdefault(a, []).append("\n".join(block).strip())
                i = j
            else:
                i += 1

        results = []
        for att, label in att_names:
            if att in errors:
                results.append((label, False,
                                "lean error: " + "\n---\n".join(errors[att])[:err_limit]))
                continue
            m = re.search(rf"GUARD\[{att}\] samestmt (\w+)", out)
            if not m or m.group(1) != "true":
                results.append((label, False, "statement mismatch/missing"))
                continue
            m = re.search(rf"GUARD\[{att}\] used ?(.*)", out)
            used = m.group(1).split() if m else []
            if "sorryAx" in used:
                results.append((label, False, "sorryAx"))
                continue
            ok, leak = leak_free(used, goal.index, self.index_of)
            results.append((label, ok, "ok" if ok else f"leak {leak}"))
        return results

    # ---- induction (see induction.py) ------------------------------------

    def _vampire_case(self, case, ranked, slices, timeout=5):
        """Vampire on one induction case; the facts it used, or None."""
        for k in slices:
            try:
                text, ids, _ = self.thf.problem(case, ranked[:k])
            except Unsupported:
                return None
            status, used = run_vampire(text, timeout=timeout)
            if status == "Theorem":
                return [ids[u] for u in used if u in ids]
        return None

    def induction_split(self, goal, ranked=None, slices=(16, 32, 64)):
        """First (principle, variable) split whose every case Vampire
        proves from Search's facts. Returns a dict, or None."""
        if ranked is None:
            ranked = [n for n, _ in self.search.rank(goal.index, limit=max(slices),
                                                  goal_obj=goal)]
        for pname, xi, gi, cases in self.inductor.splits(goal):
            used = []
            for c in cases:
                u = self._vampire_case(c, ranked, slices)
                if u is None:
                    break
                used.append(u)
            if len(used) == len(cases):
                return {"principle": pname, "x": xi, "guard": gi,
                        "case_premises": used}
        return None

    def induction_lean(self, goal, split):
        """Lean proof from a split, in two passes. Lean's heartbeat budget
        is per declaration, so trying every tactic for every case inside
        ONE proof lets a slow failing attempt starve the rest. Pass 1 tries
        each (case, tactic) as its own declaration with the other cases
        left as `sorry`; an attempt whose only defect is sorryAx closed its
        case. Pass 2 assembles one winner per case into a single sorry-free
        proof, which gets the full check. Returns (ok, why, script)."""
        n, s = 0, goal.stmt
        while isinstance(s, list) and s[0] in ("ALL", "IMP"):
            n, s = n + 1, s[2]
        args = (split["x"], split["guard"], split["principle"])
        gdefs = self.goal_defs(goal)
        case_tacs = [[t for _, t in candidate_tactics(p, gdefs, gdefs)]
                     for p in split["case_premises"]]
        probes = []
        for k, tacs in enumerate(case_tacs):
            for i, t in enumerate(tacs):
                per_case = [["sorry"]] * len(case_tacs)
                per_case = per_case[:k] + [[t]] + per_case[k + 1:]
                probes.append((f"{k}:{i}", lean_script(n, *args, per_case)))
        res = self.attempt_batch(goal, probes, timeout=600, single_timeout=120)
        closes = {lbl for lbl, ok, why in res if ok or why == "sorryAx"}
        winners = []
        for k, tacs in enumerate(case_tacs):
            i = next((i for i in range(len(tacs)) if f"{k}:{i}" in closes), None)
            if i is None:
                return False, f"no tactic closes case {k}", None
            winners.append([tacs[i]])
        script = lean_script(n, *args, winners)
        (_, ok, why), = self.attempt_batch(goal, [("induction", script)],
                                           timeout=300, single_timeout=300)
        return ok, why, script

    def prove(self, goal, extra_candidates=(), induction=True, guard=None):
        sets, defs, vstatus = self.premise_sets(goal)
        premises = sets[0]
        cands = candidate_tactics(premises, defs, self.goal_defs(goal))
        # further premise sets: their premise-using strategies only, and
        # only if the first batch fails (a batch costs the sum of all its
        # candidates, so adding them up front slowed easy goals ~10x)
        second, third, fourth = [], [], []
        for j, alt in enumerate(sets[1:], start=2):
            second += [(f"{lbl}#{j}", s)
                       for lbl, s in candidate_tactics(alt, defs, self.goal_defs(goal))
                       if lbl.startswith(("prem-", "solve_by_elim", "goal-unfold"))]
        if vstatus.startswith("Theorem"):
            # second-line strategies over every premise set (followup_tactics)
            for j, ps in enumerate(sets, start=1):
                second += [(f"{lbl}#{j}", s) for lbl, s in
                           followup_tactics(ps, defs, self.goal_defs(goal))]
        if not vstatus.startswith("Theorem"):
            # Without a Vampire proof, premise-heavy grind attempts succeeded
            # 0/19 times on the sample while costing ~30s each; keep only
            # the cheap, fast-failing strategies.
            cands = [c for c in cands
                     if c[0] in ("intro-grind", "unfold-grind", "solve_by_elim",
                                 "goal-unfold-sbe", "ext-grind")]
        cands += list(extra_candidates)
        results = self.attempt_batch(goal, cands, guard=guard)
        winner = next((lbl for lbl, ok, _ in results if ok), None)
        if not winner and second:
            results += self.attempt_batch(goal, second, guard=guard, timeout=300,
                                          single_timeout=90, max_retry_secs=600)
            winner = next((lbl for lbl, ok, _ in results if ok), None)
        if not winner and vstatus.startswith("Theorem"):
            # third line: one backward step with each premise, then grind
            # (apply_tactics; 10 of the 115 v3 reconstruction failures)
            third = [(f"{lbl}#{j}", s) for j, ps in enumerate(sets, start=1)
                     for lbl, s in apply_tactics(ps, defs)]
            if third:
                results += self.attempt_batch(goal, third, guard=guard, timeout=300,
                                              single_timeout=60, max_retry_secs=600)
                winner = next((lbl for lbl, ok, _ in results if ok), None)
        if not winner and vstatus.startswith("Theorem") and self.use_duper:
            # last line: Duper (Metis-style reconstruction; 51 of the 109
            # goals every other line failed on, try_duper.jsonl)
            # each attempt in its own Lean process with its own time limit:
            # batched, a slow failing variant used up the time of the one
            # that would have succeeded (SepI: 106 s alone, lost in a batch)
            fourth = [(f"{lbl}#{j}", s) for j, ps in enumerate(sets[:2], start=1)
                      for lbl, s in duper_tactics(ps, defs)]
            t_duper = time.time()
            for cand in fourth:
                if time.time() - t_duper > 900:
                    results.append((cand[0], False, "skipped: duper time cap"))
                    continue
                results += self.attempt_batch(goal, [cand], guard=guard, timeout=300,
                                              single_timeout=300, max_retry_secs=0,
                                              heartbeats=1000000, duper=True)
                if results[-1][1]:
                    winner = results[-1][0]
                    break
        if winner:
            win_script = dict(cands + second + third + fourth).get(winner)
        out = {"goal": goal.name, "index": goal.index, "vampire": vstatus,
               "premises": premises, "premise_sets": sets, "defs": defs,
               "results": results, "proved_by": winner}
        if winner:
            out["script"] = win_script
        if winner or not induction or vstatus.startswith("Theorem"):
            return out
        # Vampire found no direct proof: try induction, which supplies the
        # predicate Vampire cannot invent.
        split = self.induction_split(goal)
        out["induction"] = split and split["principle"]
        if split:
            ok, why, script = self.induction_lean(goal, split)
            label = f"induction:{split['principle']}"
            out["results"].append((label, ok, why))
            if ok:
                out["proved_by"] = label
                out["script"] = script
        return out
