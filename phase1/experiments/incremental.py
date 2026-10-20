"""Incremental prover: best-first search over partial Lean proof scripts.

The one-shot prover ranks premises once, against the theorem statement, and
hands Lean a finished script. Four measurements in results/ say that is the
binding constraint, not retrieval: on the goals v4 failed, premise recall is
100% at top-512, yet the facts the human proof cites sit at median rank 116
-- because the human cites them against an *intermediate* state (after the
intros, the unfolding, the case split) whose symbols are not the statement's
symbols. 64% of those proofs have `have` steps; 5% of the successes do.

So search instead of guessing once. A node is a partial script. Lean reports
the live goal state at that node (`probe_state`, below). The premises for the
next step are ranked against *that state*. One `have` of a well-chosen fact
rewrites the state's symbols, which rewrites the next ranking -- which is how
a human have-chain actually makes progress.

This is not the earlier chain attempt. That one lifted the human's `have`
steps out of the proof, stated them as closed lemmas and asked grind to
reassemble them; it failed because 93% of those steps live inside an
application or a case analysis and cannot be stated out of context. Here
nothing is lifted: every step is taken inside the real proof state, so the
context is whatever Lean says it is.

Every proof found is re-checked by `Prover.attempt_batch` under the ordinary
guard -- type identical to the library declaration, no sorryAx, no leak -- so
a win here is a win at the same bar as the 640.
"""
import heapq
import os
import re
import subprocess
import tempfile
import time

from library import Decl
from itp import LEAN, LIB, BRIDGE
from prover import _lean_name, candidate_tactics, apply2_tactics

# Lean orders a declaration's messages by source position, and a logged
# message's content carries no position of its own, so with twenty probes in
# one file there is no reliable way to tell whose state is whose. Each blob
# therefore names its own probe and closes itself.
PROBE_ELAB = r'''
open Lean Elab Tactic Meta in
elab "probe_state " n:str : tactic => do
  let gs ← getGoals
  let mut s : String := ""
  for g in gs do
    s := s ++ "\n<<GOAL>>\n" ++ (← ppGoal g).pretty
  logInfo m!"@@STATE {n.getString} {gs.length}{s}
@@END {n.getString}"
'''

_STATE_RE = re.compile(r"@@STATE (\S+) (\d+)\n?(.*?)\n@@END \1", re.S)
_IDENT_RE = re.compile(r"«([^»]+)»|([A-Za-z_][A-Za-z0-9_']*)")

# Connectives the bridge lemmas already handle; unfolding them by hand just
# makes the state bigger without making it more tractable.
_LOGICAL = {"True", "False", "not", "and", "or", "iff", "eq", "neq", "ex"}


def state_syms(text, by_name):
    """Megalodon constants mentioned in a pretty-printed goal state.

    Lean prints inaccessible names with a dagger (`x1250✝`); those are
    binders, never library constants, so stripping it costs nothing and
    keeps `«name»`-quoted constants matchable."""
    out = set()
    for m in _IDENT_RE.finditer(text.replace("✝", "")):
        n = m.group(1) or m.group(2)
        if n in by_name:
            out.add(n)
    return out


def probe_batch(prover, goal, cands, timeout=240, heartbeats=100000):
    """Elaborate many partial scripts for one goal in a single Lean process.

    Returns {label: (status, payload)} where status is
      "closed" -- the script left no goals (a candidate proof; payload [])
      "open"   -- payload is the list of pretty-printed remaining goals
      "error"  -- payload is Lean's complaint
    A script that errors is pruned: Lean has already refused it, and no
    extension of a refused prefix can be a proof."""
    sig = prover.sigs[goal.name]
    parts = ["import Lean", "import Bridge",
             "set_option Elab.async false",
             "set_option maxRecDepth 8000",
             f"set_option maxHeartbeats {heartbeats}",
             "set_option linter.unusedVariables false",
             PROBE_ELAB]
    labels = []
    for i, (label, script) in enumerate(cands):
        labels.append((f"probe__{i}", label))
        body = "".join(f"  {ln}\n" for ln in script.strip().splitlines())
        parts.append(f"namespace Megalodon\ntheorem probe__{i}{sig} := by\n"
                     f'{body}  probe_state "{i}"\n  all_goals sorry\n'
                     f"end Megalodon")
    src = "\n".join(parts) + "\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     dir="/tmp") as fh:
        fh.write(src)
        path = fh.name
    try:
        r = subprocess.run([LEAN, path], capture_output=True, text=True,
                           timeout=timeout,
                           env={**os.environ, "LEAN_PATH": LIB})
        out = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        os.unlink(path)
        return {label: ("error", "batch timeout") for _, label in labels}
    os.unlink(path)

    # errors carry a line number, so attribute them the way attempt_batch
    # does: walk the source and remember which declaration owns each line
    owner = {}
    cur = None
    for ln_no, ln in enumerate(src.splitlines(), start=1):
        m = re.match(r"theorem (probe__\d+)", ln)
        if m:
            cur = m.group(1)
        if ln.startswith("end Megalodon"):
            owner[ln_no] = cur
            cur = None
        elif cur:
            owner[ln_no] = cur
    errors = {}
    for m in re.finditer(r"^.*?:(\d+):\d+: error(?:\([^)]*\))?: ?(.*)$",
                         out, re.M):
        a = owner.get(int(m.group(1)))
        if a:
            errors.setdefault(a, []).append(m.group(2))

    states = {}
    for m in _STATE_RE.finditer(out):
        n, count, blob = m.group(1), int(m.group(2)), m.group(3)
        gs = [g.strip() for g in blob.split("<<GOAL>>") if g.strip()]
        states[f"probe__{n}"] = (count, gs)

    res = {}
    for att, label in labels:
        if att in errors:
            res[label] = ("error", "; ".join(errors[att])[:400])
        elif att in states:
            count, gs = states[att]
            res[label] = ("closed", []) if count == 0 else ("open", gs)
        else:
            # no state and no error: the declaration never reached the probe
            # (elaboration gave up elsewhere, or the batch was cut short)
            res[label] = ("error", "no probe state")
    return res


def steps(prover, goal, state, have_n, used, k=6, defs=(), seed=()):
    """Candidate next steps for one live goal state, cheapest first.

    Premises are ranked against the state, not the theorem: that is the
    whole point. `used` are facts already introduced on this branch, so a
    branch cannot keep rediscovering its own last step.

    `seed` are the facts Vampire's own proof used, when it found one. They
    go first: an ATP proof that cites a fact is far stronger evidence than
    any ranking score, and without them this search would throw away the
    premise selection that got the one-shot prover its 640."""
    syms = state_syms(state, prover.by_name)
    # rank for a statement that is not a declaration; goal.index still cuts
    # the candidate pool, so the leak discipline is untouched
    synth = Decl(index=goal.index, kind="THM", name=goal.name, hash="",
                 stmt=None, stmt_syms=syms, feats=goal.feats)
    ranked = prover.search.rank(goal.index, limit=60, goal_obj=synth)
    pool = [n for n in seed if n not in used]
    pool += [n for n, _ in ranked
             if prover.by_name[n].kind in ("THM", "AXIOM")
             and n not in used and n not in pool]
    facts = pool[:k]
    live = [n for n in sorted(syms)
            if prover.by_name[n].kind == "DEF" and n not in _LOGICAL]
    unfold = ", ".join([BRIDGE] + [_lean_name(d) for d in (live or defs)])
    allp = ", ".join(_lean_name(f) for f in facts) or "True.intro"

    out = []
    # The one-shot battery's moves, as single steps. Without these the
    # search has to rediscover `have` every premise one level at a time,
    # which costs a level of depth per premise and is why the first run
    # closed nothing: the proof it was looking for needed three facts in
    # context at once, and depth two is as far as the budget reached.
    if facts:
        bulk = "".join(f"have hq{have_n + i} := @{_lean_name(f)}\n"
                       for i, f in enumerate(facts))
        out.append(("have-all", bulk.rstrip()))
        out.append(("have-all-grind",
                    f"{bulk}simp only [{BRIDGE}] at *\ngrind"))
        sweep = (f"all_goals ((try intros); (try simp only [{BRIDGE}] at *); "
                 f"(first | grind | solve_by_elim (maxDepth := 10) [{allp}]))")
        for i, f in enumerate(facts[:4]):
            out.append((f"apply-sweep-{f}",
                        f"{bulk}apply hq{have_n + i}\n{sweep}"))

    # closers: try to finish here. `simp only [...] at *` first, because the
    # statements come out of Megalodon with and/or/ex encoded.
    out.append(("grind", "grind"))
    out.append(("norm-grind", f"simp only [{BRIDGE}] at *\ngrind"))
    # a tactic acts on the main goal only, so a branch that split earlier
    # needs an explicit sweep to finish the siblings off
    out.append(("all-grind", "all_goals grind"))
    out.append(("all-norm-grind",
                f"all_goals (simp only [{BRIDGE}] at * <;> grind)"))
    if facts:
        out.append(("grind-prem",
                    f"simp only [{BRIDGE}] at *\ngrind [{allp}]"))
        out.append(("sbe-prem",
                    f"simp only [{BRIDGE}] at *\n"
                    f"solve_by_elim (maxDepth := 8) [{allp}]"))
    if live:
        out.append(("unfold-grind", f"simp only [{unfold}] at *\ngrind"))

    # expanders: make the state different, so the next ranking is different
    out.append(("intros", "intros"))
    out.append(("norm", f"simp only [{BRIDGE}] at *"))
    for d in live[:3]:
        out.append((f"unfold-{d}", f"simp only [{_lean_name(d)}] at *\n"
                                   f"try intros"))
    for i, f in enumerate(facts):
        p = _lean_name(f)
        out.append((f"have-{f}", f"have h{have_n} := @{p}"))
        out.append((f"apply-{f}", f"apply @{p}"))
    # Megalodon's equality is a defined constant (`eq A a b`), not Lean's
    # `Eq`, so `rw` on a raw statement always fails with "expected an
    # equality or iff proof": every rewrite candidate was dead on arrival
    # until the bridge lemmas have turned `eq` into `=` first.
    for f in facts[:3]:
        p = _lean_name(f)
        out.append((f"rw-{f}", f"simp only [{BRIDGE}] at *\nrw [@{p}]"))
        out.append((f"rwr-{f}",
                    f"simp only [{BRIDGE}] at *\nrw [← @{p}]"))
    return out


def _target(goal_text):
    """The part of a printed goal after the turnstile.

    Progress is the target getting smaller, not the state getting smaller:
    a `have` grows the state by design, and scoring on total size would
    punish exactly the move this search exists to make."""
    i = goal_text.rfind("\u22a2")
    return goal_text[i:] if i >= 0 else goal_text


class _Node:
    __slots__ = ("script", "goals", "depth", "used", "have_n", "key", "tgt")

    def __init__(self, script, goals, depth, used, have_n):
        self.script = script
        self.goals = goals
        self.depth = depth
        self.used = used
        self.have_n = have_n
        # a state is the same state however it was reached; without this the
        # search spends its budget re-deriving `intros` by other routes
        self.key = "␞".join(goals)

    def rank(self):
        """Best-first order: shallow before deep, then fewer and smaller
        goals, as a stand-in for progress. A step that closes three of four
        subgoals shows up here as a much smaller state."""
        return (self.depth, len(self.goals), sum(len(g) for g in self.goals))


def prove(prover, goal, max_depth=3, max_probes=10, beam=3, k=6,
          probe_timeout=120, deadline=None, verbose=False, pre=None):
    """Search for a proof of `goal`. Returns (ok, label, script, stats).

    `ok` is Lean's verdict under the ordinary guard, not the search's: a
    script that closes every goal still has to pass attempt_batch."""
    t0 = time.time()
    defs = prover.goal_defs(goal)
    stats = {"probes": 0, "cands": 0, "closed": 0, "errors": 0,
             "seen": 0, "verified": 0}
    # Vampire's premises, if it found a proof at all. The one-shot prover
    # hands these straight to a fixed battery; here they only seed the pool,
    # and the search is free to range past them.
    if pre is not None:
        # reuse the premise sets the run being extended already computed:
        # Vampire over six slices is most of the wall clock here, and
        # re-deriving it would also make this run differ from that one for
        # reasons that have nothing to do with the search
        sets, vdefs, vstatus = pre
    else:
        try:
            sets, vdefs, vstatus = prover.premise_sets(goal)
        except Exception as e:
            sets, vdefs, vstatus = [], [], f"{type(e).__name__}"
    seed = []
    for s_ in sets:
        for f in s_:
            if f not in seed:
                seed.append(f)
    stats["vampire"] = vstatus
    stats["seed"] = len(seed)
    defs = sorted(set(defs) | set(vdefs))

    root = probe_batch(prover, goal, [("root", "skip")], timeout=probe_timeout)
    stats["probes"] += 1
    st, payload = root["root"]
    if st == "error":
        # `skip` cannot fail; this means the statement itself will not
        # elaborate, so there is nothing to search
        return False, None, None, dict(stats, why=f"root: {payload}")

    frontier = [_Node((), payload, 0, frozenset(), 0)]
    seen = {frontier[0].key}
    # Depth one is the existing battery, verbatim. A theorem the one-shot
    # prover can already do is then done here in one probe, and everything
    # past depth one is genuinely new ground rather than a reimplementation
    # of what the 640 already rest on.
    battery = []
    for s_ in (sets or [[]]):
        battery += candidate_tactics(s_, defs, prover.goal_defs(goal))
    battery += apply2_tactics(seed[:6], defs) if seed else []
    seen_scripts = set()
    battery = [(l, sc) for l, sc in battery
               if not (sc in seen_scripts or seen_scripts.add(sc))]

    while frontier and stats["probes"] < max_probes:
        if deadline and time.time() > deadline:
            stats["why"] = "deadline"
            break
        frontier.sort(key=lambda n: n.rank())
        node, frontier = frontier[0], frontier[1:beam * 4]
        if node.depth >= max_depth:
            continue
        cands = steps(prover, goal, node.goals[0], node.have_n, node.used,
                      k=k, defs=defs, seed=seed)
        if node.depth == 0 and battery:
            cands = battery[:24] + cands
        batch = [(f"d{node.depth}:{lab}", "\n".join(node.script + (tac,)))
                 for lab, tac in cands]
        stats["cands"] += len(batch)
        # One Lean process per chunk rather than per node: sixty candidates
        # in one file means one slow `grind` can take the whole batch's
        # timeout down with it, and the budget is counted in Lean calls.
        res = {}
        for ci in range(0, len(batch), 10):
            if stats["probes"] >= max_probes:
                break
            res.update(probe_batch(prover, goal, batch[ci:ci + 10],
                                   timeout=probe_timeout))
            stats["probes"] += 1
            if deadline and time.time() > deadline:
                break

        kids = []
        for (label, script), (lab2, tac) in zip(batch, cands):
            if label not in res:
                continue
            st, payload = res[label]
            if st == "error":
                stats["errors"] += 1
                continue
            if st == "closed":
                stats["closed"] += 1
                # the search thinks it is done; Lean's guard decides
                out = prover.attempt_batch(goal, [(label, script)],
                                           timeout=300, single_timeout=300,
                                           max_retry_secs=0)
                ok = out and out[0][1]
                if verbose:
                    print(f"    closed by {label}: guard={out[0][1:] if out else None}")
                if ok:
                    stats["verified"] += 1
                    stats["secs"] = round(time.time() - t0, 1)
                    return True, label, script, stats
                continue
            used = node.used | ({lab2[5:]} if lab2.startswith("have-") else set())
            kid = _Node(node.script + (tac,), payload, node.depth + 1, used,
                        node.have_n + (1 if lab2.startswith("have-") else 0))
            if kid.key in seen:
                stats["seen"] += 1
                continue
            seen.add(kid.key)
            kids.append(kid)
        kids.sort(key=lambda n: n.rank())
        frontier = kids[:beam] + frontier
        if verbose:
            print(f"  depth {node.depth}: {len(batch)} cands -> "
                  f"{len(kids)} new states, probes={stats['probes']}")

    stats["secs"] = round(time.time() - t0, 1)
    stats.setdefault("why", "exhausted" if not frontier else "probe budget")
    return False, None, None, stats
