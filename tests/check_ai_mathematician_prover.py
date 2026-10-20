#!/usr/bin/env python3
"""Compare controller decisions with Python and exercise the checked Lean batch.

Python generates and checks test observations; the application runs in MeTTa.
"""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import shutil
import subprocess
import sys
from types import SimpleNamespace

from check_ai_mathematician_atp import read_values
from check_ai_mathematician_library import ROOT, quote
from check_ai_mathematician_itp import load_oracles
from python_oracle import oracle_directory

PROVER_SHA256 = "d3f97da4d0b4585d0cd572a24aad136afedbfdcf6c1827f39204b9477579ae63"


def prelude():
    return ("!(import! &self proc)\n"
            f'!(import! &self {quote(ROOT / "phase1/library.metta")})\n'
            "!(import! &self (library list))\n!(import! &self (library lib_tptp))\n"
            '!(import! &self re)\n'
            f'!(import! &self {quote(ROOT / "phase1/vampire_output.metta")})\n'
            f'!(import! &self {quote(ROOT / "phase1/search.metta")})\n'
            f'!(import! &self {quote(ROOT / "phase1/atp.metta")})\n'
            "!(import! &self json)\n!(import! &self system)\n"
            f'!(import! &self {quote(ROOT / "phase1/itp.metta")})\n'
            f'!(import! &self {quote(ROOT / "phase1/proof_strategy.metta")})\n'
            f'!(import! &self {quote(ROOT / "phase1/induction.metta")})\n'
            f'!(import! &self {quote(ROOT / "phase1/smt_bridge.metta")})\n'
            f'!(import! &self {quote(ROOT / "phase1/induction_prover.metta")})\n'
            f'!(import! &self {quote(ROOT / "phase1/prover.metta")})\n')


def execute(binary, source, directory):
    path = directory / (hashlib.sha256(source.encode()).hexdigest()[:20] + ".metta")
    path.write_text(source, encoding="utf-8")
    result = subprocess.run([str(binary), "--lang", "petta@1.0.6", str(path)],
                            cwd=ROOT.parent, text=True, capture_output=True, check=False)
    if result.returncode:
        raise AssertionError(result.stderr or result.stdout[:2000])
    values = read_values(result.stdout)
    imports = prelude().count("!(import!")
    assert values[:imports] == ["true"] * imports and len(values) == imports + 1, result.stdout[:2000]
    return values[-1]


def names(values):
    return "(" + " ".join(quote(value) for value in values) + ")"


def candidates(rows):
    return "(" + " ".join(f"(AiITP:Candidate {quote(label)} {quote(tactic)})"
                           for label, tactic in rows) + ")"


def check_candidates(binary, directory):
    reference_source = oracle_directory() / "prover.py"
    assert hashlib.sha256(reference_source.read_bytes()).hexdigest() == PROVER_SHA256
    load_oracles()
    spec = importlib.util.spec_from_file_location("original_prover", reference_source)
    oracle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracle)
    rng = random.Random(20261018)
    alphabet = ["orIL", "andI", "lamI", "pair_Sigma", "x'", "λ", "«nested»"]
    samples = [([], [], []), (["orIL"], [], []), ([], ["eq"], ["and"])]
    for _ in range(61):
        samples.append(tuple([rng.choice(alphabet) for _ in range(rng.randrange(5))]
                             for _ in range(3)))
    rows = " ".join(f"({names(p)} {names(d)} {names(g)})" for p, d, g in samples)
    observed = execute(binary, prelude() + f"""
!(map-atom ({rows}) $sample
   (let ($p $d $g) $sample
     ((ai-math:candidate-tactics $p $d $g)
      (ai-math:followup-tactics $p $d $g)
      (ai-math:apply-tactics $p $d)
      (ai-math:candidate-tactics $p $d)
      (ai-math:duper-tactics $p $d))))
""", directory)
    checks = 0
    for sample, actual in zip(samples, observed, strict=True):
        p, d, g = sample
        expected = [oracle.candidate_tactics(p, d, g), oracle.followup_tactics(p, d, g),
                    oracle.apply_tactics(p, d), oracle.candidate_tactics(p, d), oracle.duper_tactics(p, d)]
        for left, right in zip(actual, expected, strict=True):
            assert left == [["AiITP:Candidate", *entry] for entry in right], (sample, left, right)
            checks += len(right) + 1

    plans = []
    for sets, defs, gdefs, status in [
        ([[]], [], [], "skipped"),
        ([["orIL", "andI"], ["lamI"], []], ["Subq"], ["Subq"], "Theorem@16,32"),
        ([["λ"], ["x'", "λ"]], ["or"], [], "Timeout"),
        ([[], ["orIL"]], [], [], "Theorem@8"),
    ]:
        extra = [("extra", "exact custom")]
        stub = oracle.Prover.__new__(oracle.Prover)
        stub.use_duper = False
        stub.premise_sets = lambda goal: (sets, defs, status)
        stub.goal_defs = lambda goal: gdefs
        recorded = []

        def record(goal, cs, **kwargs):
            recorded.append(cs)
            return [(label, False, "test: not executed") for label, _ in cs]

        stub.attempt_batch = record
        stub.prove(SimpleNamespace(name="test", index=7), extra_candidates=extra, induction=False)
        hints = f"(AiProver:Hints ({' '.join(names(s) for s in sets)}) {names(defs)} {names(gdefs)} {quote(status)} ())"
        observed = execute(binary, prelude() + f"""
!(map-atom (base followup apply) $stage
   (ai-math:prover-stage-candidates $stage {hints} {candidates(extra)}))
""", directory)
        observed = [row for row in observed if row]
        assert observed == [[["AiITP:Candidate", *entry] for entry in row]
                            for row in recorded], (observed, recorded)
        plans.append(len(recorded))
        checks += sum(len(row) for row in recorded) + 1
    return checks, oracle


def check_units(binary):
    source = ROOT / "tests/metta/ai_mathematician_prover.metta"
    result = subprocess.run([str(binary), "--lang", "petta@1.0.6", str(source)],
                            cwd=ROOT.parent, text=True, capture_output=True, check=False)
    count = source.read_text().count("!(test")
    assert result.returncode == 0 and result.stdout.count("✅") == count, result.stdout + result.stderr
    assert "❌" not in result.stdout + result.stderr, result.stdout + result.stderr
    return count


def check_trace_objects(binary, directory):
    trace_dir = directory / "trace-object-controls"
    trace_dir.mkdir(parents=True, exist_ok=True)
    problem = "thf(goal,conjecture,$true).\n"
    solver = "% SZS status Theorem\n"
    problem_hash = hashlib.sha256(problem.encode()).hexdigest()
    solver_hash = hashlib.sha256(solver.encode()).hexdigest()
    corrupt = "content-address mismatch control"
    corrupt_hash = hashlib.sha256(corrupt.encode()).hexdigest()
    (trace_dir / f"{corrupt_hash}.problem.p").write_text("different", encoding="utf-8")
    missing = trace_dir / "missing-parent" / "objects"
    actual = execute(binary, prelude() + f"""
!(let* (($problem (ai-math:trace-write-object {quote(trace_dir)} Problem {quote(problem)}))
        ($same (ai-math:trace-write-object {quote(trace_dir)} Problem {quote(problem)}))
        ($solver (ai-math:trace-write-object {quote(trace_dir)} Solver {quote(solver)}))
        ($corrupt (ai-math:trace-write-object {quote(trace_dir)} Problem {quote(corrupt)}))
        ($missing (ai-math:trace-write-object {quote(missing)} Solver "x")))
   ($problem $same $solver $corrupt $missing))
""", directory)
    expected_problem = ["AiATP:TraceObject", "Problem", problem_hash, str(len(problem.encode()))]
    expected_solver = ["AiATP:TraceObject", "Solver", solver_hash, str(len(solver.encode()))]
    assert actual[:2] == [expected_problem, expected_problem], actual[:2]
    assert actual[2] == expected_solver, actual[2]
    assert actual[3][0] == "AiATP:TraceFault" and actual[3][1:3] == ["Problem", corrupt_hash], actual[3]
    assert actual[4][0] == "AiATP:TraceFault" and actual[4][1] == "Solver", actual[4]
    assert (trace_dir / f"{problem_hash}.problem.p").read_text(encoding="utf-8") == problem
    assert (trace_dir / f"{solver_hash}.solver.szs").read_text(encoding="utf-8") == solver
    return 7


def check_integration(binary, lean, vampire, corpus, directory, oracle):
    checks = 0
    genuine = "intro P Q hp r f g\nexact f hp"
    setup = (f"(let* (($decls (ai-math:load-library {quote(corpus)})) "
             f"($itp (ai-math:itp $decls {quote(ROOT)} {quote(lean)}))) ")
    rows = [("same", "exact orIL"), ("same", genuine),
            ("isolated", "exact CettaITP.checkedAttempt")]
    result = execute(binary, prelude() + "!" + setup + f"""
      (ai-math:itp-batch-with $itp "orIL" {candidates(rows)} (AiITP:Budget 30000 200000 8000)))
""", directory)
    assert result[:2] == ["AiITP:Batch", "orIL"], result
    assert [row[1] for row in result[2]] == [label for label, _ in rows], result
    assert [row[2][0] for row in result[2]] == ["AiITP:Rejected", "AiITP:Accepted", "AiITP:Rejected"], result
    assert any(reason in str(result[2][0][2]) for reason in
               ("source-order", "Unknown identifier", "Unknown constant")), result
    checks += 5

    # A bounded batch may expire before producing a complete reply. Retrying
    # isolates each attempt, then skips remaining work only after acceptance.
    retry = execute(binary, prelude() + "!" + setup + f"""
      (ai-math:itp-batch-resilient $itp "orIL" {candidates(rows)}
        (AiITP:Budget 1 200000 8000) (AiITP:Budget 30000 200000 8000) 60000))
""", directory)
    assert retry[:2] == ["AiITP:Batch", "orIL"], retry
    assert [row[2][0] for row in retry[2]] == ["AiITP:Rejected", "AiITP:Accepted", "AiITP:Skipped"], retry
    checks += 2

    slow = ('run_tac do\n  for _ in [:10000000] do\n'
            '    Lean.Core.checkMaxHeartbeats "batch-budget-control"\n' + genuine)
    resource = execute(binary, prelude() + "!" + setup + f"""
      (ai-math:itp-batch-with $itp "orIL" {candidates([('slow', slow), ('fast', genuine)])}
        (AiITP:Budget 30000 10000 8000)))
""", directory)
    assert resource[:2] == ["AiITP:Batch", "orIL"], resource
    assert [row[2][0] for row in resource[2]] == ["AiITP:Unfinished", "AiITP:Accepted"], resource
    checks += 2

    noisy = [('noise', 'run_tac IO.println "not protocol"\n' + genuine), ('fast', genuine)]
    printed = execute(binary, prelude() + "!" + setup + f"""
      (ai-math:itp-batch-with $itp "orIL"
        {candidates(noisy)}
        (AiITP:Budget 30000 200000 8000)))
""", directory)
    assert printed[:2] == ["AiITP:Batch", "orIL"], printed
    assert [row[2][0] for row in printed[2]] == ["AiITP:Accepted", "AiITP:Accepted"], printed
    checks += 2

    fake = json.dumps({"schema": "ai-math.itp.v1", "target": "orIL",
                       "kind": "checked", "reason": "ok", "used": [],
                       "axioms": []}, separators=(",", ":"))
    forged_exit = ("run_tac do\n  (← IO.getStdout).putStrLn "
                   + json.dumps(fake) + "\n  IO.Process.exit (α := Unit) 0")
    interrupted = execute(binary, prelude() + "!" + setup + f"""
      (ai-math:itp-batch-with $itp "orIL"
        {candidates([('valid-before-exit', genuine), ('forged', forged_exit)])}
        (AiITP:Budget 30000 200000 8000)))
""", directory)
    assert interrupted[0] == "AiITP:Fault", interrupted
    checks += 1

    budget = "(AiProver:LeanPolicy (AiITP:Budget 30000 200000 8000) (AiITP:Budget 30000 200000 8000) 60000)"
    trace_dir = directory / "solver-trace-integration"
    trace_dir.mkdir(parents=True, exist_ok=True)
    options = (f"((slices (8 16)) (vampire-seconds 2) (trace-directory {quote(trace_dir)}) "
               f"(base {budget}) (followup {budget}) (apply {budget}))")
    program = prelude() + f"""
!(let* (($decls (ai-math:load-library {quote(corpus)}))
        ($context (ai-math:prover-with $decls {quote(corpus)} {quote(ROOT)} {quote(lean)} {quote(vampire)} {options})))
   (let (AiProver $search $thf $itp $vampire $options) $context
     (ProverCorpus
       (map-atom ("orIL" "andI" "not-a-corpus-theorem") $name (ai-math:prove $context $name))
       (map-atom (filter-atom (ai-math:search-facts $search) $fact
                   (== (ai-math:declaration-kind $fact) THM)) $fact
         ((ai-math:declaration-name $fact) (ai-math:prover-goal-defs $thf $fact))))))
"""
    report = execute(binary, program, directory)
    assert report[0] == "ProverCorpus", report
    _, results, definitions = report
    for target, result in zip(["orIL", "andI"], results[:2], strict=True):
        assert result[:2] == ["AiProver:Result", target], result
        assert result[-1][0] == "AiProver:Proved", result
        assert result[-1][1] == "base", result[-1]
        assert len(result[3][-1]) == 2, result[3]  # Both Vampire slices ran.
        assert all(row[1] == "base" for row in result[4]), result[4]
        archived = [row[2] for row in result[3][-1]
                    if row[2][0] == "AiATP:ArchivedAdvice"]
        assert archived, result[3][-1]
        for wrapper in archived:
            ref = wrapper[2]
            assert ref[:3] == ["AiATP:TraceRef", "ai-math.tstp.v1", target], ref
            assert ref[3] in ("8", "16"), ref
            for obj, suffix in ((ref[4], ".problem.p"), (ref[5], ".solver.szs")):
                path = trace_dir / f"{obj[2]}{suffix}"
                data = path.read_bytes()
                assert len(data) == int(obj[3]) and hashlib.sha256(data).hexdigest() == obj[2], (path, obj)
        checks += 6 + 2 * len(archived)
    assert results[2][:3] == ["AiProver:Fault", "not-a-corpus-theorem", "unknown-theorem"], results[2]
    checks += 1

    # Test the later strategies with a genuine earlier identical theorem,
    # independently of which sufficient hints this Vampire build selects.
    library, _ = load_oracles()
    decls = library.load(str(corpus))
    by_name = {decl.name: decl for decl in decls}
    stub = oracle.Prover.__new__(oracle.Prover)
    stub.by_name = by_name
    expected = [[decl.name, stub.goal_defs(decl)] for decl in decls if decl.kind == "THM"]
    assert definitions == expected, (definitions[:5], expected[:5])
    checks += len(expected)
    print(f"ProverGoalDefinitions {len(expected)} 0", flush=True)
    early, late = sorted((by_name["pair_Sigma"], by_name["lamI"]), key=lambda decl: decl.index)
    later = execute(binary, prelude() + "!" + setup + f"""
      (map-atom (followup apply) $stage
        (ai-math:prover-run $itp {quote(late.name)} {late.index}
          (AiProver:Hints (({quote(early.name)})) () () "Theorem@control" ())
          ($stage) ($stage) {options} () ())))
""", directory)
    for stage, result in zip(["followup", "apply"], later, strict=True):
        assert result[:2] == ["AiProver:Result", late.name], result
        assert result[-1][:2] == ["AiProver:Proved", stage], result[-1]
        assert "Megalodon." + early.name in result[-1][-2], result[-1]
        checks += 3

    # Retain no-match, unfinished work and operational failure separately,
    # even when a wall deadline prevents the entire batch reply.
    failures = execute(binary, prelude() + "!" + setup + f"""
      (let (AiITP $catalog $root $lean $profile) $itp
       (map-atom (("rejected" {quote(late.name)} {late.index} (AiITP:Budget 30000 200000 8000) $itp)
                  ("unfinished" "orIL" {by_name['orIL'].index} (AiITP:Budget 1 200000 8000) $itp)
                  ("fault" "orIL" {by_name['orIL'].index} (AiITP:Budget 30000 200000 8000)
                    (AiITP $catalog $root "nonexistent-ai-math-lean" $profile))) $control
        (let ($label $target $index $budget $context) $control
          ($label (ai-math:prover-run $context $target $index
            (AiProver:Hints (()) () () "skipped" ()) (base) (base)
            ((base (AiProver:LeanPolicy $budget $budget 1)))
            ((AiITP:Candidate "self" (str:concat "exact " $target))) ()))))))
""", directory)
    assert all(row[1][0] == "AiProver:Result" for row in failures), failures
    assert failures[0][1][-1][0] == "AiProver:NotProved", failures[0]
    assert failures[1][1][-1][0] == "AiProver:Unfinished", failures[1]
    assert failures[2][1][-1][0] == "AiProver:Faulted", failures[2]
    checks += 4

    # The CLI is an actual Python-free consumer, including foreign CWDs.
    cli = subprocess.run([str(binary), "--no-results", "--lang", "petta@1.0.6",
                          str(ROOT / "phase1/prover_main.metta"), str(corpus),
                          "orIL", str(vampire), lean], cwd=ROOT.parent,
                         text=True, capture_output=True, check=False)
    assert cli.returncode == 0, cli.stdout + cli.stderr
    assert read_values(cli.stdout)[0][-1][0] == "AiProver:Proved", cli.stdout
    checks += 1
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--vampire", type=Path)
    parser.add_argument("--corpus", type=Path)
    args = parser.parse_args()
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    directory = ROOT / ".cetta/prover"
    directory.mkdir(parents=True, exist_ok=True)
    candidate_checks, oracle = check_candidates(binary, directory)
    checks = check_units(binary) + check_trace_objects(binary, directory) + candidate_checks
    print(f"ProverCandidates {checks} 0", flush=True)
    if args.corpus and args.vampire:
        prefix = subprocess.run([args.lean, "--print-prefix"], cwd=ROOT, text=True,
                                capture_output=True, check=True).stdout.strip()
        lean = str(Path(prefix) / "bin/lean")
        vampire = Path(shutil.which(str(args.vampire)) or args.vampire).resolve()
        checks += check_integration(binary, lean, vampire, args.corpus.resolve(), directory, oracle)
    else:
        print("ProverIntegrationSkipped: supply --corpus and --vampire for checked execution")
    print(f"AiMathematicianProver {checks} 0")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ValueError, IndexError, subprocess.CalledProcessError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        sys.exit(1)
