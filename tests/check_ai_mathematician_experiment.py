#!/usr/bin/env python3
"""Exercise JSONL resume, source identity and renewed Lean acceptance."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from check_ai_mathematician_atp import read_values
from check_ai_mathematician_library import ROOT, quote
from check_ai_mathematician_prover import prelude as prover_prelude


def prelude():
    return prover_prelude() + f'!(import! &self {quote(ROOT / "phase1/experiment.metta")})\n'


def execute(binary, source, directory):
    path = directory / (hashlib.sha256(source.encode()).hexdigest()[:20] + ".metta")
    path.write_text(source)
    ran = subprocess.run([str(binary), "--lang", "petta@1.0.6", str(path)],
                         cwd=ROOT, text=True, capture_output=True, check=False)
    assert ran.returncode == 0, ran.stderr or ran.stdout[:2000]
    values = read_values(ran.stdout)
    imports = prelude().count("!(import!")
    assert values[:imports] == ["true"] * imports and len(values) == imports + 1, ran.stdout[:2000]
    return values[-1]


def check_cli_boundary(binary, corpus, vampire, lean, directory):
    log = directory / "cli observations with spaces.jsonl"
    trace = directory / "cli traces with spaces"
    stride = 1_000_000
    shard = stride - 1
    ran = subprocess.run([
        str(binary), "--lang", "petta@1.0.6",
        str(ROOT / "phase1/experiment_main.metta"),
        str(corpus), str(log), str(stride), "Fresh", str(vampire), str(lean),
        str(shard), "PythonV4", str(trace),
    ], cwd=ROOT, text=True, capture_output=True, check=False)
    assert ran.returncode == 0, ran.stderr or ran.stdout[:2000]
    assert "AiRun:Summary" in ran.stdout, ran.stdout[:2000]
    rows = [json.loads(line) for line in log.read_text().splitlines() if line.strip()]
    assert len(rows) == 1 and rows[0]["schema"] == "ai-math.run.v1", rows
    invalid_log = directory / "invalid shard must not create a log.jsonl"
    rejected = subprocess.run([
        str(binary), "--lang", "petta@1.0.6",
        str(ROOT / "phase1/experiment_main.metta"),
        str(corpus), str(invalid_log), "2", "Fresh", str(vampire), str(lean),
        "2", "PythonV4", str(trace),
    ], cwd=ROOT, text=True, capture_output=True, check=False)
    assert rejected.returncode == 2 and "AiRun:Request shard" in rejected.stdout, \
        rejected.stderr or rejected.stdout[:2000]
    assert not invalid_log.exists(), invalid_log
    return 7


def check_publication(binary, directory):
    destination = directory / "published snapshot"
    destination.write_text("previous-complete")
    pending = Path(str(destination) + ".pending")
    pending.write_text("interrupted-prefix")
    assert destination.read_text() == "previous-complete"
    result = execute(binary, prelude() +
                     f'!(ai-math:run-publish-file {quote(destination)} "next-complete")\n', directory)
    assert result == [] and destination.read_text() == "next-complete", result
    assert not pending.exists()
    blocked = directory / "blocked destination"
    blocked.mkdir()
    marker = blocked / "retained"
    marker.write_text("retained")
    result = execute(binary, prelude() +
                     f'!(ai-math:run-publish-file {quote(blocked)} "unpublished-complete")\n', directory)
    assert result[:2] == ["fs:failed", "fs:io"], result
    assert marker.read_text() == "retained"
    assert Path(str(blocked) + ".pending").read_text() == "unpublished-complete"
    assert destination.read_text() == "next-complete"
    return 8


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--vampire", type=Path, required=True)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--duper", action="store_true")
    args = parser.parse_args()
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    corpus = args.corpus.resolve()
    base = ROOT / ".cetta/experiment"
    base.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix="resume-", dir=base))
    cli_checks = check_cli_boundary(binary, corpus, args.vampire.resolve(), args.lean, output)
    cli_checks += check_publication(binary, output)
    log = output / "observations with spaces.jsonl"
    setup = prelude() + f"""
!(let* (($ds (ai-math:load-library {quote(corpus)}))
        ($context (ai-math:prover-with $ds {quote(corpus)} {quote(ROOT)} {quote(args.lean)} {quote(args.vampire.resolve())}
          ((slices ()) (lean-stages (base)) (induction false) (use-duper false)
           (base (AiProver:LeanPolicy (AiITP:Budget 30000 200000 8000)
             (AiITP:Budget 30000 200000 8000) 60000)))))
"""
    actual = execute(binary, setup + f"""
        ($owner (ai-math:run-open $context {quote(corpus)} {quote(log)} "test-toolchain" Fresh))
        ($first (ai-math:run-one $owner "orIL" (AiITP:Budget 30000 200000 8000)))
        ($summary (ai-math:run-summary $owner))
        ($resume (ai-math:run-open $context {quote(corpus)} {quote(log)} "test-toolchain" Resume))
        ($unverified (ai-math:run-summary $resume))
        ($again (ai-math:run-one $resume "orIL" (AiITP:Budget 30000 200000 8000))))
   ($first $summary $unverified $again (ai-math:run-summary $resume)
    (ai-math:run-open $context {quote(corpus)} {quote(log)} "test-toolchain" Fresh)))
""", output)
    first, summary, unverified, reused, resummary, refused = actual
    assert first[:2] == ["AiRun:Recorded", "orIL"], first
    assert summary[0] == "AiRun:Summary" and summary[2:4] == ["1", [["proved", "1"], ["not-proved", "0"], ["unfinished", "0"], ["fault", "0"]]], summary
    assert unverified[2] == "0", unverified
    assert reused[:3] == ["AiRun:Reused", "orIL", "rechecked"], reused
    assert resummary[2:4] == summary[2:4], resummary
    assert refused[:2] == ["AiRun:Request", "existing-log"], refused
    rows = [json.loads(line) for line in log.read_text().splitlines() if line.strip()]
    assert len(rows) == 2 and rows[1]["outcome"] == "proved", rows
    assert rows[1]["tactic"] and "Megalodon.orIL" not in rows[1]["used"], rows[1]
    checks = 8 + cli_checks
    with log.open("a") as stream:
        stream.write(json.dumps(dict(rows[1], used=["Megalodon.orIL"], axioms=["sorryAx"])) + "\n")
    actual = execute(binary, setup + f"""
        ($owner (ai-math:run-open $context {quote(corpus)} {quote(log)} "test-toolchain" Resume)))
   (ai-math:run-one $owner "orIL" (AiITP:Budget 30000 200000 8000)))
""", output)
    assert actual[:3] == ["AiRun:Reused", "orIL", "rechecked"], actual
    refreshed = {row[1]: row[2] for row in actual[3][1]}
    assert refreshed["used"] != ["JsonArray", ["Megalodon.orIL"]], refreshed["used"]
    assert refreshed["axioms"] != ["JsonArray", ["sorryAx"]], refreshed["axioms"]
    assert refreshed["resume_check"] == "kernel-and-source-order"
    checks += 4
    forged = dict(rows[1], tactic="exact orIL")
    with log.open("a") as stream:
        stream.write(json.dumps(forged) + '\n{"unfinished":')
    actual = execute(binary, setup + f"""
        ($owner (ai-math:run-open $context {quote(corpus)} {quote(log)} "test-toolchain" Resume))
        ($new (ai-math:run-one $owner "orIL" (AiITP:Budget 30000 200000 8000)))
        ($other (ai-math:run-one $owner "andI" (AiITP:Budget 30000 200000 8000)))
        ($again (ai-math:run-open $context {quote(corpus)} {quote(log)} "test-toolchain" Resume)))
   ($new $other (ai-math:run-summary $owner) (ai-math:run-summary $again)))
""", output)
    assert actual[0][:2] == ["AiRun:Recorded", "orIL"], actual[0]
    assert actual[1][:2] == ["AiRun:Recorded", "andI"], actual[1]
    assert actual[2][2] == "2" and len(actual[2][-1]) == 1, actual[2]
    assert actual[3][2] == "0" and len(actual[3][-1]) == 1, actual[3]
    checks += 4
    changed = output / "different.sexpr"
    changed.write_text(corpus.read_text() + "\nWARNING: changed export bytes\n")
    actual = execute(binary, setup + f"""
   )
   ((ai-math:run-open $context {quote(changed)} {quote(log)} "test-toolchain" Resume)
    (ai-math:run-open $context {quote(corpus)} {quote(log)} "other-toolchain" Resume)
    (ai-math:run-targets $context 100)
    (ai-math:run-targets-shard $context 100 1)
    (ai-math:run-targets $context 1)
    (ai-math:run-targets-shard $context 3 0)
    (ai-math:run-targets-shard $context 3 1)
    (ai-math:run-targets-shard $context 3 2)
    (ai-math:run-targets-shard $context 100 100)
    (ai-math:run-targets $context 0)
    (ai-math:run-trace-fields
      ((AiProver:Slice 8
         (AiATP:ArchivedAdvice (AiATP:Advice "Theorem" ("p") ())
           (AiATP:TraceRef "ai-math.tstp.v1" "goal" 8
             (AiATP:TraceObject Problem "problem" 10)
             (AiATP:TraceObject Solver "solver" 20) "parsed")) () ())
       (AiProver:Slice 16
         (AiATP:TraceFailure (AiATP:Advice "Theorem" () ()) write-failed) () ())))
    (ai-math:run-options-identity ((trace-directory "one") (definition-depth 3)))
    (ai-math:run-options-identity ((trace-directory "two") (definition-depth 3)))))
""", output)
    assert all(row[:2] == ["AiRun:Fault", "incompatible-run"] for row in actual[:2]), actual[:2]
    assert len(actual[2]) == 10 and len(actual[3]) == 10, actual[2:4]
    assert not set(map(str, actual[2])) & set(map(str, actual[3])), actual[2:4]
    all_targets, shards = actual[4], actual[5:8]
    flat = [name for shard in shards for name in shard]
    assert len(flat) == len(set(map(str, flat))) == len(all_targets), [len(all_targets), *map(len, shards)]
    assert set(map(str, flat)) == set(map(str, all_targets)), [len(all_targets), *map(len, shards)]
    assert actual[8] == ["AiRun:Request", "shard", ["100", "100"]], actual[8]
    assert actual[9] == ["AiRun:Request", "stride", "0"], actual[9]
    fields = actual[10]
    assert fields[0] == "AiRun:TraceFields" and len(fields[1]) == len(fields[2]) == 1, fields
    ref = {row[1]: row[2] for row in fields[1][0][1]}
    assert ref["schema"] == "ai-math.tstp.v1", ref
    assert ref["problem_sha256"] == "problem", ref
    fault = {row[1]: row[2] for row in fields[2][0][1]}
    assert fault["slice"] == "16" and "write-failed" in fault["detail"], fault
    assert actual[11] == actual[12] == [["trace-policy", "SuccessfulSolverEvidenceV1"],
                                        ["definition-depth", "3"]], actual[11:13]
    checks += 16
    actual = execute(binary, prelude() + f"""
!((ai-math:run-effective-options {quote(output)} ((use-duper Auto)))
  (ai-math:run-effective-options {quote(ROOT)} ((use-duper false)))
  (ai-math:run-effective-options {quote(ROOT)} ((lean-stages (base))))
  (ai-math:run-effective-options {quote(output)} ((lean-stages (base))))
  (ai-math:run-effective-options {quote(ROOT)} ((use-duper Auto))))
""", output)
    assert actual[0] == ["AiRun:EffectiveOptions", [["use-duper", "Auto"]],
                         ["base", "followup", "apply"]], actual[0]
    assert actual[1][-1] == ["base", "followup", "apply"], actual[1]
    assert actual[2] == actual[3] == ["AiRun:EffectiveOptions", [["lean-stages", ["base"]]],
                                     ["base"]], actual[2:4]
    checks += 3
    if args.duper:
        assert actual[4][-1] == ["base", "followup", "apply", "duper"], actual[4]
        assert actual[0] != actual[4], actual
        checks += 2
    if args.duper:
        script = "intros\ntry simp only [b_or] at *\nduper [*]"
        actual = execute(binary, setup + f"""
   )
   ((ai-math:run-reusable $context
      (JsonObject ((JsonPair "outcome" "proved")
                   (JsonPair "goal" "orIL")
                   (JsonPair "proof_profile" "duper")
                   (JsonPair "tactic" {quote(script)})))
      (AiITP:Budget 30000 1000000 8000))
    (json:get (ai-math:run-result "run" 0
      (AiProver:Result "orIL" 0 (AiProver:Hints (()) () () "" ()) ()
        (AiProver:Proved duper 0 "duper#1" {quote(script)} () ()))) "proof_profile")))
""", output)
        assert actual[0][0] == "AiRun:Rechecked", actual[0]
        assert actual[1] == "duper", actual[1]
        checks += 2
    print(f"AiMathematicianExperiment {checks} 0")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ValueError, IndexError, subprocess.CalledProcessError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        sys.exit(1)
