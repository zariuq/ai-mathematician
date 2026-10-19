#!/usr/bin/env python3
"""Check process partitioning, private journals, joins and checked resume."""
import argparse
import fcntl
import hashlib
import json
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

from check_ai_mathematician_experiment import prelude as run_prelude
from check_ai_mathematician_library import ROOT, quote


def prelude():
    return run_prelude() + f'!(import! &self {quote(ROOT / "phase1/experiment_workers.metta")})\n'


def run_config(binary, config_path, config, *, cwd=ROOT):
    config_path.write_text(json.dumps(config))
    start = time.monotonic_ns()
    ran = subprocess.run([str(binary), "--no-results", "--lang", "petta@1.0.6",
                          str(ROOT / "phase1/workers_main.metta"), str(config_path)],
                         cwd=cwd, text=True, capture_output=True, check=False)
    elapsed = time.monotonic_ns() - start
    return ran, elapsed


def records(path):
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--corpus", type=Path)
    parser.add_argument("--vampire", default="vampire")
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--real", action="store_true", help="Compare real one/two-worker proof runs")
    parser.add_argument("--worker-counts", default="1,2", help="Worker counts to compare (for example 1,2,4)")
    args = parser.parse_args()
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    base = ROOT / ".cetta/workers"
    base.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix="controls-", dir=base))
    worker_counts = [int(value) for value in args.worker_counts.split(",")]
    assert worker_counts and all(value > 0 for value in worker_counts), "positive worker counts required"
    unit = ROOT / "tests/metta/ai_mathematician_workers.metta"
    checked = subprocess.run([str(binary), "--lang", "petta@1.0.6", str(unit)], cwd=ROOT,
                             text=True, capture_output=True, check=False)
    unit_count = len(re.findall(r"^!\(test\b", unit.read_text(), re.M))
    assert checked.returncode == 0 and checked.stdout.count("✅") == unit_count, checked.stdout + checked.stderr
    assert "❌" not in checked.stdout + checked.stderr, checked.stdout + checked.stderr
    source = prelude() + r'''
!(let* (($good (json-parse "{\"corpus\":\"c.sexpr\",\"output\":\"run\"}"))
        ($decls ((Decl 2 THM "a" "h" () NoBody () () ())
                 (Decl 5 AXIOM "p" "h" () NoBody () () ())
                 (Decl 7 THM "b" "h" () NoBody () () ())
                 (Decl 9 THM "c" "h" () NoBody () () ())
                 (Decl 12 THM "d" "h" () NoBody () () ()))))
   ((ai-math:workers-config-valid $good)
    (ai-math:workers-config-valid (json-parse "{\"corpus\":\"c\",\"output\":\"r\",\"workers\":0}"))
    (ai-math:workers-config-valid (json-parse "{\"corpus\":\"c\",\"output\":\"r\",\"workers\":1.5}"))
    (ai-math:workers-config-valid (json-parse "{\"corpus\":\"c\",\"output\":\"r\",\"typo\":true}"))
    (ai-math:workers-config-valid (json-parse "{\"corpus\":\"c\",\"output\":\"r\",\"trace\":1}"))
    (ai-math:workers-config-valid (json-parse "{\"corpus\":\"c\",\"output\":\"r\",\"goals\":[4]}"))
    (ai-math:workers-targets $decls $good)
    (ai-math:workers-targets $decls (json-parse "{\"stride\":2,\"skip\":1,\"limit\":1}"))
    (ai-math:workers-targets $decls (json-parse "{\"goals\":[\"d\",\"a\"]}"))
    (ai-math:workers-targets $decls (json-parse "{\"goals\":[\"a\",\"a\"]}"))
    (ai-math:workers-targets $decls (json-parse "{\"goals\":[\"unknown\"]}"))
    (ai-math:workers-partition ((2 "a") (7 "b") (9 "c") (12 "d")) 2 0)
    (ai-math:workers-partition ((2 "a") (7 "b") (9 "c") (12 "d")) 2 1)
    (ai-math:workers-options (json-parse "{\"slices\":[],\"lean_stages\":[\"base\"],\"induction\":false,\"use_duper\":false}") "traces")
    (ai-math:workers-dirname "/a path/config.json")
    (ai-math:workers-dirname "/config.json")
    (ai-math:workers-process-text (proc:result (proc:exited 0) proc:normal "ok" ""
       (proc:capture 2 3 0 0 proc:eof proc:eof (proc:input 0 0))))
    (ai-math:workers-exit-code (AiWorkers:Summary "key" 1 (("proved" 0) ("not-proved" 0) ("unfinished" 1) ("fault" 0)) "out"))))
'''
    # The experiment harness counts its own prelude imports.
    from check_ai_mathematician_atp import read_values
    path = directory / "pure.metta"
    path.write_text(source)
    ran = subprocess.run([str(binary), "--lang", "petta@1.0.6", str(path)], cwd=ROOT,
                         text=True, capture_output=True, check=False)
    assert ran.returncode == 0, ran.stderr or ran.stdout[:3000]
    rows = read_values(ran.stdout)
    assert rows[:-1] == ["true"] * prelude().count("!(import!"), ran.stdout[:3000]
    got = rows[-1]
    assert got[:6] == ["true", "false", "false", "false", "false", "false"], got[:6]
    assert got[6] == [["2", "a"], ["7", "b"], ["9", "c"], ["12", "d"]], got[6]
    assert got[7] == [["7", "b"]], got[7]
    assert got[8] == [["2", "a"], ["12", "d"]], got[8]
    assert all(row[:2] == ["AiWorkers:Request", "goals"] for row in got[9:11]), got[9:11]
    assert got[11:13] == [[["2", "a"], ["9", "c"]], [["7", "b"], ["12", "d"]]], got[11:13]
    options = dict(got[13])
    assert options["slices"] == [] and options["lean-stages"] == ["base"], options
    assert options["induction"] == options["use-duper"] == "false", options
    assert got[14:16] == ["/a path", "/"], got[14:16]
    assert got[16][:2] == ["AiWorkers:Fault", "incomplete-process"], got[16]
    assert got[17] == "3", got[17]
    checks = 22 + unit_count

    # Exhaust the small partition domain. Job order is presentation only;
    # the observed bag must contain every requested occurrence exactly once.
    expressions, expected = [], []
    for size in range(17):
        for count in range(1, 10):
            entries = "(" + " ".join(f'({i * 3} "g{i}")' for i in range(size)) + ")"
            expressions.append("(" + " ".join(
                f"(ai-math:workers-partition {entries} {count} {worker})"
                for worker in range(count)) + ")")
            expected.append([[str(i * 3), f"g{i}"] for i in range(size)])
    partition_source = prelude() + "!(" + " ".join(expressions) + ")\n"
    path = directory / "partitions.metta"
    path.write_text(partition_source)
    ran = subprocess.run([str(binary), "--lang", "petta@1.0.6", str(path)], cwd=ROOT,
                         text=True, capture_output=True, check=False)
    assert ran.returncode == 0, ran.stderr or ran.stdout[:3000]
    values = read_values(ran.stdout)[-1]
    assert len(values) == len(expected)
    for shards, wanted in zip(values, expected):
        flat = [entry for shard in shards for entry in shard]
        assert sorted(flat) == sorted(wanted), (shards, wanted)
        checks += 1
    path = directory / "cancel-and-fault.metta"
    path.write_text(prelude() + '''
!(let* (($owner (proc:spawn ("sleep" "30") ()))
        ($waited (proc:wait $owner 10))
        ($closed (ai-math:workers-cancel ((AiWorkers:Active ignored $owner)))))
   ((proc:status $owner)
    (ai-math:workers-observe (AiRun:Identity "key" descriptor)
      (AiWorkers:Job 7 () "journal" "snapshot" "traces")
      (proc:result (proc:exited 7) proc:normal "" "diagnostic"
        (proc:capture 0 0 10 10 proc:eof proc:eof (proc:input 0 0))))))
''')
    cancelled = subprocess.run([str(binary), "--lang", "petta@1.0.6", str(path)], cwd=ROOT,
                               text=True, capture_output=True, check=False)
    assert cancelled.returncode == 0, cancelled.stderr or cancelled.stdout[:3000]
    closed, failed = read_values(cancelled.stdout)[-1]
    assert closed[:2] == ["proc:failed", "proc:invalid-handle"], closed
    assert failed[:2] == ["AiWorkers:FailedWorker", "7"], failed
    assert failed[2][:2] == ["AiWorkers:Fault", "process"], failed
    checks += 3

    if args.corpus:
        corpus = args.corpus.resolve()
        config_path = directory / "run config with spaces.json"
        invalid = {"corpus": str(corpus), "output": "must not exist", "goals": ["not-a-theorem"]}
        ran, _ = run_config(binary, config_path, invalid, cwd=Path("/"))
        assert ran.returncode == 2 and "AiWorkers:Request goals" in ran.stdout, ran.stderr or ran.stdout[:3000]
        assert not (directory / "must not exist").exists()
        empty = {"corpus": str(corpus), "output": "empty run", "goals": [], "workers": 2,
                 "lean": args.lean, "vampire": args.vampire}
        ran, _ = run_config(binary, config_path, empty, cwd=Path("/"))
        assert ran.returncode == 0 and "AiWorkers:Summary" in ran.stdout, ran.stderr or ran.stdout[:3000]
        assert len(records(directory / "empty run/joined.jsonl")) == 1
        empty["mode"] = "Resume"
        ran, _ = run_config(binary, config_path, empty)
        assert ran.returncode == 0, ran.stderr or ran.stdout[:3000]
        make_config = {"corpus": str(corpus), "output": "make entry", "goals": []}
        config_path.write_text(json.dumps(make_config))
        made = subprocess.run(["make", "--no-print-directory", "-s", "run-cetta",
                               "CETTA=" + str(binary), "RUN_CONFIG=" + str(config_path),
                               "LEAN=" + args.lean, "VAMPIRE=" + args.vampire],
                              cwd=ROOT, text=True, capture_output=True, check=False)
        assert made.returncode == 0 and "AiWorkers:Summary" in made.stdout, made.stderr or made.stdout[:3000]
        make_header = records(directory / "make entry/joined.jsonl")[0]
        assert args.lean in make_header["descriptor"] and args.vampire in make_header["descriptor"], make_header
        checks += 2
        # Joining is an exact partition check, not a count-only check.
        joined = records(directory / "empty run/joined.jsonl")
        identity = joined[0]
        identity_atom = '(AiRun:Identity ' + quote(identity["run"]) + " (parse-first " + quote(identity["descriptor"]) + "))"
        sample = {"schema": "ai-math.result.v1", "run": identity["run"],
                  "goal": "example", "index": 3, "outcome": "not-proved"}
        controls = [([sample], [[3, "example"]], "true"),
                    ([sample, sample], [[3, "example"], [7, "other"]], "false"),
                    ([dict(sample, run="foreign")], [[3, "example"]], "false"),
                    ([dict(sample, index=4)], [[3, "example"]], "false"),
                    ([], [[3, "example"]], "false"),
                    ([dict(sample, outcome="accepted")], [[3, "example"]], "false")]
        exprs = []
        for observations, targets, _ in controls:
            json_rows = [identity] + observations
            metta_rows = "(" + " ".join("(json-parse " + quote(json.dumps(r)) + ")" for r in json_rows) + ")"
            metta_targets = "(" + " ".join(f"({i} {quote(name)})" for i, name in targets) + ")"
            exprs.append(f"(ai-math:workers-snapshot-valid {metta_rows} {identity_atom} {metta_targets})")
        path = directory / "join-controls.metta"
        path.write_text(prelude() + "!(" + " ".join(exprs) + ")\n")
        checked = subprocess.run([str(binary), "--lang", "petta@1.0.6", str(path)], cwd=ROOT,
                                 text=True, capture_output=True, check=False)
        assert checked.returncode == 0, checked.stderr or checked.stdout[:3000]
        assert read_values(checked.stdout)[-1] == [c[2] for c in controls], checked.stdout[-3000:]
        # A fresh invocation must not overwrite a completed run.
        before = (directory / "empty run/manifest.json").read_bytes()
        empty["mode"] = "Fresh"
        refused, _ = run_config(binary, config_path, empty)
        assert refused.returncode == 2 and "existing-output" in refused.stdout, refused.stdout[:3000]
        assert (directory / "empty run/manifest.json").read_bytes() == before
        # Unknown manifests are not resume authority.
        (directory / "empty run/manifest.json").write_text('{}\n')
        empty["mode"] = "Resume"
        refused, _ = run_config(binary, config_path, empty)
        assert refused.returncode == 2 and "incompatible-manifest" in refused.stdout, refused.stdout[:3000]
        # An independently held lock excludes the coordinator before effects.
        locked = dict(empty, mode="Fresh", output="locked run")
        with (directory / "locked run.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            refused, _ = run_config(binary, config_path, locked)
            assert refused.returncode == 4, refused.stderr or refused.stdout[:3000]
        assert not (directory / "locked run").exists()
        # Worker deadline is unfinished, never a published negative result.
        deadline = dict(empty, mode="Fresh", output="deadline run", goals=["andI", "orIL"],
                        worker_timeout_ms=1)
        timed, _ = run_config(binary, config_path, deadline)
        assert timed.returncode == 3 and "Unfinished deadline" in timed.stdout, timed.stderr or timed.stdout[:3000]
        assert not (directory / "deadline run/joined.jsonl").exists()
        checks += 18

    if args.real:
        assert args.corpus, "--real requires --corpus"
        comparisons = []
        for count in worker_counts:
            config = {"corpus": str(args.corpus.resolve()), "output": f"real {count}", "workers": count,
                      "goals": ["andI", "orIL", "orIR", "iffI"], "lean": args.lean,
                      "vampire": args.vampire, "slices": [], "lean_stages": ["base"],
                      "induction": False, "use_duper": False}
            ran, elapsed = run_config(binary, config_path, config, cwd=Path("/"))
            assert ran.returncode == 0, ran.stderr or ran.stdout[:5000]
            result = records(directory / f"real {count}/joined.jsonl")
            assert len(result) == 5 and all(row["outcome"] == "proved" for row in result[1:]), result
            observations = [(r["goal"], r["index"], r["outcome"], r["tactic"], r["used"], r["axioms"]) for r in result[1:]]
            comparisons.append(observations)
            config["mode"] = "Resume"
            resumed, resume_ns = run_config(binary, config_path, config)
            assert resumed.returncode == 0, resumed.stderr or resumed.stdout[:3000]
            refreshed = records(directory / f"real {count}/joined.jsonl")
            assert all(row["resume_check"] == "kernel-and-source-order" for row in refreshed[1:]), refreshed
            print(json.dumps({"workers": count, "fresh_ns": elapsed, "resume_ns": resume_ns,
                              "source_sha256": hashlib.sha256((ROOT / "phase1/experiment_workers.metta").read_bytes()).hexdigest()}))
            checks += 5
        assert all(observation == comparisons[0] for observation in comparisons), comparisons
        checks += 1
        trace_config = {"corpus": str(args.corpus.resolve()), "output": "solver traces", "workers": 2,
                        "goals": ["andI", "orIL"], "lean": args.lean, "vampire": args.vampire,
                        "slices": [8], "lean_stages": ["base"], "induction": False,
                        "use_duper": False, "trace": True}
        traced, _ = run_config(binary, config_path, trace_config)
        assert traced.returncode == 0, traced.stderr or traced.stdout[:3000]
        trace_rows = records(directory / "solver traces/joined.jsonl")[1:]
        assert len(trace_rows) == 2 and all(r["outcome"] == "proved" for r in trace_rows), trace_rows
        for worker in range(2):
            snapshot = records(directory / f"solver traces/worker-{worker}.snapshot.jsonl")
            assert len(snapshot) == 2 and len(snapshot[1]["solver_traces"]) == 1, snapshot
            evidence = snapshot[1]["solver_traces"][0]
            for kind, suffix in (("problem", "problem.p"), ("solver", "solver.szs")):
                digest = evidence[kind + "_sha256"]
                content = (directory / f"solver traces/worker-{worker}-traces/{digest}.{suffix}").read_bytes()
                assert hashlib.sha256(content).hexdigest() == digest
                assert len(content) == evidence[kind + "_bytes"]
                checks += 2
        # A Duper success must resume in the same trusted import profile,
        # without silently reproving and appending a replacement record.
        duper_config = dict(trace_config, output="duper profile", goals=["orIL"],
                            workers=1, trace=False, lean_stages=["duper"], use_duper=True)
        if (ROOT / "tools/duper-env/.lake/packages/Duper/.lake/build/lib/lean/Duper.olean").is_file():
            proved, _ = run_config(binary, config_path, duper_config)
            assert proved.returncode == 0, proved.stderr or proved.stdout[:3000]
            fresh_rows = records(directory / "duper profile/joined.jsonl")
            assert fresh_rows[1]["proof_profile"] == "duper" and fresh_rows[1]["outcome"] == "proved", fresh_rows
            journal = directory / "duper profile/worker-0.jsonl"
            original_bytes = journal.read_bytes()
            duper_config["mode"] = "Resume"
            checked, _ = run_config(binary, config_path, duper_config)
            assert checked.returncode == 0, checked.stderr or checked.stdout[:3000]
            assert journal.read_bytes() == original_bytes
            checked_rows = records(directory / "duper profile/joined.jsonl")
            assert checked_rows[1]["resume_check"] == "kernel-and-source-order", checked_rows
            checks += 5
        else:
            print("WorkersDuperSkipped: prepare-cetta-duper enables the optional profile check")
    elif args.corpus:
        print("WorkersRealProofsSkipped: --real enables solver/kernel and process-count comparisons")
    else:
        print("WorkersIntegrationSkipped: --corpus and --real enable corpus/solver/kernel controls")
    print("WorkersEvidence " + str(directory.relative_to(ROOT)))
    print(f"AiMathematicianWorkers {checks} 0")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ValueError, IndexError, subprocess.CalledProcessError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        sys.exit(1)
