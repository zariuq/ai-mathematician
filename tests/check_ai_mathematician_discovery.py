#!/usr/bin/env python3
"""Focused discovery-adapter journal and owned-process controls."""
import argparse
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

from check_ai_mathematician_library import ROOT, quote
from compare_ai_mathematician_discovery import budget_exhaustions, check_induction_evidence, load
from complete_ai_mathematician_discovery import process_birth, qualification_manifest, wait_for_producer
from run_ai_mathematician_discovery import append, digest, owned_run, prior_results


def bounded_row(answer):
    attempt = f'(AiProver:Attempt base 0 "candidate" "skip" {answer})'
    return dict(goal='example-1', index=1, outcome='unfinished',
                evidence=f'(AiProver:Result "example-1" 1 () ({attempt}) (AiProver:Unfinished ({attempt})))')


def budget_controls():
    timeout = '(proc:result (proc:signaled 15) proc:timed-out "" "" ())'
    replies = [
        '(AiITP:Unfinished "example-1" retry-deadline ())',
        f'(AiITP:Unfinished "example-1" deadline {timeout})',
        '(AiITP:Unfinished "example-1" vampire-resource (64 "Timeout"))',
        f'(AiITP:Unfinished "example-1" vampire-process (64 "Unknown" {timeout} ()))',
        '(AiITP:Unfinished "example-1" "lean-errors" (JsonObject '
        '((JsonPair "schema" "ai-math.itp.v1") (JsonPair "target" "example-1") '
        '(JsonPair "kind" "unfinished") (JsonPair "reason" "lean-errors"))))',
    ]
    for answer in replies:
        assert len(budget_exhaustions(bounded_row(answer))) == 1
    explained = bounded_row(replies[0])
    explained['evidence'] = explained['evidence'].replace(
        ' () ((AiProver:Attempt', ' () ((AiProver:InductionEvidence (AiInd:NoReconstruction () ())) (AiProver:Attempt', 1)
    assert len(budget_exhaustions(explained)) == 1
    check_induction_evidence(['AiInd:NoReconstruction', [['AiATP:Advice', 'Timeout', [], []]], []])
    try:
        check_induction_evidence(['AiInd:NoReconstruction', [['AiATP:Advice', 'MemoryOut', [], []]], []])
    except AssertionError:
        pass
    else:
        raise AssertionError('induction memory failure was treated as a completed attempt budget')
    for answer in [
        '(AiITP:Unfinished "example-1" cancelled ())',
        '(AiITP:Unfinished "example-1" incomplete-capture ())',
        replies[2].replace('Timeout', 'MemoryOut'),
        '(AiITP:Unfinished "example-1" "lean-exception" (JsonObject '
        '((JsonPair "schema" "ai-math.itp.v1") (JsonPair "target" "example-1") '
        '(JsonPair "kind" "unfinished") (JsonPair "reason" "lean-exception") '
        '(JsonPair "message" "interrupted"))))',
        '(AiITP:Fault "example-1" process ())',
    ]:
        try:
            budget_exhaustions(bounded_row(answer))
        except AssertionError:
            pass
        else:
            raise AssertionError('unfinished/faulted work relabeled as budget exhaustion')
    return 13


def native_budget_controls(args, output):
    from check_ai_mathematician_prover import execute, prelude
    source = prelude() + f'''
!(let* (($decls (ai-math:load-library {quote(args.corpus)}))
        ($itp (ai-math:itp $decls {quote(ROOT)} {quote(args.lean)}))
        ((AiITP $catalog $root $lean $profile) $itp)
        ((AiITP:Declaration $index THM) (ai-math:get $catalog "orIL" AiMissing)))
   (map-atom ((AiITP:Budget 1 0 0) (AiITP:Budget 0 1 0) (AiITP:Budget 0 0 1)) $budget
     ($index (repr (ai-math:prover-run $itp "orIL" $index
       (AiProver:Hints (()) () () "skipped" ()) (base) (base)
       ((base (AiProver:LeanPolicy $budget $budget 1)))
       ((AiITP:Candidate "bounded" "intro P Q hp r f g\\nexact f hp")) () )))))
'''
    results = execute(args.cetta, source, output)
    assert len(results) == 3
    for index, evidence in results:
        row = dict(goal='orIL', index=int(index), outcome='unfinished', evidence=evidence)
        assert budget_exhaustions(row), evidence
    return len(results)


def cohort_controls(output):
    # Synthetic records exercise the evidence join, not Lean proof validity.
    targets = [f'example-{i}' for i in range(999)]
    rows = [dict(goal=name, index=i, outcome='not-proved') for i, name in enumerate(targets)]
    rows[0].update(outcome='proved', tactic='by trivial', used=[], axioms=[],
                   independent_check='kernel-statement-and-source-order')
    inputs = dict(targets=targets, full_corpus=True, python_revision='fixture',
                  tools=dict(corpus='same', lean='same', vampire='same'))
    summary = dict(targets=999, full_corpus=True, complete=True,
                   counts=dict(proved=1, **{'not-proved': 998, 'fault': 0, 'unfinished': 0, 'missing': 0}))
    directories = []
    for profile in ('python', 'PythonV4', 'CettaFull'):
        directory = output / profile
        directory.mkdir()
        directories.append(directory)
        (directory / 'inputs.json').write_text(json.dumps(dict(inputs, profile=profile)))
        receipt = dict(summary, profile=profile, input_manifest_sha256=digest(directory / 'inputs.json'))
        (directory / 'summary.json').write_text(json.dumps(receipt))
        (directory / 'comparison-input.json').write_text(json.dumps(rows))
        (directory / 'toolchain.json').write_text(json.dumps(dict(duper_revision='fixture')))
        _, observed = load(directory, profile)
        assert len(observed) == 999 and observed[targets[0]] == rows[0]
        if profile == 'PythonV4':
            budgeted = copy.deepcopy(rows)
            budgeted[1] = bounded_row('(AiITP:Unfinished "example-1" retry-deadline ())')
            receipt['complete'] = False
            receipt['counts'] = dict(receipt['counts'], **{'not-proved': 997, 'unfinished': 1})
            (directory / 'summary.json').write_text(json.dumps(receipt))
            (directory / 'comparison-input.json').write_text(json.dumps(budgeted))
            before = digest(directory / 'comparison-input.json')
            _, observed = load(directory, profile)
            assert observed['example-1']['outcome'] == 'not-proved'
            assert observed['example-1']['controller_outcome'] == 'unfinished'
            assert digest(directory / 'comparison-input.json') == before, 'raw controller record changed'
    command = [sys.executable, ROOT / 'tests/compare_ai_mathematician_discovery.py',
               '--python', directories[0], '--metta-v4', directories[1],
               '--metta-full', directories[2], '--output', output / 'comparison']
    result = owned_run(command)
    assert result.returncode == 0, result.stderr
    joined = json.loads(result.stdout)
    assert joined['goals'] == 999 and joined['v4_outcome_differences'] == 0
    assert joined['normalized_controller_unfinished']['PythonV4'] == 1
    checks = 5
    for case in ('unknown', 'missing', 'unverified', 'duplicate-index', 'false-count', 'changed-input'):
        mutated = copy.deepcopy(rows)
        receipt = dict(summary, profile='python', input_manifest_sha256=digest(directories[0] / 'inputs.json'))
        if case == 'unknown':
            mutated[1]['outcome'] = 'skipped'
        elif case == 'missing':
            mutated.pop()
        elif case == 'unverified':
            mutated[0].pop('independent_check')
        elif case == 'duplicate-index':
            mutated[1]['index'] = 0
        elif case == 'false-count':
            receipt['counts'] = dict(receipt['counts'], proved=2)
        else:
            receipt['input_manifest_sha256'] = 'not-the-input-hash'
        (directories[0] / 'comparison-input.json').write_text(json.dumps(mutated))
        (directories[0] / 'summary.json').write_text(json.dumps(receipt))
        try:
            load(directories[0], 'python')
        except AssertionError:
            checks += 1
        else:
            raise AssertionError(f'accepted invalid cohort: {case}')
    assert process_birth(os.getpid()) is not None and process_birth(0) is None
    checks += 1
    manifest = output / 'qualified-input.json'
    manifest.write_text(json.dumps(inputs, indent=2))
    receipt = dict(status='qualified', input_manifest=manifest.name,
                   input_manifest_sha256=digest(manifest))
    (output / 'result.json').write_text(json.dumps(receipt))
    assert qualification_manifest(output) == (inputs, digest(manifest))
    manifest.write_text('{}')
    try:
        qualification_manifest(output)
    except AssertionError:
        pass
    else:
        raise AssertionError('accepted changed qualification receipt')
    checks += 2
    marker = output / 'producer-finished'
    with subprocess.Popen([sys.executable, '-c',
            'import pathlib,sys,time; time.sleep(.05); pathlib.Path(sys.argv[1]).write_text("finished")',
            str(marker)]) as producer:
        wait_for_producer(producer.pid, interval=.01)
        assert producer.wait() == 0 and marker.read_text() == 'finished'
    wait_for_producer(0, interval=.01)
    return checks + 1


def launch_guard_controls(output):
    common = [item for flag in ('cetta', 'corpus', 'lean', 'vampire')
              for item in ('--' + flag, str(output / ('unavailable-' + flag)))]
    commands = [
        ('run_ai_mathematician_discovery.py', ['--profile', 'python']),
        ('complete_ai_mathematician_discovery.py',
         [item for flag in ('python', 'metta-v4', 'metta-full', 'qualification')
          for item in ('--' + flag, str(output / flag))]),
    ]
    for script, extra in commands:
        destination = output / (script + '-must-not-start')
        ran = subprocess.run([sys.executable, str(ROOT / 'tests' / script), *common,
                              *extra, '--output', str(destination)],
                             cwd=ROOT, text=True, capture_output=True, timeout=10)
        assert ran.returncode == 2 and 'requires --full-discovery' in ran.stderr, ran.stderr
        assert not destination.exists(), 'research was started without explicit selection'
    return len(commands)


def main():
    if sys.flags.optimize:
        raise RuntimeError('qualification checks require Python assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta', type=Path, required=True)
    parser.add_argument('--corpus', type=Path)
    parser.add_argument('--lean', type=Path)
    args = parser.parse_args()
    assert bool(args.corpus) == bool(args.lean), 'supply corpus and Lean together'
    base = ROOT / '.cetta/discovery-controls'
    base.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix='controls-', dir=base))
    journal = output / 'worker-0.jsonl'
    assert prior_results(output, 'worker-*.jsonl') == {}
    row = dict(goal='example', outcome='not-proved')
    append(journal, row)
    with journal.open('a') as stream:
        stream.write('{"goal":')
    assert prior_results(output, 'worker-*.jsonl') == {'example': row}
    bad = output / 'corrupt.jsonl'
    bad.write_text('{\n' + json.dumps(row) + '\n')
    try:
        prior_results(output, 'corrupt.jsonl')
    except json.JSONDecodeError:
        pass
    else:
        raise AssertionError('interior corruption was treated as a valid journal')
    completed = owned_run([sys.executable, '-c', 'print("owned")'])
    assert (completed.returncode, completed.stdout, completed.stderr) == (0, 'owned\n', '')
    # The grandchild retains the stdout pipe. Returning promptly after the
    # timeout therefore requires retiring the owned group, not just its leader.
    command = [sys.executable, '-c',
               'import subprocess,sys,time; '
               'subprocess.Popen([sys.executable,"-c","import time; time.sleep(30)"]); '
               'print("started",flush=True); time.sleep(30)']
    started = time.monotonic()
    try:
        owned_run(command, timeout=1)
    except subprocess.TimeoutExpired as error:
        assert error.stdout == 'started\n'
    else:
        raise AssertionError('missing process timeout')
    assert time.monotonic() - started < 10, 'owned grandchild outlived timeout cleanup'
    checks = 5 + cohort_controls(output) + budget_controls() + launch_guard_controls(output)
    if args.corpus:
        checks += native_budget_controls(args, output)
    print('AiMathematicianDiscovery', checks, 0)


if __name__ == '__main__':
    main()
