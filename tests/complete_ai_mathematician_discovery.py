#!/usr/bin/env python3
"""Sequence an optional three-cohort proof-discovery research experiment.

This is not a port acceptance command. --full-discovery explicitly selects
the exhaustive study; ordinary qualification never invokes it.

An already running Python reference may be awaited by PID. Its process birth
identity is checked while waiting; a vanished producer or incomplete result
stops the sequence. No negative result is invented to fill a missing goal.
"""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

from check_ai_mathematician_library import ROOT
from compare_ai_mathematician_discovery import load
from run_ai_mathematician_discovery import digest, owned_run


def process_birth(pid):
    try:
        # Linux stat's command field may itself contain spaces/parentheses.
        fields = Path(f'/proc/{pid}/stat').read_text().rsplit(') ', 1)[1].split()
        return None if fields[0] in ('Z', 'X') else fields[19]
    except (FileNotFoundError, ProcessLookupError):
        return None


def wait_for_producer(pid, interval=20):
    birth = process_birth(pid)
    if birth is not None:
        while process_birth(pid) == birth:
            time.sleep(interval)


def checked_summary(directory, profile):
    _, rows = load(directory, profile)
    result = json.loads((directory / 'summary.json').read_text())
    observed = Counter(row['outcome'] for row in rows.values())
    result['controller_counts'] = result['counts']
    result['counts'] = {key: observed[key] for key in result['counts']}
    result['complete'] = True
    return result


def completed_cohort(directory, profile):
    if not (directory / 'summary.json').exists():
        return False
    try:
        checked_summary(directory, profile)
    except AssertionError:
        return False
    return True


def qualification_manifest(directory):
    qualification = json.loads((directory / 'result.json').read_text())
    assert qualification['status'] == 'qualified'
    key = qualification['input_manifest_sha256']
    name = qualification['input_manifest']
    assert Path(name).name == name, 'input receipt must be local to qualification'
    path = directory / name
    assert digest(path) == key, 'qualification input receipt changed'
    return json.loads(path.read_text()), key


def qualified_toolchain(args):
    manifest, key = qualification_manifest(args.qualification)
    for name in ('cetta', 'corpus', 'lean', 'vampire'):
        path = getattr(args, name)
        assert manifest['tools'][str(path)] == digest(path), (name, 'requalify changed tool')
    for name in ('itp-worker', 'itp-guard'):
        path = ROOT / '.cetta/lean-native' / name
        assert manifest['tools'][str(path)] == digest(path), (name, 'checker artifact changed')
    # Driver/report edits need not invalidate an unchanged runtime. Runtime
    # source changes require fresh qualification evidence before a new cohort.
    for name, expected in manifest['application'].items():
        path = Path(name)
        if (path.suffix in ('.metta', '.lean') and path.parts[0] in ('phase1', 'lib')) or name == 'lean-toolchain':
            assert digest(ROOT / path) == expected, (name, 'requalify changed runtime source')
    duper = subprocess.check_output(['git', 'rev-parse', 'HEAD'],
        cwd=ROOT / 'tools/duper-env/.lake/packages/Duper', text=True).strip()
    assert duper == manifest['duper_revision'] == 'b603c493b09f07b4f7d1a873e5b9b1f60577692c'
    return dict(duper_revision=duper, qualification_input_sha256=key)


def check_existing_inputs(directory, profile, args):
    path = directory / 'inputs.json'
    if path.exists():
        inputs = json.loads(path.read_text())
        assert inputs['profile'] == profile and inputs['full_corpus'] and len(inputs['targets']) == 999
        for name in ('cetta', 'corpus', 'lean', 'vampire'):
            assert inputs['tools'][name] == digest(getattr(args, name)), (profile, name, 'cohort tool differs')
        for name, expected in inputs['application'].items():
            if profile == 'python' and name.startswith('phase1/') and name not in ('phase1/library.metta', 'phase1/itp.metta'):
                # Python loads the pinned oracle, not native search/ATP sources.
                # Its independent checker uses only these two MeTTa modules
                # plus the recorded lib/ Lean sources and unchanged tools.
                continue
            assert digest(ROOT / name) == expected, (profile, name, 'cohort source differs')


def main():
    if sys.flags.optimize:
        raise RuntimeError('qualification checks require Python assertions enabled')
    def interrupted(_signal, _frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta', type=Path, required=True)
    parser.add_argument('--corpus', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--vampire', type=Path, required=True)
    parser.add_argument('--python', type=Path, required=True)
    parser.add_argument('--metta-v4', type=Path, required=True)
    parser.add_argument('--metta-full', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--qualification', type=Path, required=True)
    parser.add_argument('--wait-python-pid', type=int)
    parser.add_argument('--workers', type=int, default=2,
                        help='Workers for newly started cohorts (default: 2)')
    parser.add_argument('--full-discovery', action='store_true',
                        help='Explicitly start the optional exhaustive research comparison')
    args = parser.parse_args()
    if not args.full_discovery:
        parser.error('exhaustive research requires --full-discovery; port acceptance uses qualify_ai_mathematician.py')
    if args.workers < 1:
        parser.error('--workers must be positive')
    for name in ('cetta', 'corpus', 'lean', 'vampire', 'python', 'metta_v4', 'metta_full', 'output', 'qualification'):
        setattr(args, name, getattr(args, name).resolve())
    assert len({args.python, args.metta_v4, args.metta_full, args.output}) == 4, 'cohorts need separate directories'
    qualified_toolchain(args)
    args.output.mkdir(parents=True, exist_ok=True)
    for profile, directory in [('python', args.python), ('PythonV4', args.metta_v4), ('CettaFull', args.metta_full)]:
        toolchain = qualified_toolchain(args)
        check_existing_inputs(directory, profile, args)
        directory.mkdir(parents=True, exist_ok=True)
        receipt = directory / 'toolchain.json'
        if receipt.exists():
            assert json.loads(receipt.read_text())['duper_revision'] == toolchain['duper_revision'], 'cohort Duper pin differs'
        else:
            receipt.write_text(json.dumps(toolchain, indent=2) + '\n')
        if profile == 'python' and args.wait_python_pid:
            print('WAIT python', args.wait_python_pid, flush=True)
            # A resumed producer may have an older summary, and writing a new
            # summary is not its terminal event. Await its lifetime, then check
            # the complete receipt; never start a second producer beside it.
            wait_for_producer(args.wait_python_pid)
        elif not completed_cohort(directory, profile):
            command = [sys.executable, ROOT / 'tests/run_ai_mathematician_discovery.py',
                       '--full-discovery', '--profile', profile, '--cetta', args.cetta, '--corpus', args.corpus,
                       '--lean', args.lean, '--vampire', args.vampire, '--output', directory,
                       '--workers', str(args.workers)]
            if (directory / 'inputs.json').exists():
                command.append('--resume')
            print('START', profile, flush=True)
            run = owned_run(command, env=dict(os.environ, PYTHONUNBUFFERED='1', CETTA_ITP_RUNTIME='native'))
            (args.output / (profile + '.stdout')).write_text(run.stdout)
            (args.output / (profile + '.stderr')).write_text(run.stderr)
            # Exit 1 can mean native attempts exhausted their declared budgets.
            # checked_summary below admits only that explicit observation; all
            # missing goals, operational faults and unknown causes still stop.
            if run.returncode not in (0, 1):
                raise RuntimeError(f'{profile} needs inspection; saved journals remain resumable')
        summary = checked_summary(directory, profile)
        qualified_toolchain(args)
        check_existing_inputs(directory, profile, args)
        print('COMPLETE', profile, json.dumps(summary['counts']), flush=True)
    run = owned_run([sys.executable, ROOT / 'tests/compare_ai_mathematician_discovery.py',
                     '--python', args.python, '--metta-v4', args.metta_v4,
                     '--metta-full', args.metta_full, '--output', args.output])
    (args.output / 'comparison.stdout').write_text(run.stdout)
    (args.output / 'comparison.stderr').write_text(run.stderr)
    if run.returncode:
        raise RuntimeError('cohort comparison failed; inspect its saved output')
    print(run.stdout, end='', flush=True)


if __name__ == '__main__':
    main()
