#!/usr/bin/env python3
"""Explicit, resumable Phase 1 qualification; not part of ordinary engine tests.

All integration capabilities are required. This is the port acceptance gate.
Fresh proof discovery is an optional research experiment, not a prerequisite
for acceptance. Passing this command does not establish discovery recall parity.
"""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

from acquire_ai_mathematician_vampire import VERSION, REVISION
from check_ai_mathematician_library import ROOT
from python_oracle import oracle_directory, PYTHON_V4

DUPER_REVISION = 'b603c493b09f07b4f7d1a873e5b9b1f60577692c'
BUILD = ['BUILD=core', 'ENABLE_HTTP=1', 'ENABLE_GMP=1', 'ENABLE_LIB_PROLOG=0']


def digest(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def capture(command, cwd=ROOT):
    return subprocess.check_output(list(map(str, command)), cwd=cwd, text=True).strip()


def source_manifest(root):
    names = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard'], cwd=root).decode().split('\0')
    # Untracked generated logs and private notes are not source dependencies.
    extensions = {'.c', '.h', '.py', '.metta', '.module', '.toml', '.json',
                  '.sexpr', '.expected', '.sh', '.pl', '.txt', '.def', '.inc'}
    return {name: digest(root / name) for name in sorted(set(names)) if name
            and (root / name).is_file() and not name.startswith(('tmp/', 'docs/plans/'))
            and (Path(name).suffix in extensions or Path(name).name in ('Makefile', 'lean-toolchain'))}


def python_dependencies(script):
    paths = {}
    def visit(path):
        if str(path) in paths:
            return
        paths[str(path)] = digest(path)
        for node in ast.walk(ast.parse(path.read_text())):
            modules = ([node.module] if isinstance(node, ast.ImportFrom) else
                       [alias.name for alias in node.names] if isinstance(node, ast.Import) else [])
            for module in modules:
                if module:
                    local = ROOT / 'tests' / (module.split('.')[0] + '.py')
                    if local.is_file():
                        visit(local)
    visit(script)
    return paths


def main():
    def interrupted(_signal, _frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta', type=Path, required=True)
    parser.add_argument('--engine-source', type=Path, required=True)
    parser.add_argument('--corpus', type=Path, required=True)
    parser.add_argument('--vampire', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--zipper', type=Path, default=ROOT / 'tools/duper-env/.lake/packages/auto/.lake/build/zipperposition.exe')
    parser.add_argument('--output', type=Path, default=ROOT / '.cetta/qualification')
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    if sys.flags.optimize:
        parser.error('qualification requires Python assertions to be enabled')
    for name in ('cetta', 'vampire', 'zipper'):
        setattr(args, name, Path(shutil.which(str(getattr(args, name))) or getattr(args, name)))
    lean_command = shutil.which(str(args.lean)) or str(args.lean)
    args.lean = Path(capture([lean_command, '--print-prefix'])) / 'bin/lean'
    for name in ('cetta', 'engine_source', 'corpus', 'vampire', 'lean', 'zipper', 'output'):
        setattr(args, name, getattr(args, name).resolve())
    args.output.mkdir(parents=True, exist_ok=True)
    driver_source = Path(__file__).read_bytes()
    driver_snapshot = args.output / ('driver-' + hashlib.sha256(driver_source).hexdigest() + '.py')
    if not driver_snapshot.exists():
        driver_snapshot.write_bytes(driver_source)
    engine_version = capture([args.cetta, '--version'])
    lean_version = capture([args.lean, '--version'])
    vampire_version = capture([args.vampire, '--version'])
    assert '(core)' in engine_version, 'qualification requires a core engine'
    assert 'version 4.34.0,' in lean_version, lean_version
    assert 'Vampire ' + VERSION in vampire_version and REVISION[:7] in vampire_version, vampire_version
    assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.0'
    duper_manifest = json.loads((ROOT / 'tools/duper-env/lake-manifest.json').read_text())
    assert any(p['name'] == 'Duper' and p['rev'] == DUPER_REVISION for p in duper_manifest['packages'])
    assert capture(['git', 'rev-parse', 'HEAD'], ROOT / 'tools/duper-env/.lake/packages/Duper') == DUPER_REVISION
    assert (ROOT / '.cetta/lean-native/itp-worker').is_file(), 'run make prepare-cetta-itp-native first'
    assert (ROOT / '.cetta/lean-native/itp-guard').is_file(), 'native independent guard is required'
    assert shutil.which('bwrap') and shutil.which('flock'), 'isolation and worker-lock tools are required'
    oracle = oracle_directory()
    files = [args.cetta, args.lean, args.vampire, args.zipper, args.corpus,
             ROOT / '.cetta/lean-native/itp-worker', ROOT / '.cetta/lean-native/itp-guard']
    frozen = dict(application=source_manifest(ROOT), engine=source_manifest(args.engine_source),
                  tools={str(path): digest(path) for path in files},
                  versions=dict(cetta=engine_version, lean=lean_version, vampire=vampire_version),
                  python_revision=PYTHON_V4, duper_revision=DUPER_REVISION,
                  oracle={p.name: digest(p) for p in oracle.glob('*.py')},
                  build=BUILD, paid_model_calls=False)
    initial_digest = hashlib.sha256(json.dumps(frozen, sort_keys=True).encode()).hexdigest()
    manifest_path = args.output / ('inputs-' + initial_digest + '.json')
    if not manifest_path.exists():
        with manifest_path.open('x') as destination:
            json.dump(frozen, destination, indent=2)
            destination.write('\n')
    journal = args.output / 'gates.jsonl'
    if journal.exists() and not args.resume:
        parser.error('existing gate journal: use --resume or another output directory')
    done = {}
    if args.resume and journal.exists():
        for line in journal.read_text().splitlines():
            row = json.loads(line)
            if row['status'] == 'passed':
                done[row['gate']] = row
    env = dict(os.environ, CETTA_ITP_RUNTIME='native', PYTHONUNBUFFERED='1')
    gates = []
    def gate(name, command, cwd=ROOT, application=True):
        gates.append((name, list(map(str, command)), cwd, application))
    def app(name, extra=()):
        gate(name, [sys.executable, ROOT / ('tests/check_ai_mathematician_' + name + '.py'), '--cetta', args.cetta, *extra])
    corpus = ['--corpus', args.corpus]
    lean = ['--lean', args.lean]
    solver = ['--vampire', args.vampire]
    app('library', [*corpus, '--generated', '256', '--oracle-library', oracle / 'library.py'])
    app('search', [*corpus, '--check-recall'])
    app('score_schedule', corpus)
    app('atp', [*corpus, *solver, '--generated', '256'])
    app('ranked_bridge', [*corpus, '--all'])
    app('induction', [*corpus, '--all'])
    app('itp', [*corpus, *lean])
    app('prover', [*corpus, *lean, *solver])
    app('reconstruction', [*corpus, *lean, *solver, '--duper'])
    app('smt', [*corpus, *lean, *solver])
    app('workers', [*corpus, *lean, *solver, '--real'])
    app('experiment', [*corpus, *lean, *solver, '--duper'])
    app('isolation', [*corpus, *lean])
    app('vampire_output')
    app('lean_export', [*corpus, *lean])
    app('proof_advice', [*corpus, *solver])
    app('llm', [*corpus, *lean, *solver, '--http-cetta', args.cetta])
    app('signature_feedback', [*corpus, *lean])
    app('embeddings')
    app('upstream')
    app('replay', [*corpus, *lean])
    app('published', [*corpus, *lean, '--input', str(ROOT / 'results/proof_bundle.jsonl'),
                      '--workers', '2', '--output', str(args.output / 'published'), '--resume'])
    app('discovery', [*corpus, *lean])
    app('research', [*corpus, *lean, *solver, '--zipper', args.zipper, '--require-integrations'])
    gate('engine-basic', ['make', *BUILD, 'test'], args.engine_source, False)
    gate('engine-focused', ['make', *BUILD, 'test-regex-v1', 'test-collection-ingress',
                           'test-collection-keys', 'test-postings-fold'], args.engine_source, False)
    def dependencies(name, command, application):
        tools = {str(path): digest(path) for path in files}
        engine_sources = source_manifest(args.engine_source)
        if not application:
            return dict(policy=2, tools=tools, sources=engine_sources)
        app_sources = source_manifest(ROOT)
        runtime = {key: value for key, value in app_sources.items()
                   if key.startswith(('phase1/', 'lib/', 'tools/duper-env/', 'tests/fixtures/', 'tests/metta/'))
                   or key == 'lean-toolchain'}
        assets = {key: value for key, value in engine_sources.items()
                  if key.startswith(('lib/', 'langdef/', 'src/', 'native/'))}
        inputs = dict(policy=2, tools=tools, runtime=runtime, engine=assets,
                      tests=python_dependencies(Path(command[1])),
                      oracle=frozen['oracle'], command=command)
        if name == 'published':
            inputs['published'] = {filename: digest(ROOT / 'results' / filename) for filename in
                                   ('llm_proofs_verified.json', 'v6v7_verified.json', 'v8v9_verified.json',
                                    'proof_bundle.jsonl')}
        return inputs
    def identity(value):
        return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()
    for name, command, cwd, application in gates:
        before = dependencies(name, command, application)
        key = identity(before)
        receipt = args.output / (name + '-' + key + '.inputs.json')
        if not receipt.exists():
            receipt.write_text(json.dumps(before, indent=2) + '\n')
        if name in done and done[name].get('dependencies_sha256') == key:
            assert digest(args.output / done[name]['log']) == done[name]['log_sha256'], 'qualified log changed'
            print('REUSE', name, flush=True)
            continue
        started = time.time()
        print('START', name, flush=True)
        log = args.output / (name + '-' + str(time.time_ns()) + '.log')
        with log.open('w') as output:
            child = subprocess.Popen(command, cwd=cwd, env=env, stdout=output, stderr=subprocess.STDOUT,
                                     start_new_session=True)
            # No overall ten-minute timeout: individual policies own their
            # semantic budgets; the parent remains interruptible.
            try:
                status = child.wait()
            except BaseException:
                if child.poll() is None:
                    os.killpg(child.pid, signal.SIGTERM)
                    try:
                        child.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(child.pid, signal.SIGKILL)
                        child.wait()
                raise
        transcript = log.read_text(errors='replace')
        missing = application and ('IntegrationSkipped' in transcript or re.search(r'^SKIP', transcript, re.M))
        summaries = re.findall(r'^AiMathematician\w+\s+\d+\s+0\s*$', transcript, re.M)
        if name == 'smt':
            summaries += re.findall(r'^AiSMT\s+\d+/0\s*$', transcript, re.M)
        good = status == 0 and not missing and (not application or bool(summaries))
        unchanged = before == dependencies(name, command, application)
        good = good and unchanged
        row = dict(gate=name, command=executed_command, status='passed' if good else 'failed',
                   dependencies_sha256=key, input_receipt=receipt.name, log=log.name,
                   exit_code=status, seconds=time.time() - started, inputs_unchanged=unchanged,
                   required_capability_missing=bool(missing), summaries=summaries,
                   log_sha256=digest(log))
        with journal.open('a') as output:
            output.write(json.dumps(row) + '\n')
            output.flush()
            os.fsync(output.fileno())
        print(row['status'].upper(), name, round(row['seconds'], 2), flush=True)
        if not good:
            raise RuntimeError(f'{name} did not qualify; inspect {log}')
        done[name] = row
    for name, command, _, application in gates:
        assert done[name]['dependencies_sha256'] == identity(dependencies(name, command, application)), (
            name, 'dependencies changed after this gate; resume to recheck affected gates')
    result = dict(status='qualified', gates=len(gates), input_manifest=manifest_path.name,
                  input_manifest_sha256=digest(manifest_path),
                  scope='phase1-port-conformance', full_discovery_required=False,
                  discovery='not established by this gate', omissions=['paid model calls', 'non-production build configurations'])
    (args.output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print('AiMathematicianQualification', len(gates), 0, flush=True)


if __name__ == '__main__':
    main()
