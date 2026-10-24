#!/usr/bin/env python3
"""Audit Phase 1 coverage and refresh only invalidated, bounded checks.

A successful earlier qualification supplies the expensive deterministic and
independent-witness evidence. Logs, tool binaries, source inputs and published
witnesses are checked before reuse. Unclassified runtime changes require a new
impact decision; this command never starts a discovery run or a broad sweep.
"""
import argparse
import ast
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

from check_ai_mathematician_library import ROOT
from qualify_ai_mathematician import digest, python_dependencies


CONTRACT = ROOT / 'tests/phase1_functionality.json'
BOUNDED = {'itp', 'experiment', 'workers', 'llm', 'signature_feedback', 'upstream',
           'discovery', 'proof_advice', 'research'}
BUILD_INPUTS = {'lib/gslt_execution_contracts.metta'}


def identity(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def changed_files(expected, root=None):
    changed = []
    for name, wanted in expected.items():
        path = (root / name) if root else Path(name)
        if not path.is_file() or digest(path) != wanted:
            changed.append(name)
    return changed


def public_symbols(source):
    symbols = set()
    for node in ast.parse(source).body:
        if isinstance(node, (ast.FunctionDef, ast.ClassDef)) and not node.name.startswith('_'):
            symbols.add(node.name)
            if isinstance(node, ast.ClassDef):
                symbols.update(node.name + '.' + child.name for child in node.body
                               if isinstance(child, ast.FunctionDef) and not child.name.startswith('_'))
    return symbols


def audit_contract(contract):
    assert contract['schema'] == 'ai-math.phase1-functionality.v1'
    ids = [item['id'] for item in contract['capabilities']]
    assert len(ids) == len(set(ids)) and ids
    mapped = {}
    for item in contract['capabilities']:
        assert item['gates'] and item['native'], item['id']
        for name, symbols in item['python'].items():
            mapped.setdefault(name, set()).update(symbols)
        for name, symbols in item['native'].items():
            text = (ROOT / name).read_text()
            for symbol in symbols:
                assert re.search(r'\(=\s*\(' + re.escape(symbol) + r'(?:\s|\))', text), (item['id'], symbol)
    for name, described in mapped.items():
        reference = subprocess.check_output(['git', 'show',
            contract['python_revision'] + ':phase1/' + name], cwd=ROOT, text=True)
        actual = public_symbols(reference)
        assert actual == described, (name, 'unmapped', sorted(actual - described),
                                     'not public', sorted(described - actual))
    # Every upstream experiment is either a distinct algorithm or a recipe
    # over the listed capabilities. No growing directory can silently escape.
    algorithms = {name.removeprefix('experiments/') for name in mapped if name.startswith('experiments/')}
    recipes = [name for group in contract['experiment_recipes'] for name in group['files']]
    assert len(recipes) == len(set(recipes)) and not algorithms.intersection(recipes)
    for group in contract['experiment_recipes']:
        assert set(group['capabilities']) <= set(ids), group
    original = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only',
        contract['python_revision'], 'phase1/experiments'], cwd=ROOT, text=True)
    expected = {Path(name).name for name in original.splitlines() if name.endswith('.py')}
    assert algorithms | set(recipes) == expected, ('unmapped experiments', expected - algorithms - set(recipes))
    return {name: sorted(symbols) for name, symbols in mapped.items()}


def audit_baseline(directory):
    result_path = directory / 'result.json'
    result = json.loads(result_path.read_text())
    assert result['status'] == 'qualified', 'baseline did not qualify'
    manifest = directory / result['input_manifest']
    assert digest(manifest) == result['input_manifest_sha256'], 'baseline input manifest changed'
    frozen = json.loads(manifest.read_text())
    assert not changed_files(frozen['tools']), 'qualified binary, checker, corpus or solver changed'
    rows = {}
    for line in (directory / 'gates.jsonl').read_text().splitlines():
        row = json.loads(line)
        rows[row['gate']] = row
    assert len(rows) == result['gates'], 'baseline gate count mismatch'
    inputs = {}
    for name, row in rows.items():
        assert row['status'] == 'passed' and row['exit_code'] == 0, name
        assert row['inputs_unchanged'] and not row['required_capability_missing'], name
        assert digest(directory / row['log']) == row['log_sha256'], (name, 'log changed')
        dependency = json.loads((directory / row['input_receipt']).read_text())
        assert identity(dependency) == row['dependencies_sha256'], (name, 'receipt changed')
        inputs[name] = dependency
    return frozen, rows, inputs


def audit_inputs(frozen, rows, inputs, contract):
    required = set()
    changes = {}
    runtime_rosters = []
    for name, dependency in inputs.items():
        if 'runtime' not in dependency:
            continue
        runtime_rosters.append(set(dependency['runtime']))
        # Lean source edits do not alter an already compiled checker. Its
        # executable identity is checked separately; building proofs belongs
        # to Lean/the owning repository, not to source-text fingerprints.
        changed = changed_files({path: value for path, value in dependency['runtime'].items()
                                 if not path.endswith('.lean')}, ROOT)
        for path in changed:
            assert path in contract['impact'], ('unclassified runtime change', path,
                'run the relevant focused checks and update the impact contract before reuse')
            required.update(contract['impact'][path])
            changes[path] = contract['impact'][path]
        if changed_files(dependency['tests']):
            required.add(name)
        if 'published' in dependency:
            assert not changed_files(dependency['published'], ROOT / 'results'), 'published witnesses changed'
    assert runtime_rosters and all(roster == runtime_rosters[0] for roster in runtime_rosters)
    # New native production modules cannot evade the baseline's file-by-file audit.
    production = {p.relative_to(ROOT).as_posix() for folder in ('phase1', 'lib')
                  for p in (ROOT / folder).rglob('*')
                  if p.is_file() and p.suffix in ('.metta', '.lean')}
    added = production - runtime_rosters[0]
    assert added <= contract['impact'].keys(), ('unclassified new runtime input', sorted(added - contract['impact'].keys()))
    for path in added:
        required.update(contract['impact'][path])
        changes[path] = contract['impact'][path]
    # Runtime data is distinct from a newer checkout's compile-time inputs.
    # The exact native executable is already bound above; no claim about a
    # rebuild of the current engine source follows from this evidence reuse.
    engine = next(Path(path).parent for path in frozen['tools'] if Path(path).name == 'cetta')
    assets = {name: value for name, value in frozen['engine'].items()
              if name.startswith(('lib/', 'formats/')) and name not in BUILD_INPUTS}
    assert not changed_files(assets, engine), 'engine runtime library/grammar changed'
    for item in contract['capabilities']:
        assert set(item['gates']) <= rows.keys() | BOUNDED, ('missing capability evidence', item['id'])
        required.update(set(item['gates']) - rows.keys())
    assert required <= BOUNDED, ('additional relevant qualification required', sorted(required - BOUNDED))
    return required, changes, engine


def live_inputs(frozen, dependencies, contract, zipper):
    runtime = set(next(row['runtime'] for row in dependencies.values() if 'runtime' in row)) | contract['impact'].keys()
    return dict(contract=digest(CONTRACT), qualifier=digest(Path(__file__)),
                runtime={name: digest(ROOT / name) for name in runtime if not name.endswith('.lean')},
                tools={name: digest(Path(name)) for name in frozen['tools']},
                extra_tools={str(zipper): digest(zipper)},
                tests={name: python_dependencies(ROOT / ('tests/check_ai_mathematician_' + name + '.py'))
                       for name in BOUNDED})


def audit_native_closure(sources):
    production = {path.relative_to(ROOT).as_posix() for folder in ('phase1', 'lib')
                  for path in (ROOT / folder).rglob('*')
                  if path.is_file() and path.suffix in ('.metta', '.lean')}
    assert production <= sources.keys(), ('unstaged runtime dependency', sorted(production - sources.keys()))
    for name in production:
        if not name.endswith('.metta'):
            continue
        for dependency in re.findall(r'^!\(import!\s+&self\s+"([^"\n]+\.metta)"\)',
                                     (ROOT / name).read_text(), re.M):
            resolved = (ROOT / name).parent / dependency
            relative = resolved.resolve().relative_to(ROOT).as_posix()
            assert relative in sources, ('missing staged import', name, dependency)


def staged_sources():
    assert subprocess.run(['git', 'diff', '--quiet'], cwd=ROOT).returncode == 0, 'stage the qualified application changes first'
    names = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
    # Keep Lean files in the commit's dependency inventory without hashing
    # their source text as a substitute for checking compiled proof terms.
    sources = {name: (None if name.endswith('.lean') else digest(ROOT / name)) for name in names if name}
    audit_native_closure(sources)
    for name in ('tests/phase1_functionality.json', 'tests/qualify_ai_mathematician_functionality.py',
                 'tests/check_ai_mathematician_functionality.py', 'cetta-research.example.json'):
        assert name in sources, ('unstaged dependency', name)
    return sources


def gate_inputs(name, snapshot, contract):
    # The executed sources, tools and test dependencies determine reuse.
    # Adding a capability to the inventory is not a reason to rerun other gates.
    return dict(tools=dict(snapshot['tools'], **(snapshot['extra_tools'] if name == 'research' else {})),
                tests=snapshot['tests'][name],
                runtime={path: value for path, value in snapshot['runtime'].items()
                         if path not in contract['impact'] or name in contract['impact'][path]})


def run_gate(name, command, output, snapshot):
    assert name in BOUNDED
    assert Path(command[1]).resolve() == ROOT / ('tests/check_ai_mathematician_' + name + '.py')
    command = [sys.executable, *command[1:]]
    key = identity(dict(gate=name, command=command, inputs=snapshot))
    receipt_path = output / (name + '-' + key + '.json')
    if not receipt_path.exists():
        # An orchestration-only edit does not change the tested program.
        # Earlier receipts included that metadata in their cache key.
        for path in sorted(output.glob(name + '-*.json')):
            prior = json.loads(path.read_text())
            semantic_inputs = {field: value for field, value in prior.get('inputs', {}).items()
                               if field not in ('qualifier', 'contract')}
            if (prior.get('gate') == name and prior.get('command') == command and
                    prior.get('status') == 'passed' and semantic_inputs == snapshot):
                assert digest(output / prior['log']) == prior['log_sha256'], 'focused log changed'
                prior.update(inputs=snapshot, reused_from=dict(receipt=path.name, sha256=digest(path)))
                receipt_path.write_text(json.dumps(prior, indent=2) + '\n')
                break
    if receipt_path.exists():
        receipt = json.loads(receipt_path.read_text())
        assert receipt['inputs'] == snapshot and receipt['status'] == 'passed'
        assert digest(output / receipt['log']) == receipt['log_sha256'], 'focused log changed'
        print('REUSE focused', name, flush=True)
        return receipt
    log = output / (name + '-' + key + '.log')
    print('CHECK', name, flush=True)
    start = time.monotonic()
    with log.open('w') as destination:
        child = subprocess.Popen(command, cwd=ROOT, stdout=destination, stderr=subprocess.STDOUT,
                                 env=dict(os.environ, CETTA_ITP_RUNTIME='native'), start_new_session=True)
        try:
            code = child.wait()
        except BaseException:
            if child.poll() is None:
                try:
                    os.killpg(child.pid, signal.SIGTERM)
                    child.wait(timeout=5)
                except ProcessLookupError:
                    child.wait()
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL)
                    child.wait()
            raise
    text = log.read_text()
    assert code == 0 and 'IntegrationSkipped' not in text and not re.search(r'^SKIP', text, re.M), (name, log)
    assert re.search(r'^AiMathematician\w+\s+\d+\s+0\s*$', text, re.M), (name, 'missing summary')
    receipt = dict(gate=name, command=command, status='passed', inputs=snapshot,
                   log=log.name, log_sha256=digest(log), seconds=time.monotonic() - start)
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
    print('PASS', name, round(receipt['seconds'], 2), flush=True)
    return receipt


def main():
    def interrupted(_signal, _frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=ROOT / '.cetta/functional-qualification')
    parser.add_argument('--audit-only', action='store_true', help='Report invalidated checks without executing them')
    parser.add_argument('--zipper', type=Path, default=ROOT / 'tools/duper-env/.lake/packages/auto/.lake/build/zipperposition.exe')
    args = parser.parse_args()
    if sys.flags.optimize:
        parser.error('qualification requires Python assertions')
    contract = json.loads(CONTRACT.read_text())
    symbols = audit_contract(contract)
    frozen, rows, dependencies = audit_baseline(args.baseline.resolve())
    required, changes, engine = audit_inputs(frozen, rows, dependencies, contract)
    zipper = args.zipper.resolve()
    assert zipper.is_file(), 'Zipperposition is required for experimental-algorithm qualification'
    snapshot = live_inputs(frozen, dependencies, contract, zipper)
    if args.audit_only:
        print(json.dumps(dict(capabilities=len(contract['capabilities']), changes=changes,
                              required_checks=sorted(required)), indent=2))
        return
    staged = staged_sources()
    args.output.mkdir(parents=True, exist_ok=True)
    commands = {name: row['command'] for name, row in rows.items()}
    integration = rows['itp']['command']
    commands['research'] = [sys.executable, str(ROOT / 'tests/check_ai_mathematician_research.py'),
        *[value for flag in ('--cetta', '--corpus', '--lean')
          for value in (flag, integration[integration.index(flag) + 1])],
        '--zipper', str(zipper), '--vampire', rows['llm']['command'][rows['llm']['command'].index('--vampire') + 1],
        '--require-integrations']
    receipts = {name: run_gate(name, commands[name], args.output, gate_inputs(name, snapshot, contract))
                for name in sorted(required)}
    assert live_inputs(frozen, dependencies, contract, zipper) == snapshot, 'inputs changed during qualification'
    # Re-audit reused evidence after the bounded work as well.
    audit_baseline(args.baseline.resolve())
    audit_inputs(frozen, rows, dependencies, contract)
    assert staged_sources() == staged, 'staged application sources changed during qualification'
    completed = [dict(item, status='qualified', evidence={name: (
        dict(kind='focused', log=receipts[name]['log'], sha256=receipts[name]['log_sha256']) if name in receipts
        else dict(kind='reused', log=rows[name]['log'], sha256=rows[name]['log_sha256']))
        for name in item['gates']}) for item in contract['capabilities']]
    result = dict(schema='ai-math.functional-qualification.v1', status='qualified',
                  scope=contract['scope'], qualified_at=datetime.now(timezone.utc).isoformat(),
                  capabilities=completed, public_python_symbols=symbols, semantics=contract['semantics'],
                  separate_research=contract['separate_research'], inputs=snapshot,
                  staged_sources=staged,
                  baseline=dict(directory=str(args.baseline.resolve()), result_sha256=digest(args.baseline / 'result.json')),
                  reused_gates=sorted(rows.keys() - required - {'proof-closure'}), refreshed_gates=sorted(required),
                  engine_artifact=str(engine / 'cetta'), current_engine_source_rebuild_qualified=False,
                  paid_model_calls=False, full_discovery_required=False, full_discovery_recall_parity_claimed=False)
    (args.output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print('AiMathematicianFunctionality', len(completed), '0', flush=True)


if __name__ == '__main__':
    main()
