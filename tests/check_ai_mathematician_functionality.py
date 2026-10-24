#!/usr/bin/env python3
"""Cheap positive/negative controls for qualification evidence reuse."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
from unittest.mock import patch

from check_ai_mathematician_library import ROOT
from qualify_ai_mathematician_functionality import (
    CONTRACT, audit_baseline, audit_contract, audit_inputs, audit_native_closure,
    changed_files, digest, identity, public_symbols)


def rejected(action):
    try:
        action()
    except (AssertionError, KeyError, FileNotFoundError):
        return
    raise AssertionError('invalid evidence was accepted')


def main():
    contract = json.loads(CONTRACT.read_text())
    symbols = audit_contract(contract)
    assert len(symbols) == 25 and sum(map(len, symbols.values())) > 110
    assert public_symbols('class A:\n def f(self): pass\n def _x(self): pass\ndef g(): pass') == {'A', 'A.f', 'g'}
    invalid = copy.deepcopy(contract)
    invalid['capabilities'][0]['python']['library.py'].append('new_unmapped_api')
    rejected(lambda: audit_contract(invalid))
    invalid = copy.deepcopy(contract)
    invalid['experiment_recipes'][0]['files'].append('new_unmapped_experiment.py')
    rejected(lambda: audit_contract(invalid))
    names = set(subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0'))
    audit_native_closure(dict.fromkeys(names))
    rejected(lambda: audit_native_closure(dict.fromkeys(names - {'phase1/proof_plans.metta'})))
    base = ROOT / '.cetta/functionality-controls'
    base.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix='evidence-', dir=base))
    production = {p.relative_to(ROOT).as_posix(): None for folder in ('phase1', 'lib')
                  for p in (ROOT / folder).rglob('*') if p.suffix in ('.metta', '.lean')}
    consulted = []
    def unchanged(paths, root=None):
        consulted.extend(paths)
        assert not any(name.endswith('.lean') or 'foreign-checkout' in name for name in paths)
        return []
    # Historical reports may include another repository's proof gate.
    # Application acceptance neither opens that checkout nor hashes Lean text.
    with patch('qualify_ai_mathematician_functionality.changed_files', side_effect=unchanged):
        needed, changes, _ = audit_inputs(
            dict(tools={str(output / 'cetta'): None}, engine={}), {},
            dict(fixture=dict(runtime=production, tests={}),
                 **{'proof-closure': dict(sources={'foreign-checkout/Missing.lean': 'old'})}),
            dict(impact={}, capabilities=[]))
    assert needed == set() and changes == {} and consulted
    tool = output / 'tool'
    tool.write_text('qualified executable fixture')
    log = output / 'gate.log'
    log.write_text('AiMathematicianFixture 1 0\n')
    inputs = dict(policy=2, tools={str(tool): digest(tool)})
    (output / 'gate.inputs.json').write_text(json.dumps(inputs))
    manifest = dict(tools={str(tool): digest(tool)})
    (output / 'inputs.json').write_text(json.dumps(manifest))
    result = dict(status='qualified', input_manifest='inputs.json',
                  input_manifest_sha256=digest(output / 'inputs.json'), gates=1)
    (output / 'result.json').write_text(json.dumps(result))
    row = dict(gate='fixture', status='passed', exit_code=0, inputs_unchanged=True,
               required_capability_missing=False, input_receipt='gate.inputs.json',
               dependencies_sha256=identity(inputs), log='gate.log', log_sha256=digest(log))
    (output / 'gates.jsonl').write_text(json.dumps(row) + '\n')
    assert audit_baseline(output)[0] == manifest
    assert changed_files(manifest['tools']) == []
    log.write_text('altered log')
    rejected(lambda: audit_baseline(output))
    log.write_text('AiMathematicianFixture 1 0\n')
    tool.write_text('different executable')
    assert changed_files(manifest['tools']) == [str(tool)]
    rejected(lambda: audit_baseline(output))
    tool.write_text('qualified executable fixture')
    (output / 'gates.jsonl').write_text(json.dumps(dict(row, status='failed')) + '\n')
    rejected(lambda: audit_baseline(output))
    (output / 'gates.jsonl').write_text(json.dumps(dict(row, required_capability_missing=True)) + '\n')
    rejected(lambda: audit_baseline(output))
    (output / 'gates.jsonl').write_text(json.dumps(dict(row, dependencies_sha256='forged')) + '\n')
    rejected(lambda: audit_baseline(output))
    print('AiMathematicianFunctionalityControls 15 0')


if __name__ == '__main__':
    main()
