#!/usr/bin/env python3
"""Build/check a staged source export with no application build artifacts.

The external engine, Lean toolchain and pinned Duper package cache are explicit
inputs. Python oracle sources come from named Git commits and are copied into
the export; its application source is read exclusively from the staging index.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import sys

from check_ai_mathematician_library import ROOT
from python_oracle import oracle_directory, PYTHON_V4, UPSTREAM_V9


def digest(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta', type=Path, required=True)
    parser.add_argument('--corpus', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--vampire', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    for name in ('cetta', 'corpus', 'lean', 'vampire'):
        setattr(args, name, getattr(args, name).resolve())
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=False)
    source = args.output / 'source'
    source.mkdir()
    names = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
    entries = {}
    for name in sorted(set(filter(None, names))):
        # Documentation and published scripts are source inputs too; ignored
        # caches and binaries cannot enter through git ls-files.
        content = subprocess.check_output(['git', 'show', ':' + name], cwd=ROOT)
        live = ROOT / name
        if not live.is_file() or live.read_bytes() != content:
            raise ValueError('staged/live mismatch: ' + name)
        destination = source / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(content)
        destination.chmod(live.stat().st_mode & 0o777)
        entries[name] = hashlib.sha256(content).hexdigest()
    # Source closure includes newer published-script and feedback consumers.
    for name in ('phase1/lean_sigs.py', 'results/v8v9_verified.json',
                 'tests/check_ai_mathematician_signature_feedback.py'):
        assert name in entries, 'missing staged dependency: ' + name
    oracle_roots = {}
    for revision in (PYTHON_V4, UPSTREAM_V9):
        original = oracle_directory(revision)
        target = source / '.cetta/python-oracles' / revision
        (target / 'phase1').mkdir(parents=True)
        for path in original.glob('*.py'):
            shutil.copy2(path, target / 'phase1' / path.name)
        for name in ('lib', 'tools'):
            (target / name).symlink_to(source / name, target_is_directory=True)
        oracle_roots[revision] = {path.name: digest(path) for path in (target / 'phase1').glob('*.py')}
    packages = ROOT / 'tools/duper-env/.lake/packages'
    destination = source / 'tools/duper-env/.lake/packages'
    destination.parent.mkdir(parents=True)
    destination.symlink_to(packages, target_is_directory=True)
    manifest = dict(sources=entries, python_oracles=oracle_roots,
                    tools={str(path.resolve()): digest(path) for path in
                           (args.cetta, args.lean, args.vampire, args.corpus)},
                    external_packages='pinned Duper, auto and batteries',
                    application_build_artifacts_copied=False)
    (args.output / 'sources.json').write_text(json.dumps(manifest, indent=2) + '\n')
    with (args.output / 'build.log').open('w') as log:
        subprocess.run(['make', '-j2', 'prepare-cetta-itp-native', 'LEAN=' + str(args.lean.resolve())],
                       cwd=source, stdout=log, stderr=subprocess.STDOUT, check=True)
    # The oracle data is already verified above. Redirect only its data lookup,
    # not application functions or the independent checker being exercised.
    sys.path.insert(0, str(source / 'tests'))
    for name in list(sys.modules):
        if name.startswith(('check_ai_mathematician_', 'python_oracle', 'typed_export_oracle')):
            del sys.modules[name]
    import python_oracle as exported_oracle
    exported_oracle.oracle_directory = lambda revision=PYTHON_V4: source / '.cetta/python-oracles' / revision / 'phase1'
    os.environ['CETTA_ITP_RUNTIME'] = 'native'
    os.chdir(source)
    for name, extra in [
        ('library', ['--corpus', str(args.corpus.resolve()), '--oracle-library',
                     str(source / '.cetta/python-oracles' / PYTHON_V4 / 'phase1/library.py')]),
        ('itp', ['--corpus', str(args.corpus.resolve()), '--lean', str(args.lean.resolve())]),
        ('embeddings', []),
    ]:
        sys.argv = [name, '--cetta', str(args.cetta.resolve()), *extra]
        runpy.run_path(str(source / 'tests' / ('check_ai_mathematician_' + name + '.py')), run_name='__main__')
    for name, wanted in entries.items():
        assert digest(source / name) == wanted, 'exported source mutated: ' + name
    (args.output / 'result.json').write_text(json.dumps(dict(status='qualified', source_files=len(entries)), indent=2) + '\n')
    print('AiMathematicianSourceClosure', len(entries), 0, flush=True)


if __name__ == '__main__':
    main()
