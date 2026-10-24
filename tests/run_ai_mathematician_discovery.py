#!/usr/bin/env python3
"""Run optional proof-discovery research with durable evidence.

This experiment is separate from port acceptance. Full-corpus search requires
an explicit --full-discovery request; --goals selects a diagnostic subset.

Python's search/prover algorithms are loaded unchanged from the pinned oracle.
The adapter supplies tool paths, canonical set iteration, process ownership and
observations. Every claimed success is independently checked through CeTTa's
Lean boundary before it is recorded as proved. Native profiles use the existing
resumable MeTTa workers and are independently replayed after their run.
"""
import argparse
import functools
import hashlib
import importlib
import inspect
import json
import multiprocessing
import os
from pathlib import Path
import signal
import shutil
import subprocess
import sys
import tempfile
import time

from check_ai_mathematician_library import ROOT, quote
from check_ai_mathematician_atp import read_values
from check_ai_mathematician_itp import prelude as checker_prelude
from check_ai_mathematician_search import load_reference, reference_decls
from python_oracle import oracle_directory, PYTHON_V4


def digest(path):
    with Path(path).open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def append(path, value):
    with path.open('a') as output:
        output.write(json.dumps(value, ensure_ascii=True) + '\n')
        output.flush()
        os.fsync(output.fileno())


def stop(child):
    if child.poll() is None:
        os.killpg(child.pid, signal.SIGTERM)
        try:
            child.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid, signal.SIGKILL)
            child.wait()


def owned_run(command, *, timeout=None, env=None, cwd=ROOT):
    child = subprocess.Popen(list(map(str, command)), cwd=cwd, env=env,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True, start_new_session=True)
    try:
        stdout, stderr = child.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as failure:
        stop(child)
        stdout, stderr = child.communicate()
        failure.stdout, failure.stderr = stdout, stderr
        raise
    except BaseException:
        stop(child)
        raise
    return subprocess.CompletedProcess(command, child.returncode, stdout, stderr)


def independent_check(config, goal, tactic, profile, output, budget=None):
    output.mkdir(parents=True, exist_ok=True)
    budget = budget or dict(timeout=300, heartbeats=1000000)
    source = checker_prelude() + f'''
!(let* (($decls (ai-math:load-library {quote(config['corpus'])}))
        ($base (ai-math:itp $decls {quote(ROOT)} {quote(config['lean'])}))
        ($context (ai-math:itp-select-profile $base {profile})))
   (ai-math:itp-check-with $context {quote(goal)} {quote(tactic)}
     (AiITP:Budget {int(budget['timeout'] * 1000)} {budget['heartbeats']} 8000)))
'''
    script = output / 'recheck.metta'
    script.write_text(source)
    run = owned_run([config['cetta'], '--lang', 'petta@1.0.6', script],
                    env=dict(os.environ, CETTA_ITP_RUNTIME='native'))
    (output / 'stdout.log').write_text(run.stdout)
    (output / 'stderr.log').write_text(run.stderr)
    if run.returncode:
        return dict(outcome='fault', detail=['checker-process', run.returncode, run.stderr])
    values = read_values(run.stdout)
    if values[:5] != ['true'] * 5 or len(values) != 6:
        return dict(outcome='fault', detail=['checker-protocol', run.stdout[:1000]])
    result = values[-1]
    if result[:2] == ['AiITP:Accepted', goal]:
        return dict(outcome='proved', used=result[2], axioms=result[3],
                    independent_check='kernel-statement-and-source-order')
    return dict(outcome='unfinished' if result[0] == 'AiITP:Unfinished' else 'fault', detail=result)


class ProcessObserver:
    def __init__(self):
        self.output = None
        self.count = 0

    def run(self, command, **kwargs):
        assert kwargs.get('capture_output') and kwargs.get('text'), kwargs
        assert set(kwargs) <= {'capture_output', 'text', 'timeout', 'env'}, kwargs
        self.count += 1
        output = self.output / f'process-{self.count:04d}'
        output.mkdir()
        # Keep the exact generated input before the oracle retires its file.
        argument = Path(command[-1])
        if argument.is_file():
            (output / ('input' + argument.suffix)).write_bytes(argument.read_bytes())
        started = time.monotonic_ns()
        try:
            result = owned_run(command, timeout=kwargs.get('timeout'), env=kwargs.get('env'))
        except subprocess.TimeoutExpired as failure:
            (output / 'stdout.log').write_text(failure.stdout or '')
            (output / 'stderr.log').write_text(failure.stderr or '')
            append(self.output / 'processes.jsonl', dict(process=output.name, command=command,
                timeout=kwargs.get('timeout'), outcome='timeout', elapsed_ns=time.monotonic_ns() - started))
            raise
        (output / 'stdout.log').write_text(result.stdout)
        (output / 'stderr.log').write_text(result.stderr)
        append(self.output / 'processes.jsonl', dict(process=output.name, command=command,
            timeout=kwargs.get('timeout'), outcome='exited', returncode=result.returncode,
            elapsed_ns=time.monotonic_ns() - started))
        return result

    def __getattr__(self, name):
        return getattr(subprocess, name)


def prior_results(directory, pattern):
    results = {}
    for path in sorted(directory.glob(pattern)):
        lines = path.read_text().splitlines()
        for index, line in enumerate(lines):
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                if index != len(lines) - 1:
                    raise
                # A torn final record is retained, not interpreted as a result.
                continue
            if 'goal' in row and 'outcome' in row:
                results[row['goal']] = row
    return results


def python_worker(config, shard, targets):
    def interrupted(_signal, _frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    directory = Path(config['output'])
    invocation = str(time.time_ns())
    journal = directory / f'worker-{shard}-{invocation}.jsonl'
    work = directory / f'worker-{shard}-{invocation}'
    work.mkdir()
    scratch = work / 'temporary'
    scratch.mkdir()
    os.environ['LEAN_BIN'] = config['lean']
    os.environ['TMPDIR'] = str(scratch)
    tempfile.tempdir = str(scratch)
    library, Search = load_reference(oracle_directory())
    declarations = reference_decls(library, Path(config['corpus']))
    module = importlib.import_module('prover')
    atp = importlib.import_module('atp')
    itp = importlib.import_module('itp')
    module.Search = Search
    module.LEAN = itp.LEAN = config['lean']
    atp.VAMPIRE = config['vampire']
    observer = ProcessObserver()
    module.subprocess = atp.subprocess = observer
    original_tempfile = tempfile.NamedTemporaryFile
    class OwnedTemporaries:
        @staticmethod
        def NamedTemporaryFile(*args, **kwargs):
            kwargs['dir'] = str(scratch)
            return original_tempfile(*args, **kwargs)
    module.tempfile = atp.tempfile = OwnedTemporaries
    original_batch = module.Prover.attempt_batch
    signature = inspect.signature(original_batch)

    class ObservedProver(module.Prover):
        @functools.wraps(original_batch)
        def attempt_batch(self, goal, cands, *args, **kwargs):
            bound = signature.bind(self, goal, cands, *args, **kwargs)
            bound.apply_defaults()
            budget = {key: value for key, value in bound.arguments.items() if key not in ('self', 'goal', 'cands')}
            self.batch_number += 1
            batch = self.batch_number
            append(self.trace / 'attempts.jsonl', dict(batch=batch, stage='begin',
                   goal=goal.name, candidates=cands, policy=budget))
            started = time.monotonic_ns()
            results = original_batch(self, goal, cands, *args, **kwargs)
            append(self.trace / 'attempts.jsonl', dict(batch=batch, stage='complete',
                   results=results, elapsed_ns=time.monotonic_ns() - started))
            scripts = dict(cands)
            for label, accepted, _ in results:
                if accepted:
                    self.successes.append((label, scripts[label], budget))
            return results

    prover = ObservedProver(declarations, config['corpus'], itp.load_statements(str(ROOT / 'lib/MegLib.lean')))
    assert prover.use_duper, 'pinned Duper environment is required'
    prior = prior_results(directory, 'worker-*.jsonl')
    by_name = {d.name: d for d in declarations}
    for name in targets:
        goal = by_name[name]
        trace = work / str(goal.index)
        trace.mkdir()
        old = prior.get(name)
        if old and old['outcome'] in ('proved', 'not-proved'):
            row = dict(old, resumed=True)
            if row['outcome'] == 'proved':
                row.update(independent_check(config, name, row['tactic'], row['proof_profile'], trace / 'resume-check'))
            append(journal, row)
            if row['outcome'] != 'fault':
                print('PYTHON REUSED', goal.index, name, row['outcome'], flush=True)
                continue
        observer.output, observer.count = trace, 0
        prover.trace, prover.successes, prover.batch_number = trace, [], 0
        started = time.monotonic_ns()
        try:
            result = prover.prove(goal)
            row = dict(goal=name, index=goal.index, outcome='not-proved', original=result,
                       elapsed_ns=time.monotonic_ns() - started, trace=str(trace.relative_to(directory)))
            if result.get('proved_by'):
                if result.get('script'):
                    tactic, policy = result['script'], dict(timeout=300, heartbeats=200000, duper=False)
                else:
                    _, tactic, policy = next(x for x in prover.successes if x[0] == result['proved_by'])
                profile = 'duper' if policy['duper'] else 'core'
                row.update(tactic=tactic, proof_profile=profile, proved_by=result['proved_by'])
                row.update(independent_check(config, name, tactic, profile, trace / 'independent-check', policy))
            elif result['vampire'] == 'Unknown':
                row.update(outcome='fault', detail='solver returned no recognized status; inspect process evidence')
        except Exception as failure:
            row = dict(goal=name, index=goal.index, outcome='fault',
                       detail=f'{type(failure).__name__}: {failure}', trace=str(trace.relative_to(directory)))
        append(journal, row)
        print('PYTHON', goal.index, name, row['outcome'], flush=True)
        if row['outcome'] in ('fault', 'unfinished'):
            return dict(worker=shard, status='needs-repair', goal=name)
    return dict(worker=shard, status='completed')


def python_worker_entry(config, shard, targets):
    result = python_worker(config, shard, targets)
    print(json.dumps(result), flush=True)
    raise SystemExit(0 if result['status'] == 'completed' else 1)


def main():
    def interrupted(_signal, _frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', choices=('python', 'PythonV4', 'CettaFull'), required=True)
    parser.add_argument('--cetta', type=Path, required=True)
    parser.add_argument('--corpus', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--vampire', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--workers', type=int, default=2)
    parser.add_argument('--goals', nargs='+', help='Explicit diagnostic subset; omitted means the full corpus')
    parser.add_argument('--full-discovery', action='store_true',
                        help='Explicitly run the optional full-corpus research experiment')
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    if not args.goals and not args.full_discovery:
        parser.error('full-corpus research requires --full-discovery; port acceptance uses qualify_ai_mathematician.py')
    assert args.workers > 0
    for key in ('cetta', 'vampire'):
        setattr(args, key, Path(shutil.which(str(getattr(args, key))) or getattr(args, key)))
    lean_command = shutil.which(str(args.lean)) or str(args.lean)
    prefix = subprocess.check_output([lean_command, '--print-prefix'], cwd=ROOT, text=True).strip()
    args.lean = Path(prefix) / 'bin/lean'
    for key in ('cetta', 'corpus', 'lean', 'vampire', 'output'):
        setattr(args, key, getattr(args, key).resolve())
    args.output.mkdir(parents=True, exist_ok=True)
    library, _ = load_reference(oracle_directory())
    declarations = reference_decls(library, args.corpus)
    targets = [d.name for d in declarations if d.kind == 'THM' and (not args.goals or d.name in args.goals)]
    if args.goals:
        assert len(set(args.goals)) == len(args.goals) == len(targets), 'unknown or duplicate goal'
    else:
        assert len(targets) == 999, 'the full qualification corpus must contain 999 theorem goals'
    config = {key: str(getattr(args, key)) for key in ('cetta', 'corpus', 'lean', 'vampire', 'output')}
    manifest = dict(schema='ai-math.discovery.v1', profile=args.profile, targets=targets,
                    full_corpus=not args.goals, python_revision=PYTHON_V4,
                    tools={key: digest(config[key]) for key in ('cetta', 'corpus', 'lean', 'vampire')},
                    adapter_sha256=digest(__file__), workers=args.workers,
                    application={str(p.relative_to(ROOT)): digest(p) for base in ('phase1', 'lib')
                                 for p in (ROOT / base).glob('*') if p.suffix in ('.metta', '.lean')},
                    model_calls=False)
    manifest_path = args.output / 'inputs.json'
    if args.resume:
        assert json.loads(manifest_path.read_text()) == manifest, 'run identity changed; use a new output directory'
    else:
        with manifest_path.open('x') as output:
            json.dump(manifest, output, indent=2)
            output.write('\n')
    if args.profile == 'python':
        context = multiprocessing.get_context('spawn')
        workers = [context.Process(target=python_worker_entry, args=(config, i, targets[i::args.workers]))
                   for i in range(args.workers)]
        try:
            for worker in workers:
                worker.start()
            while any(worker.is_alive() for worker in workers):
                for worker in workers:
                    worker.join(timeout=0.2)
                if any(worker.exitcode not in (None, 0) for worker in workers):
                    break
        finally:
            for worker in workers:
                if worker.is_alive():
                    worker.terminate()
            for worker in workers:
                if worker.pid is not None:
                    worker.join(timeout=5)
                    if worker.is_alive():
                        worker.kill()
                        worker.join()
        observations = prior_results(args.output, 'worker-*.jsonl')
    else:
        native_output = args.output / 'native'
        native_config = dict(corpus=config['corpus'], output=str(native_output), workers=args.workers,
                             lean=config['lean'], vampire=config['vampire'], profile=args.profile,
                             goals=targets, mode='Resume' if args.resume else 'Fresh',
                             itp_runtime='native', trace=True, use_duper=True)
        path = args.output / 'run.json'
        path.write_text(json.dumps(native_config, indent=2) + '\n')
        run = owned_run([args.cetta, '--no-results', '--lang', 'petta@1.0.6', ROOT / 'phase1/workers_main.metta', path],
                        env=dict(os.environ, CETTA_ITP_RUNTIME='native'))
        (args.output / 'coordinator.stdout').write_text(run.stdout)
        (args.output / 'coordinator.stderr').write_text(run.stderr)
        replies = read_values(run.stdout)
        assert len(replies) == 1 and len(replies[0]) == 5 and replies[0][0] == 'AiWorkers:Summary', (
            run.returncode, run.stdout[-2000:], run.stderr)
        counts = {key: int(value) for key, value in replies[0][3]}
        expected_exit = 2 if counts['fault'] else 3 if counts['unfinished'] else 0
        assert run.returncode == expected_exit, (run.returncode, expected_exit, run.stderr)
        assert int(replies[0][2]) == len(targets)
        observations = prior_results(native_output, 'joined.jsonl')
        assert set(observations) == set(targets)
        assert all(row['run'] == replies[0][1] for row in observations.values())
        assert all(counts[key] == sum(row['outcome'] == key for row in observations.values()) for key in counts)
        rechecks = args.output / ('rechecks-' + str(time.time_ns()) + '.jsonl')
        for name in targets:
            row = observations[name]
            if row['outcome'] == 'proved':
                result = independent_check(config, name, row['tactic'], row['proof_profile'],
                                           args.output / 'independent' / str(row['index']))
                row.update(result)
            append(rechecks, row)
    ordered = [observations[name] for name in targets if name in observations]
    (args.output / 'comparison-input.json').write_text(json.dumps(ordered, indent=2) + '\n')
    counts = {kind: sum(row['outcome'] == kind for row in ordered) for kind in ('proved', 'not-proved', 'fault', 'unfinished')}
    counts['missing'] = len(targets) - len(ordered)
    complete = not any(counts[key] for key in ('missing', 'fault', 'unfinished'))
    summary = dict(profile=args.profile, full_corpus=not args.goals, targets=len(targets),
                   complete=complete, counts=counts, input_manifest_sha256=digest(manifest_path))
    (args.output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary), flush=True)
    if not complete:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
