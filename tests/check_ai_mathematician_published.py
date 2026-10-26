#!/usr/bin/env python3
"""Recheck published upstream scripts; no solver or model requests."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import threading
import time

from check_ai_mathematician_itp import execute, prelude
from check_ai_mathematician_atp import read_values
from check_ai_mathematician_library import ROOT, quote


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'duplicate JSON field: {key}')
        result[key] = value
    return result


def bundle_rows(files, limit):
    rows, names = [], set()
    for path in files:
        source = [json.loads(line, object_pairs_hook=unique_object)
                  for line in path.read_text().splitlines()]
        for row in source[:limit or len(source)]:
            if (not isinstance(row, dict) or set(row) != {'goal', 'origin', 'script', 'prelude', 'duper'}
                    or any(not isinstance(row[k], str) for k in ('goal', 'origin', 'script', 'prelude'))
                    or not row['goal'] or not row['script'] or type(row['duper']) is not bool):
                raise ValueError(f'invalid proof-bundle row in {path.name}')
            if row['goal'] in names:
                raise ValueError(f'duplicate bundle goal: {row["goal"]}')
            names.add(row['goal'])
            rows.append(row)
    if not rows:
        raise ValueError('no published proofs selected')
    return rows


def validate_record(record, rows):
    ordinal = record.get('ordinal')
    if type(ordinal) is not int or not 0 <= ordinal < len(rows):
        raise ValueError('invalid replay ordinal')
    expected = rows[ordinal]
    if (record.get('schema') != 'ai-math.replay.result.v1'
            or any(record.get(k) != expected[k] for k in ('goal', 'origin', 'duper'))
            or type(record.get('duper')) is not bool
            or type(record.get('ok')) is not bool
            or type(record.get('nanoseconds')) is not int or record['nanoseconds'] < 0
            or not isinstance(record.get('result'), str)
            or not all(isinstance(record.get(k), list) and all(isinstance(x, str) for x in record[k])
                       for k in ('used', 'axioms'))):
        raise ValueError('replay result does not identify the supplied witness')
    if record['ok'] and read_values(record['result']) != [
            ['AiITP:Accepted', expected['goal'], record['used'], record['axioms']]]:
        raise ValueError('accepted replay row lacks the independent checker verdict')


def checkpoint(path, size, checksum, inputs):
    value = dict(bytes=size, sha256=checksum, inputs_sha256=inputs)
    temporary = path.with_suffix('.pending')
    temporary.write_text(json.dumps(value) + '\n')
    os.replace(temporary, path)


def checked_receipts(output, rows, inputs):
    accepted = {}
    for path in sorted(output.glob('attempt-*/results.jsonl')):
        receipt = path.with_name('receipt.json')
        if not receipt.exists():
            continue  # No completed checkpoint: recheck, never infer success.
        value = json.loads(receipt.read_text(), object_pairs_hook=unique_object)
        raw = path.read_bytes()
        size = value.get('bytes')
        if (type(size) is not int or not 0 <= size <= len(raw)
                or value.get('inputs_sha256') != inputs
                or hashlib.sha256(raw[:size]).hexdigest() != value.get('sha256')
                or (size and raw[size - 1:size] != b'\n')):
            raise ValueError('replay checkpoint was changed or truncated')
        # A torn append beyond the checkpoint is not accepted or overwritten.
        for line in raw[:size].splitlines():
            record = json.loads(line, object_pairs_hook=unique_object)
            validate_record(record, rows)
            if record['ok']:
                accepted[record['ordinal']] = record
    return accepted


def replay_bundle(args, files):
    if args.wall_ms is not None or args.heartbeats is not None:
        raise ValueError('JSONL replay uses the bundle profiles: core 300 s/200k heartbeats, Duper 600 s/1M')
    rows = bundle_rows(files, args.limit)
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    lean = Path(subprocess.check_output([str(args.lean), '--print-prefix'], cwd=ROOT, text=True).strip()) / 'bin/lean'
    output = (args.output or ROOT / '.cetta/bundle-replay').resolve()
    output.mkdir(parents=True, exist_ok=True)
    artifacts = dict(cetta=digest(binary), lean=digest(lean))
    for name in ('itp-guard', 'itp-worker', 'lib/MegLib.olean', 'lib/Bridge.olean',
                 'lib/CettaProofTactics.olean', 'lib/CettaITP.olean',
                 'lib/CettaProposalView.olean', 'lib/CettaITPGuard.olean'):
        artifacts[name] = digest(ROOT / '.cetta/lean-native' / name)
    identity = dict(schema='ai-math.replay.receipt.v1',
                    witnesses=hashlib.sha256(json.dumps(rows, sort_keys=True).encode()).hexdigest(),
                    corpus=digest(args.corpus), artifacts=artifacts,
                    lean=subprocess.check_output([str(lean), '--version'], text=True).strip(),
                    duper_manifest=digest(ROOT / 'tools/duper-env/lake-manifest.json'),
                    runtime={name: digest(ROOT / 'phase1' / name) for name in
                             ('library.metta', 'itp.metta', 'replay.metta', 'replay_main.metta')})
    manifest = output / 'inputs.json'
    if manifest.exists():
        if not args.resume:
            raise ValueError('replay output already has a receipt; use --resume or another output directory')
        if json.loads(manifest.read_text()) != identity:
            raise ValueError('replay inputs or compiled checker changed; use another output directory')
    else:
        manifest.write_text(json.dumps(identity, indent=2) + '\n')
    inputs = digest(manifest)
    accepted = checked_receipts(output, rows, inputs)
    pending = [i for i in range(len(rows)) if i not in accepted]
    print(f'Replay: {len(rows)} witnesses, {len(accepted)} prior checked receipts, {len(pending)} pending', flush=True)
    attempt = Path(tempfile.mkdtemp(prefix='attempt-', dir=output))
    selected = [rows[i] for i in pending]
    bundle = attempt / 'input.jsonl'
    bundle.write_text(''.join(json.dumps(row, ensure_ascii=False) + '\n' for row in selected))
    workers = min(args.workers, len(pending))
    lock, stopped = threading.Lock(), threading.Event()
    processes = []
    started = time.monotonic()
    journal_hash, journal_bytes = hashlib.sha256(), 0
    with (attempt / 'results.jsonl').open('wb') as journal:
        def worker(shard):
            nonlocal journal_bytes
            command = [str(binary), '--no-results', '--lang', 'petta', str(ROOT / 'phase1/replay_main.metta'),
                       str(args.corpus.resolve()), str(bundle), str(lean), str(shard), str(workers)]
            expected = list(range(shard, len(selected), workers))
            observed, header, summary = [], None, None
            with (attempt / f'worker-{shard}.stderr').open('w') as errors, \
                    (attempt / f'worker-{shard}.jsonl').open('w') as trace:
                process = subprocess.Popen(command, cwd=ROOT, env=dict(os.environ, CETTA_ITP_RUNTIME='native'),
                                           stdout=subprocess.PIPE, stderr=errors, text=True)
                with lock:
                    processes.append(process)
                    if stopped.is_set():
                        process.terminate()
                try:
                    for line in process.stdout:
                        trace.write(line)
                        trace.flush()
                        record = json.loads(line, object_pairs_hook=unique_object)
                        schema = record.get('schema')
                        if schema == 'ai-math.replay.header.v1':
                            if (header is not None or observed
                                    or any(type(record.get(k)) is not int for k in ('entries', 'selected', 'shard', 'shards'))
                                    or record != dict(
                                    schema=schema, entries=len(selected), selected=len(expected), shard=shard, shards=workers)):
                                raise ValueError('unexpected replay header')
                            header = record
                        elif schema == 'ai-math.replay.result.v1':
                            if header is None or summary is not None:
                                raise ValueError('replay result outside its header/summary')
                            validate_record(record, selected)
                            ordinal = record['ordinal']
                            if len(observed) == len(expected) or ordinal != expected[len(observed)]:
                                raise ValueError('missing, repeated or reordered replay result')
                            observed.append(ordinal)
                            record['ordinal'] = pending[ordinal]
                            with lock:
                                encoded = (json.dumps(record, ensure_ascii=False) + '\n').encode()
                                journal.write(encoded)
                                journal.flush()
                                journal_hash.update(encoded)
                                journal_bytes += len(encoded)
                                checkpoint(attempt / 'receipt.json', journal_bytes, journal_hash.hexdigest(), inputs)
                                if record['ok']:
                                    accepted[record['ordinal']] = record
                                    if len(accepted) % 25 == 0 or len(accepted) == len(rows):
                                        print(f'Replay: {len(accepted)}/{len(rows)} accepted', flush=True)
                            if not record['ok']:
                                raise ValueError(f'{record["goal"]}: {record["result"]}')
                        elif schema == 'ai-math.replay.summary.v1':
                            if (summary is not None or header is None or record.get('ok') is not True
                                    or type(record.get('checked')) is not int or record['checked'] != len(expected)):
                                raise ValueError(f'incomplete replay summary: {record}')
                            summary = record
                        else:
                            raise ValueError(f'unexpected replay record: {schema}')
                    code = process.wait()
                    if code or header is None or summary is None or observed != expected:
                        raise ValueError(f'worker {shard}: incomplete output or exit {code}')
                finally:
                    if process.poll() is None:
                        process.terminate()
                        try:
                            process.wait(timeout=10)
                        except subprocess.TimeoutExpired:
                            process.kill()
                            process.wait()
        if workers:
            with ThreadPoolExecutor(max_workers=workers) as executor:
                futures = [executor.submit(worker, shard) for shard in range(workers)]
                try:
                    for future in as_completed(futures):
                        future.result()
                except BaseException:
                    stopped.set()
                    with lock:
                        for process in processes:
                            if process.poll() is None:
                                process.terminate()
                    raise
    # Receipts describe the tools actually exercised, not a mutable Lean
    # source checkout. They are qualification evidence, not proof-store input.
    current = dict(cetta=digest(binary), lean=digest(lean))
    current.update({name: digest(ROOT / '.cetta/lean-native' / name) for name in artifacts if name not in ('cetta', 'lean')})
    if (current != artifacts or digest(args.corpus) != identity['corpus']
            or any(digest(ROOT / 'phase1' / name) != value for name, value in identity['runtime'].items())
            or bundle_rows(files, args.limit) != rows):
        raise ValueError('replay tools, runtime or inputs changed during replay')
    if len(accepted) != len(rows):
        raise ValueError('replay coverage is incomplete')
    summary = dict(schema='ai-math.replay.qualification.v1', status='passed', checked=len(rows),
                   newly_checked=len(pending), reused=len(rows) - len(pending),
                   duper=sum(row['duper'] for row in rows), helpers=sum(bool(row['prelude']) for row in rows),
                   elapsed_seconds=round(time.monotonic() - started, 3), input_receipt='inputs.json',
                   input_receipt_sha256=digest(manifest))
    (output / 'results.jsonl').write_text(''.join(json.dumps(accepted[i], ensure_ascii=False) + '\n' for i in range(len(rows))))
    (output / 'result.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(f'AiMathematicianPublished {len(rows)} 0', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta', type=Path, required=True)
    parser.add_argument('--corpus', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--input', type=Path, action='append')
    parser.add_argument('--limit', type=int, default=0, help='Per-input sample size; zero checks all')
    parser.add_argument('--wall-ms', type=int)
    parser.add_argument('--heartbeats', type=int)
    parser.add_argument('--workers', type=int, default=1, help='Parallel JSONL replay processes')
    parser.add_argument('--output', type=Path, help='JSONL replay receipt directory')
    parser.add_argument('--resume', action='store_true', help='Reuse checked JSONL qualification receipts with identical inputs/tools')
    args = parser.parse_args()
    if min(args.limit, args.wall_ms or 0, args.heartbeats or 0) < 0 or args.workers < 1:
        parser.error('counts must be nonnegative')
    files = args.input or [ROOT / 'results/llm_proofs_verified.json', ROOT / 'results/v6v7_verified.json',
                           ROOT / 'results/v8v9_verified.json']
    if any(path.suffix == '.jsonl' for path in files):
        if not all(path.suffix == '.jsonl' for path in files):
            parser.error('JSONL bundles and legacy verified JSON files are separate input modes')
        replay_bundle(args, files)
        return
    args.wall_ms = 30000 if args.wall_ms is None else args.wall_ms
    args.heartbeats = 1000000 if args.heartbeats is None else args.heartbeats
    if args.workers != 1 or args.output or args.resume:
        parser.error('workers/output/resume apply to JSONL bundles')
    requests = []
    for path in files:
        rows = json.loads(path.read_text())['verified']
        selected = list(rows.items())[:args.limit or len(rows)]
        for target, row in selected:
            if row.get('prelude'):
                raise ValueError(f'{target}: a nonempty prelude requires separate reconstruction')
            requests.append((target, row['script']))
    if not requests:
        raise ValueError('no published proofs selected')
    directory = ROOT / '.cetta/published'
    directory.mkdir(parents=True, exist_ok=True)
    literal = '(' + ' '.join(f'({quote(target)} {quote(script)})' for target, script in requests) + ')'
    source = prelude() + f'''
!(let* (($declarations (ai-math:load-library {quote(args.corpus.resolve())}))
        ($context (ai-math:itp $declarations {quote(ROOT)} {quote(args.lean.resolve())})))
   (map-atom {literal} $row (let ($target $script) $row
     ($target (ai-math:itp-check-with $context $target $script
       (AiITP:Budget {args.wall_ms} {args.heartbeats} 8000))))))
'''
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    answers = execute(binary, source, directory)
    for (target, _), actual in zip(requests, answers, strict=True):
        assert actual[0] == target and actual[1][:2] == ['AiITP:Accepted', target], actual
    print(f'AiMathematicianPublished {len(requests)} 0')


if __name__ == '__main__':
    main()
