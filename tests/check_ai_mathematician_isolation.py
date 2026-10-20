#!/usr/bin/env python3
"""Adversarial proposal and process-ownership controls, with no network API."""
import argparse
import ctypes
import os
from pathlib import Path
import signal
import socket
import subprocess
import sys
import tempfile
import time

from check_ai_mathematician_itp import execute, prelude
from check_ai_mathematician_library import ROOT, quote


def matching(directory, helpers_only=False):
    found = set()
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit():
            continue
        try:
            argv = (entry / 'cmdline').read_bytes().split(b'\0')
            helper = str(ROOT / 'tests/fixtures/process_scope_child.py').encode()
            instance = str(directory).encode()
            positions = [i for i in range(len(argv) - 1)
                         if argv[i] == helper and argv[i + 1] == instance]
            if positions and (not helpers_only or 1 in positions):
                status = (entry / 'stat').read_text().rsplit(')', 1)[1].split()[0]
                if status != 'Z':
                    found.add(int(entry.name))
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            pass
    return found


def ownership(binary, output, timeout, startup_runs):
    checks = 0
    for index, sig in enumerate([signal.SIGTERM, signal.SIGKILL] + [signal.SIGKILL] * startup_runs):
        directory = Path(tempfile.mkdtemp(prefix='owner-', dir=output))
        argv = f'({quote(sys.executable)} {quote(ROOT / "tests/fixtures/process_scope_child.py")} {quote(directory)})'
        source = f'''!(import! &self proc)
!(let $job (proc:spawn {argv} ((lifetime owner))) (proc:await $job))
'''
        caller = subprocess.Popen([str(binary), '--no-results', '--lang', 'petta@1.0.6', '-e', source],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            if index < 2:
                end = time.monotonic() + timeout
                while not ((directory / 'child-ready').exists() and (directory / 'parent-ready').exists()):
                    assert caller.poll() is None, 'scope exited before readiness'
                    assert time.monotonic() < end, 'scope did not become ready'
                    time.sleep(0.01)
                assert len(matching(directory, helpers_only=True)) == 2
                checks += 1
            else:
                time.sleep((index % 7) / 1000)
            caller.send_signal(sig)
            caller.wait(timeout=timeout)
            end = time.monotonic() + timeout
            while matching(directory) and time.monotonic() < end:
                time.sleep(0.01)
            assert not matching(directory), f'owner death left children: {matching(directory)}'
            checks += 1
        finally:
            if caller.poll() is None:
                caller.kill()
                caller.wait(timeout=timeout)
            for pid in matching(directory):
                libc = ctypes.CDLL(None, use_errno=True)
                descriptor = libc.pidfd_open(pid, 0)
                if descriptor < 0:
                    continue
                try:
                    # A pidfd and rechecked unique argv avoid PID-reuse races.
                    if pid in matching(directory):
                        libc.pidfd_send_signal(descriptor, signal.SIGKILL, None, 0)
                finally:
                    os.close(descriptor)
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta', type=Path, required=True)
    parser.add_argument('--corpus', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=15)
    parser.add_argument('--startup-runs', type=int, default=32)
    args = parser.parse_args()
    binary = args.cetta.resolve()
    lean_prefix = subprocess.run(
        [str(args.lean), '--print-prefix'], cwd=ROOT, text=True,
        capture_output=True, check=True).stdout.strip()
    lean = Path(lean_prefix) / 'bin/lean'
    output = ROOT / '.cetta/isolation'
    output.mkdir(parents=True, exist_ok=True)
    secret = output / 'outside-worker.txt'
    secret.write_text('local-fixture-not-a-credential\n')
    written = output / 'must-not-be-written.txt'
    listener = socket.socket()
    listener.bind(('127.0.0.1', 0))
    listener.listen()
    listener.setblocking(False)
    network = ('import socket,sys; s=socket.socket(); s.settimeout(0.2); '
               f'r=s.connect_ex(("127.0.0.1",{listener.getsockname()[1]})); sys.exit(0 if r else 1)')
    genuine = 'intro P Q hp r f g\nexact f hp'
    probe = ('run_tac do\n'
             '  if (← IO.getEnv "AI_MATH_ISOLATION_SECRET").isSome then throwError "environment leaked"\n'
             f'  if (← (System.FilePath.mk {quote(secret)}).pathExists) then throwError "filesystem leaked"\n'
             '  if (← Lean.getEnv).contains `Megalodon.orIL then throwError "target leaked"\n'
             '  if (← Lean.getEnv).contains `Megalodon.SNoCutP_SNoCut_R then throwError "future leaked"\n'
             f'  let observed ← IO.Process.output {{cmd := "/usr/bin/python3", args := #["-c", {quote(network)}]}}\n'
             '  unless observed.exitCode == 0 do throwError "network leaked"\n')
    copy = ('run_tac do\n  let ci ← Lean.getConstInfo `Megalodon.orIL\n'
            '  let some proof := ci.value? (allowOpaque := true) | throwError "no proof"\n'
            '  (← Lean.Elab.Tactic.getMainGoal).assign proof\n  Lean.Elab.Tactic.replaceMainGoal []')
    write = f'run_tac IO.FS.writeFile {quote(written)} "escaped"\n' + genuine
    cases = [('valid', genuine, 'AiITP:Accepted'), ('isolated', probe + genuine, 'AiITP:Accepted'),
             ('copy-target', copy, 'AiITP:Rejected'), ('write-outside', write, 'AiITP:Rejected')]
    rows = '(' + ' '.join(f'({quote(label)} {quote(script)})' for label, script, _ in cases) + ')'
    source = prelude() + f'''
!(let* (($ds (ai-math:load-library {quote(args.corpus.resolve())}))
        ($ctx (ai-math:itp $ds {quote(ROOT)} {quote(lean)})))
   (map-atom {rows} $row (let ($label $script) $row
     ($label (ai-math:itp-check-with $ctx "orIL" $script (AiITP:Budget 30000 200000 8000))))))
'''
    os.environ['AI_MATH_ISOLATION_SECRET'] = 'local-fixture-secret'
    try:
        observed = execute(binary, source, output)
        for actual, (label, _, kind) in zip(observed, cases, strict=True):
            assert actual[0] == label and actual[1][0] == kind, (label, actual)
        assert not written.exists(), 'proposal wrote outside its certificate directory'
        try:
            connection, _ = listener.accept()
        except BlockingIOError:
            pass
        else:
            connection.close()
            raise AssertionError('proposal reached the host network')
    finally:
        os.environ.pop('AI_MATH_ISOLATION_SECRET', None)
        listener.close()
    checks = len(cases) + 2 + ownership(binary, output, args.timeout, args.startup_runs)
    print(f'AiMathematicianIsolation {checks} 0')


if __name__ == '__main__':
    main()
