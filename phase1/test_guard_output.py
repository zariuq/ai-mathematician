"""The guard must fail closed: incomplete or broken Lean output is a rejection.

Runs without Lean (Lean's output is mocked), so it checks only the Python side
of the acceptance path. test_guard.py checks the Lean side with real proofs.

  python3 test_guard_output.py
"""
import subprocess
from unittest import mock

import itp
from itp import guard_verdict

COMPLETE = ("GUARD samestmt true\nGUARD used Megalodon.or\n"
            "GUARD axioms Megalodon.set propext\nGUARD done\n")


def run_check(stdout, returncode=0):
    fake = subprocess.CompletedProcess([], returncode, stdout=stdout, stderr="")
    with mock.patch("itp.subprocess.run", return_value=fake):
        return itp.check("orIL", " : True", "trivial")


CASES = [
    # (description, verdict, expected acceptance)
    ("complete report", guard_verdict(COMPLETE), True),
    ("dependency line missing", guard_verdict("GUARD samestmt true\nGUARD done\n"), False),
    ("completion marker missing (guard stopped)",
     guard_verdict(COMPLETE.replace("GUARD done\n", "")), False),
    ("axiom list missing", guard_verdict(COMPLETE.replace("GUARD axioms Megalodon.set propext\n", "")), False),
    ("axiom the proof declared itself", guard_verdict(COMPLETE.replace("propext", "Megalodon.cheat")), False),
    ("native_decide's compiler trust", guard_verdict(COMPLETE.replace("propext", "Lean.ofReduceBool")), False),
    ("library and standard axioms only", guard_verdict(COMPLETE.replace(
        "propext", "Classical.choice Quot.sound Megalodon.EmptyAx")), True),
    ("output cut off after the statement check", guard_verdict("GUARD samestmt true\n"), False),
    ("empty output", guard_verdict(""), False),
    ("statement differs", guard_verdict(COMPLETE.replace("true", "false")), False),
    ("sorryAx used", guard_verdict(COMPLETE.replace("Megalodon.or", "sorryAx")), False),
    ("batch: own report complete", guard_verdict(
        COMPLETE.replace("GUARD ", "GUARD[attempt__1] "), "[attempt__1]"), True),
    ("batch: only another attempt's report is complete", guard_verdict(
        "GUARD[attempt__1] samestmt true\nGUARD[attempt__1] used x\n"
        + COMPLETE.replace("GUARD ", "GUARD[attempt__10] "), "[attempt__1]"), False),
    ("check: complete report, exit 0", run_check(COMPLETE), True),
    ("check: complete report, non-zero exit", run_check(COMPLETE, returncode=1), False),
    ("check: dependency line missing", run_check("GUARD samestmt true\nGUARD done\n"), False),
    ("check: error inside the guard", run_check(
        "GUARD samestmt true\n/tmp/x.lean:12:2: error: unknown constant\n", returncode=1), False),
]

if __name__ == "__main__":
    bad = 0
    for desc, (ok, why, _), expected in CASES:
        good = ok == expected
        bad += not good
        print(f"{'PASS' if good else 'FAIL'}  {desc}: accepted={ok} ({why})")
    print("ALL GUARD OUTPUT TESTS PASS" if not bad else f"{bad} FAILED")
    raise SystemExit(bad)
