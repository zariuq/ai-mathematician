#!/usr/bin/env python3
"""Exercise a layout-enabled CeTTa runtime without adding an application dependency."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", required=True)
    parser.add_argument("--cetta-source", required=True)
    parser.add_argument("--cc", default=os.environ.get("CC", "cc"))
    args = parser.parse_args()
    source = Path(args.cetta_source).resolve(strict=True)
    runtime = Path(args.cetta).resolve(strict=True)
    if not runtime.is_relative_to(source / "runtime"):
        parser.error("select the built executable from this source checkout's runtime directory")
    inputs = [source / "langdef/layouts/runtime_words.module",
              source / "src/generated/cetta_layout_words.generated.h",
              source / "tests/test_layout_words.c", runtime]
    for path in inputs:
        if not path.is_file():
            parser.error(f"missing integration input: {path}")
    before = {str(p.relative_to(source)): digest(p) for p in inputs}
    application = sorted({*ROOT.glob("phase1/*.metta"), *ROOT.glob("phase1/*.py"),
                          Path(__file__).resolve(),
                          ROOT / "tests/check_ai_mathematician_library.py",
                          ROOT / "tests/check_ai_mathematician_search.py",
                          ROOT / "tests/typed_export_oracle.py"})
    # Include the optional newer oracle when present, while retaining support
    # for application revisions whose comparison driver is self-contained.
    application = [p for p in application if p.is_file()]
    application_before = {str(p.relative_to(ROOT)): digest(p) for p in application}
    work = ROOT / ".cetta/layout-runtime"
    work.mkdir(parents=True, exist_ok=True)
    executable = work / "test-layout-words"
    subprocess.run([*shlex.split(args.cc), "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror",
                    str(inputs[2]), "-o", str(executable)], check=True)
    subprocess.run([str(executable)], check=True)
    for test, extra in [("check_ai_mathematician_library.py", ["--generated", "256"]),
                        ("check_ai_mathematician_search.py", [])]:
        subprocess.run([sys.executable, str(ROOT / "tests" / test),
                        "--cetta", str(runtime), *extra], cwd=ROOT, check=True)
    after = {str(p.relative_to(source)): digest(p) for p in inputs}
    application_after = {str(p.relative_to(ROOT)): digest(p) for p in application}
    if before != after or application_before != application_after:
        raise SystemExit("integration inputs changed during the check; rerun against stable inputs")
    receipt = {"passed": True, "inputs": after, "application_inputs": application_after,
               "checks": ["native word codecs", "application loader: fixtures and 256 generated cases",
                          "application search fixtures"],
               "boundary": "runtime/application regression tests, not a proof of the executable's source correspondence"}
    (work / "summary.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("layout-enabled CeTTa: native codecs, application loader and search passed")


if __name__ == "__main__":
    main()
