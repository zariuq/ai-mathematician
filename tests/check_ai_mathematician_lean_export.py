#!/usr/bin/env python3
"""Compare structural Lean generation with the pinned translator and compile it."""
import argparse
import contextlib
import hashlib
import importlib.util
import io
from pathlib import Path
import re
import shutil
import subprocess
import sys

from check_ai_mathematician_atp import read_values
from check_ai_mathematician_itp import load_oracles
from check_ai_mathematician_library import ROOT, quote


def prelude():
    return (f'!(import! &self {quote(ROOT / "phase1/library.metta")})\n'
            '!(import! &self (library list))\n'
            f'!(import! &self {quote(ROOT / "phase1/lean_export.metta")})\n')


def execute(binary, source, directory):
    path = directory / (hashlib.sha256(source.encode()).hexdigest()[:20] + ".metta")
    path.write_text(source)
    ran = subprocess.run([str(binary), "--lang", "petta", str(path)],
                         cwd=ROOT, text=True, capture_output=True, check=False)
    assert ran.returncode == 0, ran.stderr or ran.stdout[:2000]
    values = read_values(ran.stdout)
    assert len(values) == 4 and values[:3] == ["true"] * 3, ran.stdout[:2000]
    return values[-1]


def normal(text):
    text = re.sub(r"-- dependency from [a-z_]+", "", text)
    return re.sub(r"\s+", " ", text.replace("Megalodon.", "").replace("«", "").replace("»", "")).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--corpus", type=Path)
    parser.add_argument("--lean", default="lean")
    args = parser.parse_args()
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    output = ROOT / ".cetta/lean-export"
    output.mkdir(parents=True, exist_ok=True)
    fixture = '''(PARAM "P" "hp" 0 (PROP))
(AXIOM "given" "ha" 0 (TMH "hp"))
(DEF "idset" "hdef" 0 (AR (SET) (SET)) (LAM (SET) (DB 0)))
(THM "identity" "hi" "pfi" 0 (IMP (TMH "hp") (TMH "hp")))
(PROOF "identity" (PLAM (TMH "hp") (HYP 0)))
(PARAM "poly" "hpoly" 2 (AR (TPVAR 0) (AR (TPVAR 1) (TPVAR 0))))
'''
    p = output / "fixture.sexpr"
    p.write_text(fixture)
    library, _ = load_oracles()
    spec = importlib.util.spec_from_file_location("original_lean_export", ROOT / "phase1/sexpr_translate.py")
    oracle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracle)
    checks = 0
    for corpus in [p] + ([args.corpus.resolve()] if args.corpus else []):
        with contextlib.redirect_stdout(io.StringIO()):
            expected = oracle.translate(library.parse_toplevel_forms(corpus.read_text()))
        actual = execute(binary, prelude() + f'!(ai-math:lean-export {quote(corpus)})\n', output)
        assert actual[0] == "AiLean:Entries", str(actual)[:2000]
        assert len(actual[1]) == len(expected), (len(actual[1]), len(expected))
        for row, entry in zip(actual[1], expected, strict=True):
            assert row[0] == "AiLean:Entry" and row[2] == entry.name, row[:3]
            assert normal(row[3]) == normal(entry.text), (entry.name, row[3][:1000], entry.text[:1000])
            assert set(row[4]) == entry.deps, (entry.name, row[4], entry.deps)
            checks += 3
        generated = output / ("Fixture.lean" if corpus == p else "All.lean")
        emitted = subprocess.run([str(binary), "--no-results", "--lang", "petta",
                                  str(ROOT / "phase1/lean_export_main.metta"), str(corpus), str(generated)],
                                 cwd=ROOT, text=True, capture_output=True, check=False)
        assert emitted.returncode == 0, emitted.stdout[:6000] + emitted.stderr[:2000]
        assert all(row[3] in generated.read_text() for row in actual[1])
        compiled = subprocess.run([args.lean, "-M", "4096", "-Dlinter.unusedVariables=false",
                                   "-o", str(generated.with_suffix(".olean")), str(generated)],
                                  cwd=ROOT, text=True, capture_output=True, check=False)
        assert compiled.returncode == 0, compiled.stdout[:6000] + compiled.stderr[:2000]
        checks += 1
        views = output / ("fixture-views" if corpus == p else "corpus-views")
        views.mkdir(exist_ok=True)
        emitted = subprocess.run([str(binary), "--no-results", "--lang", "petta",
                                  str(ROOT / "phase1/lean_export_main.metta"), str(corpus), str(views), "--views"],
                                 cwd=ROOT, text=True, capture_output=True, check=False)
        assert emitted.returncode == 0, emitted.stdout[:6000] + emitted.stderr[:2000]
        by_name = {entry.name: entry for entry in expected}
        for tier in oracle.TIER_ORDER:
            generated_view = views / (tier + ".lean")
            assert normal(generated_view.read_text()) == normal(oracle.render_category(expected, by_name, tier)), tier
            compiled = subprocess.run([args.lean, "-M", "4096", "-Dlinter.unusedVariables=false",
                                       "-o", str(generated_view.with_suffix(".olean")), str(generated_view)],
                                      cwd=ROOT, text=True, capture_output=True, check=False)
            assert compiled.returncode == 0, tier + compiled.stdout[:6000] + compiled.stderr[:2000]
            checks += 2
        print(f"LeanExport {corpus.name} {len(expected)} declarations checked", flush=True)
    negative = [
        '(DEF "free" "h" 0 (SET) (DB 0))',
        '(DEF "unknown" "h" 0 (SET) (TMH "missing"))',
        '(PARAM "P" "h" 0 (PROP))\n(PARAM "P" "h" 0 (PROP))',
        '(PARAM "P" "h" 0 (PROP))\n(PARAM "Q" "h" 0 (SET))',
        '(THM "missing" "h" "ph" 0 (PROP))',
        '(PROOF "orphan" (HYP 0))',
        '(PARAM "bad»name" "h" 0 (SET))',
        '(PARAM "P" "h" 0 (PROP)) trailing',
        '(PARAM "truncated"',
    ]
    actual = execute(binary, prelude() + "!(map-atom (" +
                     " ".join(quote(s) for s in negative) +
                     ") $text (ai-math:lean-export-text $text))\n", output)
    assert len(actual) == len(negative) and all(row[0] == "AiLean:Request" for row in actual), actual
    checks += len(negative)
    print(f"AiMathematicianLeanExport {checks} 0")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ValueError, IndexError, subprocess.CalledProcessError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        sys.exit(1)
