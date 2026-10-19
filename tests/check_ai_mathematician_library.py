#!/usr/bin/env python3
"""Qualify the PeTTa corpus-loader port, optionally against the Python source.

No Python is used by the port. This driver is only a comparison oracle.
Run with --cetta PATH. To compare a genuine export, also pass --corpus PATH
and --oracle-library PATH/phase1/library.py from the pinned upstream tree.
"""

import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys
import time

from typed_export_oracle import accept_source_positions


ROOT = Path(__file__).resolve().parents[1]
SOURCE_REVISION = "5e73833790d43d066f72be1548be2ee0fcab192d"
SOURCE_SHA256 = "dff524e2b8ea60543df26a6f49ac27e006da8b616a67d6caed2f4ade69983d6a"
TOKEN = re.compile(r'\s*(\(|\)|"(?:\\.|[^"\\])*"|[^\s()]+)')


def read_atoms(text):
    """Read printed MeTTa data; leave number tokens as strings, like the oracle."""
    tokens = [match.group(1) for match in TOKEN.finditer(text)]
    position = 0

    def node():
        nonlocal position
        token = tokens[position]
        position += 1
        if token == "(":
            items = []
            while position < len(tokens) and tokens[position] != ")":
                items.append(node())
            if position == len(tokens):
                raise ValueError("unterminated output expression")
            position += 1
            return items
        if token == ")":
            raise ValueError("unexpected closing parenthesis")
        return json.loads(token) if token.startswith('"') else token

    result = []
    while position < len(tokens):
        result.append(node())
    return result


def quote(value):
    return json.dumps(str(value), ensure_ascii=False)


def run(cetta, expression, language):
    program = (
        f'!(import! &self {quote(ROOT / "phase1/library.metta")})\n'
        f"!{expression}\n"
    )
    start = time.perf_counter()
    completed = subprocess.run(
        [str(cetta), "--lang", language, "-e", program],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode:
        raise AssertionError(
            f"{expression[:160]}:\n" + (completed.stderr.strip() or completed.stdout.strip())
        )
    values = read_atoms(completed.stdout)
    if not values or values[0] != "true" or len(values) != 2:
        raise AssertionError(f"expected import plus one result, got {completed.stdout[:500]!r}")
    return values[-1], time.perf_counter() - start


def normalized(declaration):
    tag, index, kind, name, digest, stmt, body, symbols, deps, features = declaration
    if tag != "Decl":
        raise AssertionError(f"not a declaration: {declaration[:4]}")
    for values in (symbols, deps, features):
        if len(values) != len(set(values)):
            raise AssertionError(f"duplicate set member in {name}")
    return {
        "index": int(index), "kind": kind, "name": name, "hash": digest,
        "stmt": stmt, "body": None if body == "NoBody" else body,
        "stmt_syms": sorted(symbols), "proof_deps": sorted(deps),
        "feats": sorted(features),
    }


def expected(declaration):
    return {
        "index": declaration.index, "kind": declaration.kind,
        "name": declaration.name, "hash": declaration.hash,
        "stmt": declaration.stmt, "body": declaration.body,
        "stmt_syms": sorted(declaration.stmt_syms),
        "proof_deps": sorted(declaration.proof_deps),
        "feats": sorted(declaration.feats),
    }


def compare(actual, wanted, label):
    if len(actual) != len(wanted):
        raise AssertionError(f"{label}: {len(actual)} declarations != {len(wanted)}")
    checked = 0
    for index, (left, right) in enumerate(zip(actual, wanted)):
        for key in right:
            if left[key] != right[key]:
                raise AssertionError(
                    f"{label}, declaration {index} {right['name']}, {key}:\n"
                    f"  MeTTa {left[key]!r}\n  Python {right[key]!r}"
                )
            checked += 1
    return checked


def generated_lines(seed):
    rng = random.Random(seed)
    forms = [
        '(PARAM "p" "hp" 0 (PROP))',
        '(PRIM 7 "member" "hmember" (AR (SET) (PROP)))',
        '(AXIOM "premise" "ha" 0 (TMH "hp"))',
    ]
    hashes = ["hp", "hmember", "ha", "unknown"]

    def term(depth):
        if depth == 0:
            return rng.choice([
                f'(TMH {quote(rng.choice(hashes))})', '(DB 0)', '(PRIM 7)', '(PROP)'
            ])
        tag = rng.choice(["AP", "TPAP", "ALL", "IMP", "LAM", "AR", "PAIR"])
        return f"({tag} {term(depth - 1)} {term(depth - 1)})"

    for index in range(8):
        body = term(rng.randrange(4))
        if index % 3 == 0:
            forms.extend([
                f'(THM "t{index}" "ht{index}" "pt{index}" 0 {body})',
                f'(PROOF "t{index}" (PAIR (KNOWN {quote(rng.choice(hashes))}) '
                f'(KNOWN "ha") (TMH "hp")))',
            ])
        else:
            forms.append(f'(DEF "d{index}" "hd{index}" 0 (PROP) {body})')
        hashes.append(f"ht{index}" if index % 3 == 0 else f"hd{index}")
    if seed % 2 == 0:
        # Rebinding a hash changes final features, not earlier symbol sets.
        forms.append('(PARAM "alias" "hp" 0 (PROP))')
    forms += ['WARNING: ignored', '(BROKEN', '(PROOF "orphan" (KNOWN "ha"))']
    return forms


def oracle_from_lines(oracle, lines):
    """Exercise load itself, substituting only its file input for generated data."""
    import io
    from unittest.mock import patch
    with patch("builtins.open", return_value=io.StringIO("\n".join(lines))):
        return [expected(d) for d in oracle.load("generated.sexpr")]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", required=True, type=Path)
    parser.add_argument("--language", default="petta@1.0.6")
    parser.add_argument("--oracle-library", type=Path, default=ROOT / "phase1/library.py")
    parser.add_argument("--corpus", type=Path)
    parser.add_argument("--generated", type=int, default=32)
    args = parser.parse_args()
    cetta = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    checks = 0

    # Public MeTTa positive and negative examples must themselves pass.
    fixture = ROOT / "tests/metta/ai_mathematician_library.metta"
    completed = subprocess.run(
        [str(cetta), "--lang", args.language, str(fixture)], cwd=ROOT,
        text=True, capture_output=True, check=False,
    )
    if completed.returncode or "❌" in completed.stderr + completed.stdout:
        raise AssertionError("MeTTa examples:\n" + (completed.stderr or completed.stdout))
    observations = completed.stdout.splitlines()
    if observations.count("true") != 9 or completed.stdout.count("✅") != 8:
        raise AssertionError(f"unexpected example observations: {completed.stdout}")
    checks += 8

    fixture_data = ROOT / "tests/fixtures/ai_mathematician_library.sexpr"
    rows, elapsed = run(cetta, f"(ai-math:load-library {quote(fixture_data)})", args.language)
    actual = [normalized(row) for row in rows]
    assert len(actual) == 11, actual
    assert [d["index"] for d in actual] == list(range(11))
    by_name = {d["name"]: d for d in actual}
    assert by_name["uses_future"]["stmt_syms"] == ["In"]
    assert by_name["uses_future"]["feats"] == ["concl:future", "concl:future>PRIM", "future", "future>PRIM"]
    assert by_name["later"]["proof_deps"] == ["future", "premise"]
    assert by_name["replaced"]["hash"] == "new-hash"
    assert by_name["replaced"]["proof_deps"] == ["later", "premise"]
    assert "unproved" not in by_name and "orphan" not in by_name
    checks += 8

    # Native reader data stays inert: it is never evaluated as a MeTTa call.
    inert_line = '(DEF "safe" "h" 0 (PROP) (+ 1 2))'
    inert, _ = run(cetta, f"(ai-math:library-from-lines ({quote(inert_line)}))", args.language)
    assert normalized(inert[0])["body"] == ["+", "1", "2"]
    checks += 1

    # Positions are metadata only at their declared record arity, and must
    # be nonnegative integral values. Unknown extra fields stay malformed.
    for annotation in ('"line"', '-1', '1.5', '(line 3)', '2 3'):
        line = f'(PARAM "p" "hp" 0 (PROP) {annotation})'
        result, _ = run(cetta, f"(ai-math:library-from-lines ({quote(line)}))", args.language)
        assert result[0] == "Error" and result[1][0] == "AiMathMalformedDeclaration", result
        checks += 1

    # A failure after an admitted prefix must not publish a partial library.
    malformed = ['(PARAM "p" "hp" 0 (PROP))', '(PARAM wrong-shape)',
                 '(PARAM "later" "hlater" 0 (PROP))']
    failed, _ = run(cetta, "(ai-math:library-from-lines (" +
                    " ".join(map(quote, malformed)) + "))", args.language)
    assert failed == ["Error", ["AiMathMalformedDeclaration", ["PARAM", "wrong-shape"]],
                      "ai-math:library-from-lines"], failed
    checks += 1

    # The CLI is a real consumer: argument handling, summary, diagnostics,
    # and non-zero failure status, not just a callable demonstration.
    entry = ROOT / "phase1/library_main.metta"
    cli = subprocess.run([str(cetta), "--lang", args.language, str(entry), str(fixture_data)],
                         cwd=ROOT.parent, text=True, capture_output=True, check=False)
    assert cli.returncode == 0, "CLI:\n" + cli.stderr
    summary = read_atoms(cli.stdout)[0]
    assert summary[0:2] == ["LibrarySummary", "11"], summary
    assert {kind[1]: int(kind[2]) for kind in summary[2]} == {
        "PARAM": 2, "PRIM": 1, "AXIOM": 2, "DEF": 4, "THM": 2}, summary
    assert summary[3] == ["Theorems", "2", ["FactsCited", "4"], ["MeanCitations", "2"]], summary
    failed_cli = subprocess.run(
        [str(cetta), "--lang", args.language, str(entry), str(fixture_data) + ".missing"],
        cwd=ROOT.parent, text=True, capture_output=True, check=False,
    )
    assert failed_cli.returncode != 0 and "LibrarySummary" not in failed_cli.stdout
    assert "cannot open file" in failed_cli.stdout + failed_cli.stderr
    assert not any(marker in failed_cli.stdout + failed_cli.stderr for marker in (
        "ERROR: LeakSanitizer", "ERROR: AddressSanitizer", "runtime error:",
    )), failed_cli.stderr
    checks += 5

    if args.oracle_library:
        source = args.oracle_library.resolve()
        if hashlib.sha256(source.read_bytes()).hexdigest() != SOURCE_SHA256:
            raise AssertionError(f"oracle is not pinned revision {SOURCE_REVISION}")
        spec = importlib.util.spec_from_file_location("ai_math_library_oracle", source)
        oracle = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(oracle)
        accept_source_positions(oracle)
        checks += compare(actual, [expected(d) for d in oracle.load(str(fixture_data))], "fixture")
        for seed in range(args.generated):
            lines = generated_lines(seed)
            expression = "(ai-math:library-from-lines (" + " ".join(map(quote, lines)) + "))"
            rows, _ = run(cetta, expression, args.language)
            checks += compare([normalized(row) for row in rows], oracle_from_lines(oracle, lines), f"seed {seed}")
            positioned = [line[:-1] + f" {i + 1})" if line.startswith(tuple(
                "(" + tag + " " for tag in ("PARAM", "AXIOM", "DEF", "PRIM", "THM", "PROOF")
            )) and line.endswith(")") else line for i, line in enumerate(lines)]
            rows, _ = run(cetta, "(ai-math:library-from-lines (" +
                          " ".join(map(quote, positioned)) + "))", args.language)
            checks += compare([normalized(row) for row in rows],
                              oracle_from_lines(oracle, lines), f"positioned seed {seed}")
        print(f"GeneratedLibraries {args.generated} 0")
        if args.corpus:
            corpus = args.corpus.resolve()
            rows, elapsed = run(cetta, f"(ai-math:load-library {quote(corpus)})", args.language)
            actual = [normalized(row) for row in rows]
            checks += compare(actual, [expected(d) for d in oracle.load(str(corpus))], "export")
            print(f"ExportDeclarations {len(actual)} {dict(Counter(d['kind'] for d in actual))}")
            print(f"ExportSHA256 {hashlib.sha256(corpus.read_bytes()).hexdigest()}")
            print(f"ExportProcessSeconds {elapsed:.6f}")
    elif args.corpus:
        parser.error("--corpus comparisons require --oracle-library")

    print(f"BinarySHA256 {hashlib.sha256(cetta.read_bytes()).hexdigest()}")
    print(f"Language {args.language}")
    print(f"AiMathematicianLibrary {checks} 0")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ValueError, IndexError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        sys.exit(1)
