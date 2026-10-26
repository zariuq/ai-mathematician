#!/usr/bin/env python3
"""Qualify the PeTTa ATP bridge; Python is only an independent test oracle."""

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys

from check_ai_mathematician_library import ROOT, SOURCE_SHA256, quote

ATP_SHA256 = "1285718afc6afb0eee59fe36d5433463545c8a99a21ef48e6a992f8c22cfd089"


@dataclass(frozen=True)
class ListValue:
    items: tuple


def read_values(text):
    tokens = re.findall(r'\(|\)|\[|\]|"(?:\\.|[^"\\])*"|[^\s()\[\]]+', display_text(text))
    position = 0

    def node():
        nonlocal position
        token = tokens[position]
        position += 1
        if token in ("(", "["):
            end, items = (")" if token == "(" else "]"), []
            while position < len(tokens) and tokens[position] != end:
                items.append(node())
            if position == len(tokens):
                raise ValueError("unterminated output value")
            position += 1
            return items if token == "(" else ListValue(tuple(items))
        if token in (")", "]"):
            raise ValueError("unexpected closing delimiter")
        return json.loads(token) if token.startswith('"') else token

    values = []
    while position < len(tokens):
        values.append(node())
    return values


def associative(node):
    """Only associativity of Boolean and/or; preserve order and list kinds."""
    if isinstance(node, ListValue):
        return ListValue(tuple(associative(x) for x in node.items))
    if not isinstance(node, list):
        return node
    items = [associative(x) for x in node]
    if items and items[0] in ("∧", "∨"):
        flat = [items[0]]
        for item in items[1:]:
            flat.extend(item[1:] if isinstance(item, list) and item and item[0] == items[0] else [item])
        return flat
    return items


def prelude():
    return ('!(import! &self proc)\n'
            f'!(import! &self {quote(ROOT / "phase1/library.metta")})\n'
            '!(import! &self (library list))\n'
            '!(import! &self (library lib_tptp))\n'
            '!(import! &self re)\n'
            f'!(import! &self {quote(ROOT / "phase1/vampire_output.metta")})\n'
            f'!(import! &self {quote(ROOT / "phase1/search.metta")})\n'
            f'!(import! &self {quote(ROOT / "phase1/atp.metta")})\n')


def display_text(text):
    # PeTTa prints control characters literally inside quoted strings.
    output, quoted, escaped = [], False, False
    for char in text:
        output.append(f"\\u{ord(char):04x}" if quoted and ord(char) < 32 else char)
        if escaped:
            escaped = False
        elif quoted and char == "\\":
            escaped = True
        elif char == '"':
            quoted = not quoted
    return "".join(output)


def execute(binary, program, output):
    # Keep generated cases out of argv: its OS size bound is unrelated to
    # the language or the number of corpus goals being qualified.
    output.mkdir(parents=True, exist_ok=True)
    source = output / f"atp-{hashlib.sha256(program.encode()).hexdigest()[:16]}.metta"
    source.write_text(program, encoding="utf-8")
    result = subprocess.run([str(binary), "--lang", "petta", str(source.resolve())],
                            cwd=ROOT, text=True, capture_output=True, check=False)
    if result.returncode:
        raise AssertionError(result.stderr or result.stdout[:1500])
    values = read_values(result.stdout)
    imports = prelude().count("!(import!")
    assert len(values) == imports + 1 and values[:imports] == ["true"] * imports, result.stdout[:1000]
    return values[-1]


def reference(directory):
    for name, digest in (("library.py", SOURCE_SHA256), ("atp.py", ATP_SHA256)):
        assert hashlib.sha256((directory / name).read_bytes()).hexdigest() == digest, name
    sys.path.insert(0, str(directory))
    import library
    from typed_export_oracle import accept_source_positions
    accept_source_positions(library)
    spec = importlib.util.spec_from_file_location("ai_math_atp_oracle", directory / "atp.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return library, module


def term_text(node):
    if isinstance(node, list):
        return "(" + " ".join(term_text(x) if i else str(x) for i, x in enumerate(node)) + ")"
    return str(node) if isinstance(node, int) else quote(node)


def generated_corpus(count):
    lines = [
        '(PARAM "p" "hp" 0 (PROP))', '(PARAM "q" "hq" 0 (PROP))',
        '(PARAM "not" "hnot" 0 (AR (PROP) (PROP)))',
        '(PARAM "and" "hand" 0 (AR (PROP) (AR (PROP) (PROP))))',
        '(PARAM "or" "hor" 0 (AR (PROP) (AR (PROP) (PROP))))',
        '(PARAM "iff" "hiff" 0 (AR (PROP) (AR (PROP) (PROP))))',
        '(PARAM "eq" "heq" 1 (AR (TPVAR 0) (AR (TPVAR 0) (PROP))))',
        '(PARAM "ex" "hex" 1 (AR (AR (TPVAR 0) (PROP)) (PROP)))',
        '(PARAM "neq" "hneq" 1 (AR (TPVAR 0) (AR (TPVAR 0) (PROP))))',
        '(PARAM "True" "htrue" 0 (PROP))', '(PARAM "False" "hfalse" 0 (PROP))',
        '(PARAM "f" "hf" 0 (AR (SET) (SET)))', '(PARAM "x" "hx" 0 (SET))',
        '(PRIM 9 "member" "hmember" (AR (SET) (AR (SET) (PROP))))',
        '(PARAM "poly" "hpoly" 1 (AR (TPVAR 0) (TPVAR 0)))',
        '(AXIOM "base_p" "hbase" 0 (TMH "hp"))',
        '(AXIOM "base_imp" "himp" 0 (IMP (TMH "hp") (TMH "hq")))',
    ]
    for i in range(8):
        previous = "hp" if i == 0 else f"hd{i-1}"
        lines.append(f'(DEF "alias_{i}" "hd{i}" 0 (PROP) (TMH "{previous}"))')

    def boolean(rng, depth):
        if depth == 0:
            return ["TMH", rng.choice(("hp", "hq", "hd7"))]
        choice = rng.randrange(16)
        if choice == 0:
            return ["IMP", boolean(rng, depth - 1), boolean(rng, depth - 1)]
        if choice == 1:
            return ["AP", ["TMH", "hnot"], boolean(rng, depth - 1)]
        if choice in (2, 3, 4):
            name = ("hand", "hor", "hiff")[choice - 2]
            return ["AP", ["AP", ["TMH", name], boolean(rng, depth - 1)], boolean(rng, depth - 1)]
        if choice == 5:
            return ["AP", ["LAM", ["PROP"], ["DB", 0]], boolean(rng, depth - 1)]
        if choice == 6:
            return ["ALL", ["PROP"], ["IMP", ["DB", 0], ["DB", 0]]]
        if choice == 7:
            return ["AP", ["TPAP", ["TMH", "hex"], ["PROP"]], ["LAM", ["PROP"], ["DB", 0]]]
        if choice == 8:
            return ["ALL", ["SET"], ["AP", ["AP", ["TPAP", ["TMH", "heq"], ["SET"]], ["DB", 0]], ["DB", 0]]]
        if choice == 9:
            return ["ALL", ["AR", ["SET"], ["PROP"]], ["AP", ["DB", 0], ["TMH", "hx"]]]
        if choice == 10:
            return ["ALL", ["SET"], ["AP", ["AP", ["PRIM", 9], ["DB", 0]], ["TMH", "hx"]]]
        if choice == 11:
            return ["ALL", ["SET"], ["ALL", ["AR", ["SET"], ["SET"]],
                ["AP", ["AP", ["TPAP", ["TMH", "heq"], ["SET"]],
                    ["AP", ["DB", 0], ["DB", 1]]], ["DB", 1]]]]
        if choice == 12:
            return ["AP", ["AP", ["TPAP", ["TMH", "hneq"], ["SET"]],
                ["AP", ["TMH", "hf"], ["TMH", "hx"]]], ["TMH", "hx"]]
        if choice == 13:
            return ["TMH", rng.choice(("htrue", "hfalse"))]
        if choice == 14:
            return ["ALL", ["SET"], ["AP", ["AP", ["TPAP", ["TMH", "heq"], ["SET"]],
                ["AP", ["TPAP", ["TMH", "hpoly"], ["SET"]], ["DB", 0]]], ["DB", 0]]]
        return boolean(rng, 0)

    for i in range(count):
        statement = term_text(boolean(random.Random(i), 3))
        lines.extend((f'(THM "generated_{i}" "hg{i}" "pg{i}" 0 {statement})',
                      f'(PROOF "generated_{i}" (KNOWN "hbase"))'))
    return "\n".join(lines) + "\n"


def compare_corpus(binary, path, library, oracle, output, *, all_goals, ranked=False):
    declarations = library.load(str(path))
    # Only hygienic alpha-renaming differs from the original translator.
    # Its type/term/definition logic is unchanged; duplicate-name policy is last.
    identifiers = {d.name: f"c_{i}" for i, d in enumerate(declarations)}
    oracle.ident = lambda name: identifiers[name]
    compiler = oracle.THF(declarations)
    oracle.attach_prim_indices(compiler, str(path))
    goals = [d for d in declarations if d.kind == "THM"]
    if ranked and not all_goals:
        selected = {goals[min(i * len(goals) // 20, len(goals) - 1)].index for i in range(min(20, len(goals)))}
        selected |= {d.index for d in goals if d.name in ("ReplI", "omega_diadic_rational_p", "mul_SNo_nonzero_cancel")}
        goals = [d for d in goals if d.index in selected]
    elif not all_goals:
        goals = goals[::max(1, len(goals) // 12)][:12]
    premises = [d.name for d in declarations if d.kind in ("AXIOM", "THM")][:4]
    requests, wanted = [], []
    if ranked:
        from search import Search
        selector = Search(declarations)
    for goal in goals:
        choices = [(premises, depth, "") for depth in (3, "All")]
        if ranked:
            names = [name for name, _ in selector.rank(goal.index, limit=512)]
            choices = [(names[:k], 3, f"/{k}") for k in (16, 32, 64, 128, 256, 512)]
        for chosen, depth, suffix in choices:
            try:
                text, ids, skipped = compiler.problem(goal, chosen,
                    max_def_depth=len(declarations) if depth == "All" else depth)
            except (oracle.Unsupported, IndexError):
                text, ids, skipped = None, {}, []
            expected = quote(text) if text is not None else '""'
            names = "(" + " ".join(quote(x) for x in chosen) + ")"
            requests.append(f"(atp-check:compare $context {goal.index} {names} {expected} {depth})")
            wanted.append((goal.name + suffix, text is None, ids, Counter(skipped)))
    program = prelude() + """
(= (atp-check:compare $context $index $names $expected $depth)
   (case (ai-math:thf-problem $context $index $names $depth)
     (((AiTHF:Problem $records $ids $skipped $frontier)
       (let (AiTHF $decls $catalog (AiTHF:Formats $reader $printer)) $context
         (let* (($text (ai-math:thf-text $context (AiTHF:Problem $records $ids $skipped $frontier)))
                ($actual (tptp:read-text $reader $text))
                ($reference (tptp:read-text $reader $expected)))
           (Comparison $index
             (and (list:is-list $actual) (list:is-list $reference)) $actual $reference
             $ids (map-atom $skipped $entry (index-atom $entry 1)) $frontier))))
      ((AiTHF:InterpretationRequest $why $term) (Request $index $why)))))
"""
    checks = 0
    # The observation is pointwise: retaining every translated syntax tree at
    # once adds no coverage. Bound each report while checking the same goals,
    # slices, identifiers, skipped occurrences and associativity quotient.
    for start in range(0, len(requests), 48):
        batch = requests[start:start + 48]
        report = program + f"""
!(let* (($decls (ai-math:load-library {quote(path)})) ($context (ai-math:thf $decls {quote(path)})))
   (Comparisons {' '.join(batch)}))
"""
        observed = execute(binary, report, output)
        assert observed[0] == "Comparisons" and len(observed) - 1 == len(batch)
        for result, (name, unsupported, ids, skipped) in zip(observed[1:], wanted[start:start + 48], strict=True):
            if unsupported:
                assert result[0] == "Request", (name, result)
                checks += 1
            else:
                assert result[0] == "Comparison" and result[2] == "true", (name, result)
                assert associative(result[3]) == associative(result[4]), (name, result[3], result[4])
                assert {entry[1]: entry[2] for entry in result[5]} == ids, (name, result[5], ids)
                assert Counter(result[6]) == skipped, (name, result[6], skipped)
                checks += 3
        print(f'ATPTranslationProgress {path.name} {start + len(batch)}/{len(requests)} profiles', flush=True)
    print(f"ATPTranslation {path.name} {len(goals)} goals {len(wanted)} profiles {checks} checks", flush=True)
    return checks




def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", required=True, type=Path)
    parser.add_argument("--vampire", required=True, type=Path)
    from python_oracle import oracle_directory
    parser.add_argument("--oracle-dir", type=Path)
    parser.add_argument("--corpus", type=Path)
    parser.add_argument("--generated", type=int, default=64)
    parser.add_argument("--output", type=Path, default=ROOT / ".cetta/atp")
    args = parser.parse_args()
    if args.oracle_dir is None:
        args.oracle_dir = oracle_directory()
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    vampire = Path(shutil.which(str(args.vampire)) or args.vampire).resolve()
    if not vampire.is_file():
        parser.error("Vampire was not found; supply --vampire with its executable")
    fixture = ROOT / "tests/fixtures/ai_mathematician_atp.sexpr"
    controls_source = ROOT / "tests/metta/ai_mathematician_atp.metta"
    expected_controls = len(re.findall(r"^!\(test\b", controls_source.read_text(), re.M))
    controls = subprocess.run([str(binary), "--lang", "petta", str(controls_source)], cwd=ROOT,
                              text=True, capture_output=True, check=False)
    assert controls.returncode == 0 and controls.stdout.count("✅") == expected_controls and "❌" not in controls.stdout, controls.stderr or controls.stdout
    checks = expected_controls
    # Exercise actual solver I/O separately from source-translation agreement.
    program = prelude() + f"""
!(let* (($decls (ai-math:load-library {quote(fixture)})) ($context (ai-math:thf $decls {quote(fixture)})))
   (SolverCases
     (ai-math:atp-summary (ai-math:vampire $context
       (ai-math:thf-problem $context 6 ("p_fact" "p_implies_q")) {quote(vampire)} 2))
     (ai-math:atp-summary (ai-math:vampire $context
       (ai-math:thf-problem $context 7 ()) {quote(vampire)} 2))
     (ai-math:atp-summary (ai-math:vampire $context
       (ai-math:thf-problem $context 8 ()) {quote(vampire)} 2))
     (ai-math:atp-summary (ai-math:vampire $context
       (ai-math:thf-problem $context 6 ()) {quote(vampire)} 1))
     (ai-math:atp-summary (ai-math:vampire $context
       (ai-math:thf-problem $context 12 ("p_fact")) {quote(vampire)} 2))
     (ai-math:atp-summary (ai-math:vampire $context
       (ai-math:thf-problem $context 7 ()) "/bin/false" 1))
     (ai-math:atp-summary (ai-math:vampire $context
       (ai-math:thf-problem $context 7 ())
       {quote(args.output.resolve() / 'absent-vampire-executable')} 1))
     (ai-math:atp-summary (ai-math:vampire $context
       (ai-math:thf-problem $context 15 ()) {quote(vampire)} 2))))
"""
    result = execute(binary, program, args.output)
    assert result[0] == "SolverCases"
    for row in result[1:4]:
        assert row[:2] == ["AiATP:Advice", "Theorem"], row
    assert set(result[1][2]) == {"p_fact", "p_implies_q"}, result[1]
    assert result[2][2:] == [[], []] and result[3][2:] == [[], []]
    assert result[4][:2] != ["AiATP:Advice", "Theorem"], result[4]
    assert result[5] == ["AiATP:Advice", "Theorem", ["p_fact"], ["alias"]], result[5]
    assert result[6][0] != "AiATP:Advice" and result[7][0] != "AiATP:Advice", result[6:]
    assert result[8] == ["AiATP:Advice", "Theorem", [], []], result[8]
    checks += 10
    driver = ROOT / "phase1/atp_main.metta"
    cli = subprocess.run([str(binary), "--lang", "petta", str(driver),
                          str(fixture), "q_goal", str(vampire)], cwd=ROOT.parent.parent,
                         text=True, capture_output=True, check=False)
    assert cli.returncode == 0 and "AiATP:Advice" in cli.stdout and '"Theorem"' in cli.stdout, cli.stderr or cli.stdout
    checks += 1
    usage = subprocess.run([str(binary), "--lang", "petta", str(driver)],
                           cwd=ROOT.parent, text=True, capture_output=True, check=False)
    assert usage.returncode == 2 and "usage:" in usage.stdout, usage.stderr or usage.stdout
    missing = subprocess.run([str(binary), "--lang", "petta", str(driver),
                              str(fixture) + ".missing", "q_goal", str(vampire)],
                             cwd=ROOT.parent, text=True, capture_output=True, check=False)
    assert missing.returncode != 0 and "cannot open file" in missing.stdout + missing.stderr
    assert "AiATP:Advice" not in missing.stdout, missing.stdout
    unknown = subprocess.run([str(binary), "--lang", "petta", str(driver),
                              str(fixture), "unknown_goal", str(vampire)],
                             cwd=ROOT.parent, text=True, capture_output=True, check=False)
    assert unknown.returncode == 0 and "AiTHF:InterpretationRequest theorem-name" in unknown.stdout
    assert "AiATP:Advice" not in unknown.stdout, unknown.stdout
    checks += 3
    if args.oracle_dir:
        library, oracle = reference(args.oracle_dir.resolve())
        checks += compare_corpus(binary, fixture, library, oracle, args.output, all_goals=True)
        args.output.mkdir(parents=True, exist_ok=True)
        # Source positions are envelope metadata, including on PRIM records.
        positioned = (args.output / "positioned.sexpr").resolve()
        positioned.write_text("\n".join(
            line[:-1] + f" {number})" if line.startswith("(") else line
            for number, line in enumerate(fixture.read_text().splitlines(), 1)
        ) + "\n", encoding="utf-8")
        checks += compare_corpus(binary, positioned, library, oracle, args.output, all_goals=True)
        primitive = execute(binary, prelude() + f'''
!(let $context (ai-math:thf (ai-math:load-library {quote(positioned)}) {quote(positioned)})
   (PrimitiveControl (ai-math:thf-term $context (PRIM 7) () ())
                     (ai-math:thf-term $context (PRIM 8) () ())))
''', args.output)
        assert primitive == ["PrimitiveControl", ["AiTHF:Value", "c_3", ["member"]],
                             ["AiTHF:InterpretationRequest", "unresolved-constant", ["PRIM", "8"]]], primitive
        checks += 2
        generated = (args.output / "generated.sexpr").resolve()
        generated.write_text(generated_corpus(args.generated), encoding="utf-8")
        checks += compare_corpus(binary, generated, library, oracle, args.output, all_goals=True)
        if args.corpus:
            checks += compare_corpus(binary, args.corpus.resolve(), library, oracle, args.output, all_goals=True)
    elif args.corpus:
        parser.error("--corpus requires --oracle-dir")
    print("BinarySHA256", hashlib.sha256(binary.read_bytes()).hexdigest())
    print("VampireSHA256", hashlib.sha256(vampire.read_bytes()).hexdigest())
    print("AiMathematicianATP", checks, 0)


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ValueError, IndexError, TypeError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        sys.exit(1)
