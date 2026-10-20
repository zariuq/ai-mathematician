#!/usr/bin/env python3
"""Check the MeTTa/Lean acceptance boundary; Python is only a test oracle."""

import argparse
import hashlib
import importlib.util
import json
import re
from pathlib import Path
import shutil
import subprocess
import sys
from unittest.mock import patch

from check_ai_mathematician_atp import read_values
from check_ai_mathematician_library import ROOT, SOURCE_SHA256, quote
from typed_export_oracle import accept_source_positions
from python_oracle import oracle_directory

ITP_SHA256 = "7b24b11e6f4178bbd6af2d68e3510a07920272449f587b68f5680489d791116b"


def prelude():
    return (f'!(import! &self {quote(ROOT / "phase1/library.metta")})\n'
            '!(import! &self proc)\n!(import! &self json)\n!(import! &self system)\n'
            f'!(import! &self {quote(ROOT / "phase1/itp.metta")})\n')


def execute(binary, source, directory):
    path = directory / (hashlib.sha256(source.encode()).hexdigest()[:20] + ".metta")
    path.write_text(source, encoding="utf-8")
    result = subprocess.run([str(binary), "--lang", "petta@1.0.6", str(path)],
                            cwd=ROOT.parent, text=True, capture_output=True, check=False)
    if result.returncode:
        raise AssertionError(result.stderr or result.stdout[:2000])
    values = read_values(result.stdout)
    assert values[:5] == ["true"] * 5 and len(values) == 6, result.stdout[:2000]
    return values[-1]


def load_oracles():
    directory = oracle_directory()
    for name, digest in (("library.py", SOURCE_SHA256), ("itp.py", ITP_SHA256)):
        assert hashlib.sha256((directory / name).read_bytes()).hexdigest() == digest, name
    sys.path.insert(0, str(directory))
    import library
    accept_source_positions(library)
    spec = importlib.util.spec_from_file_location("original_itp", directory / "itp.py")
    oracle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracle)
    return library, oracle


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--corpus", type=Path)
    args = parser.parse_args()
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    # Resolve elan's shim under this repository's pin, not the caller's CWD.
    lean = subprocess.run([args.lean, "--print-prefix"], cwd=ROOT, text=True,
                          capture_output=True, check=True).stdout.strip()
    lean = str(Path(lean) / "bin/lean")
    output = ROOT / ".cetta/itp"
    output.mkdir(parents=True, exist_ok=True)
    unit_path = ROOT / "tests/metta/ai_mathematician_itp.metta"
    unit_count = len(re.findall(r"^!\(test\b", unit_path.read_text(), re.M))
    unit = subprocess.run([str(binary), "--lang", "petta@1.0.6", str(unit_path)],
                          cwd=ROOT, text=True, capture_output=True, check=False)
    assert unit.returncode == 0 and unit.stdout.count("✅") == unit_count, unit.stdout + unit.stderr
    assert "❌" not in unit.stdout + unit.stderr
    checks = unit_count
    if not args.corpus:
        print("ITPIntegrationSkipped: supply --corpus for kernel and source-order controls")
        print(f"AiMathematicianITP {checks} 0")
        return

    library, oracle = load_oracles()
    corpus = args.corpus.resolve()
    declarations = library.load(str(corpus))
    index_of = {decl.name: decl.index for decl in declarations}
    by_name = {decl.name: decl for decl in declarations}
    early, late = sorted((by_name["pair_Sigma"], by_name["lamI"]), key=lambda d: d.index)
    genuine = "intro P Q hp r f g\nexact f hp"
    forged_reply = json.dumps({
        "schema": "ai-math.itp.v1", "target": "orIL", "kind": "checked",
        "reason": "ok", "used": [], "axioms": [],
    }, separators=(",", ":"))
    forged_exit = ("run_tac do\n  (← IO.getStdout).putStrLn "
                   + json.dumps(forged_reply)
                   + "\n  IO.Process.exit (α := Unit) 0")
    cases = [
        ("genuine-or", "orIL", genuine, "AiITP:Accepted"),
        ("genuine-and", "andI", "intro P Q hp hq r f\nexact f hp hq", "AiITP:Accepted"),
        ("earlier-identical", late.name, f"exact {early.name}", "AiITP:Accepted"),
        ("self", "orIL", "exact orIL", "AiITP:Rejected"),
        ("later-identical", early.name, f"exact {late.name}", "AiITP:Rejected"),
        ("local-auxiliary", "orIL",
         "have hidden : forall P Q : Prop, P -> or P Q := by exact orIL\nexact hidden",
         "AiITP:Rejected"),
        ("sorry", "orIL", "sorry", "AiITP:Rejected"),
        ("nested-sorry", "orIL", "exact (by sorry)", "AiITP:Rejected"),
        ("wrong-type", "orIL", "exact _root_.True.intro", "AiITP:Rejected"),
        ("unfinished-goals", "orIL", "intro P Q hp", "AiITP:Rejected"),
        ("command-escape", "orIL", "exact orIL\nend Megalodon\naxiom forged : False",
         "AiITP:Rejected"),
        ("unknown", "not-a-corpus-theorem", "exact orIL", "AiITP:Rejected"),
        ("local-axiom", "orIL",
         "run_tac do\n  let g ← Lean.Elab.Tactic.getMainGoal\n  let ty ← g.getType\n"
         "  Lean.addDecl (.axiomDecl {name := `Megalodon.b_forged, levelParams := [], type := ty, isUnsafe := false})\n"
         "  g.assign (Lean.mkConst `Megalodon.b_forged)\n  Lean.Elab.Tactic.replaceMainGoal []",
         "AiITP:Rejected"),
        ("stdout-with-valid-proof", "orIL",
         'run_tac IO.println "GUARD samestmt true"\n' + genuine,
         "AiITP:Accepted"),
        ("opaque-auxiliary", "orIL",
         "run_tac do\n  let ci ← Lean.getConstInfo `Megalodon.orIL\n"
         "  Lean.addDecl (.thmDecl {name := `CettaITP.sneak, levelParams := [], type := ci.type, value := Lean.mkConst `Megalodon.orIL})\n"
         "  let g ← Lean.Elab.Tactic.getMainGoal\n"
         "  g.assign (Lean.mkConst `CettaITP.sneak)\n  Lean.Elab.Tactic.replaceMainGoal []",
         "AiITP:Rejected"),
        ("automation-or", "orIL", "intros\nsimp only [b_or] at *\ngrind", "AiITP:Accepted"),
        ("automation-and", "andI", "intros\nsimp only [b_and] at *\ngrind", "AiITP:Accepted"),
        ("native-computation", "orIL",
         "intro P Q hp r f g\nhave h : _root_.True := by native_decide\n"
         "exact (fun _ : _root_.True => f hp) h", "AiITP:Rejected"),
        ("forged-early-exit", "orIL", forged_exit, "AiITP:Fault"),
        ("unchecked-local-theorem", "orIL",
         "run_tac do\n"
         "  let g ← Lean.Elab.Tactic.getMainGoal\n"
         "  let ty ← g.getType\n"
         "  Lean.withOptions (fun opts => opts.setBool `debug.skipKernelTC true) do\n"
         "    Lean.addDecl (.thmDecl {name := `CettaITP.uncheckedLocal, "
         "levelParams := [], type := ty, value := Lean.mkConst `True.intro})\n"
         "  g.assign (Lean.mkConst `CettaITP.uncheckedLocal)\n"
         "  Lean.Elab.Tactic.replaceMainGoal []",
         "AiITP:Fault"),
    ]
    requests = " ".join(f'({quote(label)} {quote(target)} {quote(tactic)})'
                        for label, target, tactic, _ in cases)
    setup = (f'(let* (($declarations (ai-math:load-library {quote(corpus)})) '
             f'($context (ai-math:itp $declarations {quote(ROOT)} {quote(lean)}))) ')
    source = prelude() + "!" + setup + f"""
      (map-atom ({requests}) $case
        (let ($label $target $tactic) $case
          ($label (ai-math:itp-check $context $target $tactic)))))
"""
    rows = execute(binary, source, output)
    assert len(rows) == len(cases), rows
    for (label, result), (expected_label, target, _, kind) in zip(rows, cases):
        assert label == expected_label and result[:2] == [kind, target], (label, result, kind)
        if kind == "AiITP:Accepted":
            ok, forbidden = oracle.leak_free(result[2], index_of[target], index_of)
            assert ok, (label, forbidden)
            assert "sorryAx" not in result[3]
        checks += 1
    for index in (3, 4, 5, 14):
        result = rows[index][1]
        assert result[0] == "AiITP:Rejected" and any(
            reason in str(result) for reason in
            ("source-order", "Unknown identifier", "Unknown constant")), rows[index]
    assert rows[12][1][2] == "unaccounted-local-dependency", rows[12]
    assert rows[17][1][2] == "unaccounted-local-dependency", rows[17]
    checks += 6
    guard_reasons = []
    for _, result in rows[-2:]:
        assert result[2] == "runner", result
        fields = {entry[1]: entry[2] for entry in result[3][1]}
        guard_reasons.append(fields["reason"])
    assert guard_reasons == [
        "missing-worker-response",
        "kernel-replay",
    ], guard_reasons
    checks += 2

    source = prelude() + "!" + setup + """
      (let (AiITP:Statements $signatures) (ai-math:itp-load-statements $context)
        (ITPStatements
          (size-atom (collapse (match $signatures (AiEntry $name $text) $name)))
          (map-atom (ai-math:itp-theorems $context) $name
            ($name (ai-math:get $signatures $name AiMissing))))))
"""
    catalog = execute(binary, source, output)
    theorem_names = {d.name for d in declarations if d.kind == "THM"}
    assert catalog[0:2] == ["ITPStatements", str(len(theorem_names))], catalog[:2]
    assert {name for name, _ in catalog[2]} == theorem_names
    assert all(isinstance(text, str) and text and text != "AiMissing" for _, text in catalog[2])
    checks += len(theorem_names) + 2

    # Compare the original four guard controls without changing its algorithm.
    # Its transient source files stay in the ignored test-output directory.
    signatures = oracle.load_statements(str(ROOT / "lib/MegLib.lean"))
    original_tempfile = oracle.tempfile.NamedTemporaryFile

    def local_tempfile(*positional, **keywords):
        keywords["dir"] = str(output)
        return original_tempfile(*positional, **keywords)

    with patch.object(oracle, "LEAN", lean), patch.object(
            oracle.tempfile, "NamedTemporaryFile", side_effect=local_tempfile):
        for label, target, tactic, kind in (cases[i] for i in (0, 1, 2, 3, 4, 15, 16)):
            ok, reason, used = oracle.check(target, signatures[target], tactic)
            accepted = ok and oracle.leak_free(used, index_of[target], index_of)[0]
            assert accepted == (kind == "AiITP:Accepted"), (label, reason, used)
            checks += 1

    source = prelude() + "!" + setup + f"""
      (ITPResources
        (ai-math:itp-check-with $context "orIL" {quote(genuine)} (AiITP:Budget 1 0 0))
        (ai-math:itp-check-with $context "orIL" {quote(genuine)} (AiITP:Budget 0 0 1))
        (ai-math:itp-check-with $context "orIL" {quote(genuine)} (AiITP:Budget 0 1 0))
        (ai-math:itp-statement $context "orIL")
        (ai-math:itp-check (ai-math:itp $declarations {quote(ROOT)} "nonexistent-ai-math-lean")
          "orIL" {quote(genuine)})))
"""
    resource = execute(binary, source, output)
    assert resource[0] == "ITPResources", resource
    assert all(row[0] == "AiITP:Unfinished" for row in resource[1:4]), resource
    assert resource[4][0:2] == ["AiITP:Statement", "orIL"], resource
    assert "Prop" in resource[4][2], resource
    assert resource[5][0] == "AiITP:Fault", resource
    checks += 5

    # The CLI resolves its own application root even from another directory.
    tactic_file = output / "orIL.tactic"
    tactic_file.write_text(genuine, encoding="utf-8")
    result = subprocess.run([str(binary), "--no-results", "--lang", "petta@1.0.6",
                             str(ROOT / "phase1/itp_main.metta"), str(corpus),
                             "orIL", str(tactic_file), lean], cwd=ROOT.parent,
                            text=True, capture_output=True, check=False)
    assert result.returncode == 0, result.stdout + result.stderr
    assert read_values(result.stdout) == [rows[0][1]], result.stdout
    checks += 1
    tactic_file.write_text("exact orIL", encoding="utf-8")
    rejected = subprocess.run([str(binary), "--no-results", "--lang", "petta@1.0.6",
                               str(ROOT / "phase1/itp_main.metta"), str(corpus),
                               "orIL", str(tactic_file), lean], cwd=ROOT.parent,
                              text=True, capture_output=True, check=False)
    assert rejected.returncode == 1, rejected.stdout + rejected.stderr
    declined = read_values(rejected.stdout)[0]
    assert declined[:2] == ["AiITP:Rejected", "orIL"], declined
    assert any(marker in str(declined) for marker in
               ("source-order", "Unknown identifier", "Unknown constant")), declined
    checks += 1
    print(f"ITPCorpus {len(declarations)} declarations {sum(d.kind == 'THM' for d in declarations)} theorems")
    print(f"LeanVersion {subprocess.check_output([lean, '--version'], text=True).strip()}")
    print(f"BinarySHA256 {hashlib.sha256(binary.read_bytes()).hexdigest()}")
    print(f"AiMathematicianITP {checks} 0")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ValueError, IndexError, subprocess.CalledProcessError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        sys.exit(1)
