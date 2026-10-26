#!/usr/bin/env python3
"""Check independent induction reconstruction and the optional pinned Duper."""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

from check_ai_mathematician_library import ROOT, quote
from check_ai_mathematician_prover import execute, prelude


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--corpus", type=Path)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--vampire", type=Path)
    parser.add_argument("--duper", action="store_true")
    args = parser.parse_args()
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    unit = ROOT / "tests/metta/ai_mathematician_induction.metta"
    ran = subprocess.run([str(binary), "--lang", "petta", str(unit)],
                         text=True, capture_output=True, cwd=ROOT, check=False)
    count = len(re.findall(r"^!\(test\b", unit.read_text(), re.M))
    assert ran.returncode == 0 and ran.stdout.count("✅") == count, ran.stdout + ran.stderr
    assert "❌" not in ran.stdout + ran.stderr, ran.stdout + ran.stderr
    if not args.corpus:
        print("ReconstructionIntegrationSkipped: supply --corpus and --vampire")
        print(f"AiMathematicianReconstruction {count} 0")
        return
    assert args.vampire and args.vampire.is_file(), "supply --vampire"
    corpus = args.corpus.resolve()
    lean_root = subprocess.run([args.lean, "--print-prefix"], cwd=ROOT, text=True,
                               capture_output=True, check=True).stdout.strip()
    lean = Path(lean_root) / "bin/lean"
    output = ROOT / ".cetta/reconstruction"
    output.mkdir(parents=True, exist_ok=True)
    setup = prelude() + f"""
!(let* (($ds (ai-math:load-library {quote(corpus)}))
        ($itp (ai-math:itp $ds {quote(ROOT)} {quote(lean)})))
"""
    prefix = "intro P Q hp hq\napply (b_and P Q).mpr\nconstructor"
    cases = [(0, "same", "assumption"), (1, "same", "assumption"),
             (0, "open", "skip"),
             (0, "self", "exact ((b_and P Q).mp (andI P Q hp hq)).1"),
             (0, "placeholder", "sorry"), (99, "wrong-case", "assumption"),
             (0, "leak-writer", 'run_tac do\n  Lean.addDecl (.axiomDecl { name := `CettaITP.caseLeak, levelParams := [], type := Lean.mkConst ``False, isUnsafe := false })\nskip'),
             (0, "leak-reader", "exact False.elim CettaITP.caseLeak")]
    proposals = "(" + " ".join(f"(AiITP:CaseCandidate {case} {quote(label)} {quote(tactic)})"
                                for case, label, tactic in cases) + ")"
    actual = execute(binary, setup + f"""
   (ai-math:itp-case-batch-with $itp "andI" {quote(prefix)} {proposals}
     (AiITP:Budget 30000 200000 8000)))
""", output)
    assert actual[:2] == ["AiITP:CaseBatch", "andI"], actual
    answers = actual[2]
    assert len(answers) == len(cases), answers
    for position, ((case, label, _), row) in enumerate(zip(cases, answers, strict=True)):
        assert row[:3] == ["AiITP:CaseAttempt", str(case), label], row
        assert row[3][0] == ("AiITP:CaseAccepted" if position < 2 else "AiITP:Rejected"), row
        if position < 2:
            assert row[3][1:4] == ["andI", str(case), "2"], row
        count += 2
    assert any(marker in str(answers[3]) for marker in
               ("source-order", "Unknown identifier", "Unknown constant")), answers[3]
    assert "Unknown constant" in str(answers[-1]) or "Unknown identifier" in str(answers[-1]), answers[-1]
    count += 2
    for depth in ("All", "3"):
        actual = execute(binary, prelude() + f"""
!(let* (($ds (ai-math:load-library {quote(corpus)}))
        ($context (ai-math:prover-with $ds {quote(corpus)} {quote(ROOT)} {quote(lean)} {quote(args.vampire.resolve())}
          ((slices ()) (lean-stages ()) (definition-depth {depth}) (induction-slices (8 16)) (induction-seconds 2)
           (induction-policy (AiProver:LeanPolicy (AiITP:Budget 30000 200000 8000)
             (AiITP:Budget 30000 200000 8000) 60000))))))
   ((ai-math:prove $context "In_irref") (ai-math:induction-prove $context "In_no2cycle")))
""", output)
        proved, reconstruction = actual
        assert proved[0] == "AiProver:Result" and proved[-1][:2] == ["AiProver:Proved", "induction"], proved
        assert reconstruction[0] == "AiInd:Reconstruction" and reconstruction[-1][0] == "AiITP:Accepted", reconstruction
        assert reconstruction[1][1] == "In_ind", reconstruction[1]
        assert "Megalodon.In_irref" not in proved[-1][-2], proved[-1]
        count += 4
    if args.duper:
        actual = execute(binary, setup + """
   (let $duper (ai-math:itp-select-profile $itp duper)
     (ai-math:itp-batch-with $duper "orIL"
       ((AiITP:Candidate "genuine" "intros\ntry simp only [b_or] at *\nduper [*]")
        (AiITP:Candidate "self" "exact orIL")) (AiITP:Budget 30000 1000000 8000))))
""", output)
        assert actual[:2] == ["AiITP:Batch", "orIL"], actual
        assert [row[2][0] for row in actual[2]] == ["AiITP:Accepted", "AiITP:Rejected"], actual
        assert any(reason in str(actual[2][-1]) for reason in
                   ("source-order", "Unknown identifier", "Unknown constant")), actual
        count += 3
    # Frozen Python discovery requires Vampire to advise every induction
    # case. The broader profile may still try an independently checked local
    # reconstruction; this is a search policy, not logical impossibility.
    actual = execute(binary, prelude() + f"""
!(let* (($ds (ai-math:load-library {quote(corpus)}))
        ($context (ai-math:prover-with $ds {quote(corpus)} {quote(ROOT)} {quote(lean)} {quote(args.vampire.resolve())}
          ((slices ()) (lean-stages ()) (induction-slices ()) (induction-without-advice false)))))
   ((ai-math:induction-prove $context "In_irref")
    (ai-math:option (ai-math:prover-profile-options PythonV4) induction-without-advice true)
    (ai-math:option (ai-math:prover-profile-options CettaFull) induction-without-advice true)
    (ai-math:prover-options-valid ((induction-without-advice false)))
    (ai-math:prover-options-valid ((induction-without-advice "false")))))
""", output)
    assert actual[0][0] == "AiInd:NoReconstruction" and actual[0][-1] == [], actual[0]
    assert actual[1:] == ["false", "true", "true", "false"], actual[1:]
    count += 5
    print(f"AiMathematicianReconstruction {count} 0")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ValueError, IndexError, subprocess.CalledProcessError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        sys.exit(1)
