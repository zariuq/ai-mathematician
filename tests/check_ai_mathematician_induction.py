#!/usr/bin/env python3
"""Compare source-derived induction cases with the independent Python recipes."""
import argparse
import hashlib
import importlib.util
from pathlib import Path
import shutil
import subprocess
import sys

from check_ai_mathematician_atp import read_values
from check_ai_mathematician_itp import load_oracles
from check_ai_mathematician_library import ROOT, quote
from check_ai_mathematician_prover import prelude

INDUCTION_SHA256 = "ebc023b7a072110a6b4f0ca49faccf09acac5dbd1c6612f378116f483e7d8d5c"


def execute(binary, code, output):
    source = output / (hashlib.sha256(code.encode()).hexdigest()[:20] + ".metta")
    source.write_text(code, encoding="utf-8")
    result = subprocess.run([str(binary), "--no-results", "--lang", "petta@1.0.6", str(source)],
                            cwd=ROOT, text=True, capture_output=True, check=False)
    assert result.returncode == 0, result.stderr or result.stdout[:2000]
    values = read_values(result.stdout)
    assert len(values) == 1, result.stdout[:2000]
    return values[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--all", action="store_true")
    args = parser.parse_args()
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    corpus = args.corpus.resolve()
    output = ROOT / ".cetta/induction"
    output.mkdir(parents=True, exist_ok=True)
    library, _ = load_oracles()
    assert hashlib.sha256((ROOT / "phase1/induction.py").read_bytes()).hexdigest() == INDUCTION_SHA256
    spec = importlib.util.spec_from_file_location("original_induction", ROOT / "phase1/induction.py")
    oracle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracle)
    decls = library.load(str(corpus))
    inductor = oracle.Inductor(decls)
    goals = [decl for decl in decls if decl.kind == "THM"]
    if not args.all:
        goals = goals[::37] + goals[-2:]
    indices = " ".join(str(goal.index) for goal in goals)
    code = prelude() + f'!(import! &self {quote(ROOT / "phase1/induction.metta")})\n' + f"""
!(let* (($decls (ai-math:load-library {quote(corpus)}))
        ($thf (ai-math:thf-from-primitives $decls () (AiTHF:Formats None None))))
   (println! (map-atom ({indices}) $i
     (let (AiTHF:Fact $index THM $name $statement $body) (ai-math:thf-lookup $thf Ordinal $i)
       ($name
         (ai-math:ind-db (index-atom (ai-math:ind-named $statement Goal () ()) 1) ())
         (map-atom (ai-math:induction-splits $thf $index $statement) $split
           ($split (ai-math:induction-prefix $split))))))))
"""
    actual = execute(binary, code, output)
    checks, splits = 0, 0
    for goal, row in zip(goals, actual, strict=True):
        name, roundtrip, cases = row
        assert name == goal.name and roundtrip == ["AiInd:Syntax", goal.stmt], (goal.name, roundtrip)
        expected = list(inductor.splits(goal))
        assert len(cases) == len(expected), (goal.name, len(cases), len(expected))
        prefix_len, term = 0, goal.stmt
        while isinstance(term, list) and term[0] in ("ALL", "IMP"):
            prefix_len += 1
            term = term[2]
        for (split, prefix), (principle, x, guard, statements) in zip(cases, expected, strict=True):
            want = ["AiInd:Split", principle, str(prefix_len), str(x),
                    "AiInd:NoGuard" if guard is None else str(guard),
                    [["AiInd:Syntax", case.stmt] for case in statements]]
            assert split == want, (goal.name, split, want)
            script = oracle.lean_script(prefix_len, x, guard, principle, [[] for _ in statements])
            assert prefix == script.split("\n· first", 1)[0], (goal.name, prefix, script)
            checks += len(statements) + 2
            splits += 1
        checks += 2
    print(f"InductionSource {len(goals)} goals {splits} splits")
    print(f"AiMathematicianInduction {checks} 0")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ValueError, IndexError, subprocess.CalledProcessError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        sys.exit(1)
