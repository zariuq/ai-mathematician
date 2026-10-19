#!/usr/bin/env python3
"""Compare the PeTTa search port with the pinned upstream implementation.

Python is a test oracle, not a runtime dependency. --oracle-dir points to
the original phase1 directory; --corpus optionally supplies a real export.
Set iteration is canonicalized in both implementations: Python's random
hash iteration is not part of the premise-selection policy.
"""

import argparse
from dataclasses import replace
import hashlib
import importlib.util
import math
import re
import random
import shutil
from pathlib import Path
import subprocess
import sys

from check_ai_mathematician_library import ROOT, SOURCE_SHA256, quote, read_atoms

SEARCH_SHA256 = "49d5f7490d589dfc524b378da8d741e167b1b9cde48b8ca6973d4dd741a65879"


class CanonicalSet(set):
    def __iter__(self):
        return iter(sorted(set.copy(self)))

    def __and__(self, other):
        return CanonicalSet(set.__and__(self, other))

    __rand__ = __and__

    def __or__(self, other):
        return CanonicalSet(set.__or__(self, other))

    __ror__ = __or__


def execute(binary, program):
    completed = subprocess.run(
        [str(binary), "--lang", "petta@1.0.6", "-e", program], cwd=ROOT,
        text=True, capture_output=True, check=False,
    )
    if completed.returncode:
        raise AssertionError(completed.stderr or completed.stdout[:1000])
    atoms = read_atoms(completed.stdout)
    if len(atoms) != 4 or atoms[:3] != ["true"] * 3:
        raise AssertionError(f"missing complete search report: {completed.stdout[:600]!r}")
    return atoms[-1]


def prelude():
    return (f'!(import! &self {quote(ROOT / "phase1/library.metta")})\n'
            '!(import! &self (library list))\n'
            f'!(import! &self {quote(ROOT / "phase1/search.metta")})\n')


def close(left, right, where):
    if not math.isclose(float(left), float(right), rel_tol=1e-10, abs_tol=1e-10):
        raise AssertionError(f"{where}: {left} != {right}")


def score_pairs(actual, expected, where, *, ranked=False):
    pairs = [(name, float(score)) for name, score in actual]
    if ranked:
        if [name for name, _ in pairs] != [name for name, _ in expected]:
            raise AssertionError(f"{where}: names {pairs!r} != {expected!r}")
    elif {name for name, _ in pairs} != {name for name, _ in expected}:
        raise AssertionError(f"{where}: different premise sets")
    right = dict(expected)
    for name, score in pairs:
        close(score, right[name], f"{where}/{name}")
    return len(pairs) + 1


def make_report(path, indices, probes):
    source = prelude() + """
(= (ai-search-check:goal $search $decls $i)
   (let* (($goal (index-atom $decls $i)) ($earlier (list:take $i $decls)))
     (Goal $i
       (ai-math:rank $search $i)
       (ai-math:knn $search (ai-math:declaration-symbols $goal) $earlier 24)
       (ai-math:naive-bayes $search $goal $earlier 10.0 -4.0 1.0)
       (ai-math:diverse-slices $search $i 5 3)
       (ai-math:rank-with $search $i 7
         ((name-weight 0.6) (recency-weight 0.0) (knn-weight 0.75) (nb-weight 0.0)))
       (ai-math:rank-with $search $i 7
         ((recency-weight 0.2) (knn-weight 0.0) (nb-weight 2.25) (nb-decay 4.0)
          (nb-sigma 3.0) (nb-penalty -2.5) (nb-self-weight 0.5)))
       (ai-math:naive-bayes-prefix $search $goal $i 10.0 -4.0 1.0))))
"""
    requests = " ".join(f"({kind} {quote(key)} {default})" for kind, key, default in probes)
    goals = " ".join(map(str, indices))
    return source + f"""
!(let* (($decls (ai-math:load-library {quote(path)})) ($search (ai-math:search $decls)))
   (SearchReport
     (map-atom ({requests}) $request
       (let ($kind $key $default) $request
         ($kind $key (ai-math:weight $search $kind $key $default))))
     (map-atom ({goals}) $index
       (ai-search-check:goal $search (ai-math:search-facts $search) $index))))
"""


def load_reference(directory):
    for name, digest in (("library.py", SOURCE_SHA256), ("search.py", SEARCH_SHA256)):
        if hashlib.sha256((directory / name).read_bytes()).hexdigest() != digest:
            raise AssertionError(f"unpinned oracle {name}")
    sys.path.insert(0, str(directory))
    import library
    from typed_export_oracle import accept_source_positions
    accept_source_positions(library)
    spec = importlib.util.spec_from_file_location("ai_math_search_oracle", directory / "search.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    original_tokens = module.Search._toks

    class ReferenceSearch(module.Search):
        @staticmethod
        def _toks(name):
            return CanonicalSet(original_tokens(name))

    return library, ReferenceSearch


def reference_decls(library, path):
    return [replace(d, stmt_syms=CanonicalSet(d.stmt_syms),
                    proof_deps=CanonicalSet(d.proof_deps), feats=CanonicalSet(d.feats))
            for d in library.load(str(path))]


def compare_report(report, search, decls, indices):
    tag, weights, goals = report
    assert tag == "SearchReport"
    dictionaries = {"Symbol": search.idf, "Token": search.tidf, "Feature": search.fidf}
    checks = 0
    for kind, key, value in weights:
        default = 0.0 if kind == "Token" else 1.0
        close(value, dictionaries[kind].get(key, default), f"weight/{kind}/{key}")
        checks += 1
    assert len(goals) == len(indices)
    for row, index in zip(goals, indices):
        tag, observed_index, ranked, knn, bayes, slices, named, tweaked, prepared = row
        assert tag == "Goal" and int(observed_index) == index
        checks += score_pairs(ranked, search.rank(index), f"rank/{index}", ranked=True)
        checks += score_pairs(knn, list(search._knn(set(decls[index].stmt_syms), index).items()), f"knn/{index}")
        checks += score_pairs(bayes, list(search._nb(decls[index], index).items()), f"bayes/{index}")
        assert prepared == bayes, ("prepared prefix differs from isolated training", index)
        checks += score_pairs(prepared, list(search._nb(decls[index], index).items()),
                              f"prepared-bayes/{index}")
        expected_slices = search.diverse_slices(index, k=5, nn=3)
        assert slices[0] == "DiverseSlices"
        assert {kind: names for kind, names in slices[1:]} == expected_slices, (index, slices, expected_slices)
        checks += 3
        checks += score_pairs(named, search.rank(index, limit=7, name_w=0.6,
                              recency_w=0.0, knn_w=0.75, nb_w=0.0), f"named/{index}", ranked=True)
        checks += score_pairs(tweaked, search.rank(index, limit=7, recency_w=0.2,
                              knn_w=0.0, nb_w=2.25, nb_decay=4.0,
                              nb_args={"sigma": 3.0, "penalty": -2.5, "self_w": 0.5}),
                              f"tweaked/{index}", ranked=True)
        assert all(name in {d.name for d in decls[:index]} for name, _ in ranked)
    return checks


def compare_training_sums(binary):
    """Check source-prefix selection and weighted replay against a plain fold."""
    requests, expected = [], []
    for seed in range(16):
        rng = random.Random(seed)
        sources = sorted(rng.randrange(12) for _ in range(seed * 2))
        rows = [(ordinal, source, rng.choice(("Self", "Citation")))
                for ordinal, source in enumerate(sources)]
        literals = "(" + " ".join(f"({i} {source} {kind})" for i, source, kind in rows) + ")"
        queries = []
        variable = f"$rows{seed}"
        for cutoff in (-1, 0, 1, 6, 12, "All"):
            for self_weight in (1.0, 0.1, 0.5, 2.0):
                queries.append(f"(ai-math:training-sum {variable} {cutoff} {self_weight})")
                total = 0
                for _, source, kind in rows:
                    if cutoff == "All" or source < cutoff:
                        total += self_weight if kind == "Self" else 1.0
                expected.append(total)
        requests.append(f"(let {variable} {literals} (TrainingCase {' '.join(queries)}))")
    report = execute(binary, prelude() + f"!(TrainingSums {' '.join(requests)})")
    assert report[0] == "TrainingSums"
    actual = [float(value) for row in report[1:] for value in row[1:]]
    assert actual == expected, [(i, left, right) for i, (left, right)
                               in enumerate(zip(actual, expected)) if left != right][:4]
    return len(expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", required=True, type=Path)
    parser.add_argument("--oracle-dir", type=Path, default=ROOT / "phase1")
    parser.add_argument("--corpus", type=Path)
    parser.add_argument("--check-recall", action="store_true")
    args = parser.parse_args()
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    example = ROOT / "tests/metta/ai_mathematician_search.metta"
    expected_controls = len(re.findall(r"^!\(test\b", example.read_text(), re.M))
    result = subprocess.run([str(binary), "--lang", "petta@1.0.6", str(example)],
                            cwd=ROOT, text=True, capture_output=True, check=False)
    assert result.returncode == 0, result.stderr or result.stdout
    assert result.stdout.count("✅") == expected_controls and "❌" not in result.stdout, result.stdout
    checks = expected_controls
    checks += compare_training_sums(binary)
    entry = ROOT / "phase1/search_main.metta"
    data = ROOT / "tests/fixtures/ai_mathematician_library.sexpr"
    cli = subprocess.run([str(binary), "--lang", "petta@1.0.6", str(entry), str(data)],
                         cwd=ROOT.parent, text=True, capture_output=True, check=False)
    assert cli.returncode == 0, "CLI:\n" + cli.stderr
    assert read_atoms(cli.stdout)[-1] == ["RecallSummary", "2", [
        ["RecallAt", str(k), ["Mean", "0.75"], ["Complete", "1", "0.5"]]
        for k in (8, 16, 32, 64)]], cli.stdout
    missing = subprocess.run([str(binary), "--lang", "petta@1.0.6", str(entry), str(data) + ".missing"],
                             cwd=ROOT.parent, text=True, capture_output=True, check=False)
    assert missing.returncode != 0 and "RecallSummary" not in missing.stdout
    assert "cannot open file" in missing.stdout + missing.stderr
    assert not any(marker in missing.stdout + missing.stderr for marker in (
        "ERROR: LeakSanitizer", "ERROR: AddressSanitizer", "runtime error:",
    )), missing.stderr
    checks += 3
    if args.oracle_dir:
        library, reference = load_reference(args.oracle_dir.resolve())
        paths = [ROOT / "tests/fixtures/ai_mathematician_library.sexpr"]
        if args.corpus:
            paths.append(args.corpus.resolve())
        for path in paths:
            decls = reference_decls(library, path)
            search = reference(decls)
            indices = sorted({0, min(1, len(decls) - 1), len(decls) // 4,
                              len(decls) // 2, 3 * len(decls) // 4, len(decls) - 1}
                             | {d.index for d in decls if d.kind == "THM"} if len(decls) < 20 else
                             {0, 1, 2, 5, len(decls) // 4, len(decls) // 2,
                              3 * len(decls) // 4, len(decls) - 1})
            probes = [(kind, key, default) for kind, table, default in (
                ("Symbol", search.idf, 1.0), ("Token", search.tidf, 0.0),
                ("Feature", search.fidf, 1.0)) for key in sorted(table)]
            probes += [(kind, "unknown-weight", default) for kind, default in
                       (("Symbol", 1.0), ("Token", 0.0), ("Feature", 1.0))]
            report = execute(binary, make_report(path, indices, probes))
            checks += compare_report(report, search, decls, indices)
            print(f"SearchCorpus {path.name} {len(decls)} declarations {len(indices)} goals")
            if args.check_recall:
                report = execute(binary, prelude() +
                    f"!(ai-math:evaluate-recall (ai-math:load-library {quote(path)}))")
                assert report[0] == "RecallSummary"
                selected = [d for d in decls if d.kind == "THM" and d.proof_deps]
                assert int(report[1]) == len(selected)
                rankings = {d.index: [n for n, _ in search.rank(d.index, limit=64)] for d in selected}
                for _, cutoff, mean, complete in report[2]:
                    k = int(cutoff)
                    hits = [set(rankings[d.index][:k]) & d.proof_deps for d in selected]
                    close(mean[1], sum(len(hit) / len(d.proof_deps) for hit, d in zip(hits, selected)) / len(selected), f"recall/{k}")
                    expected_full = sum(hit == d.proof_deps for hit, d in zip(hits, selected))
                    assert int(complete[1]) == expected_full, (k, complete, expected_full)
                    checks += 2
                print(f"SearchRecall {len(selected)} theorems 0 differences")
    elif args.corpus or args.check_recall:
        parser.error("corpus comparisons require --oracle-dir")
    print(f"BinarySHA256 {hashlib.sha256(binary.read_bytes()).hexdigest()}")
    print(f"AiMathematicianSearch {checks} 0")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ValueError, IndexError, TypeError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        sys.exit(1)
