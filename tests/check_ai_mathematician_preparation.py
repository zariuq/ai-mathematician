#!/usr/bin/env python3
"""Compare complete preparation observations, including binary64 scalar bits."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from check_ai_mathematician_library import ROOT, quote


def snapshot(corpus, search):
    return f'''!(import! &self {quote(ROOT / 'phase1/library.metta')})
!(import! &self (library list))
!(import! &self {quote(search)})
(= (prep-check:scalar-bits $values)
   (tensor:encode (tensor:from-values f64 ((size-atom $values)) $values)))
(= (prep-check:metadata (AiSymbolRankPlan $overlap $statement $theorems $definitions $zeroes $guards))
   (RankColumns (tensor:encode $overlap) (tensor:encode $statement)
     (tensor:encode $theorems) (tensor:encode $definitions) (tensor:encode $zeroes)))
!(let* (($context (ai-math:search (ai-math:load-library {quote(corpus)})))
        ((AiSearch $count $facts $weights (AiTraining $training $revision $prefixes)) $context)
        ($rows (collapse (match $weights (AiEntry (Weight $kind $key) $value)
                          (($kind $key) $value))))
        ($totals (union-atom
          (collapse (match $weights (AiEntry (StatementTotal $ordinal) $value)
                      ((Statement $ordinal) $value)))
          (collapse (match $weights (AiEntry (OverlapTotal $ordinal) $value)
                      ((Overlap $ordinal) $value)))))
        ($plans (ai-math:get $weights RankPlanSpace NoRankPlanSpace)))
   (PreparationSnapshot $count
     (collapse (get-atoms $facts))
     (map-atom $rows $row (index-atom $row 0))
     (prep-check:scalar-bits (map-atom $rows $row (index-atom $row 1)))
     (map-atom $totals $row (index-atom $row 0))
     (prep-check:scalar-bits (map-atom $totals $row (index-atom $row 1)))
     (collapse (get-atoms $training))
     (prep-check:metadata (ai-math:get $plans SymbolRankPlan NoSymbolRankPlan))))
'''


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cetta', type=Path, required=True)
    p.add_argument('--corpus', type=Path, required=True)
    p.add_argument('--baseline', type=Path, required=True)
    p.add_argument('--candidate', type=Path, default=ROOT / 'phase1/search.metta')
    p.add_argument('--output', type=Path, default=ROOT / '.cetta/preparation')
    a = p.parse_args()
    a.output.mkdir(parents=True, exist_ok=True)
    inputs = [a.cetta, a.corpus, a.baseline, a.candidate, ROOT / 'phase1/library.metta']
    def hashes():
        return {str(path.resolve()): hashlib.sha256(path.read_bytes()).hexdigest() for path in inputs}
    before = hashes()
    observations = []
    for label, source in [('baseline', a.baseline), ('candidate', a.candidate)]:
        driver = a.output / (label + '.metta')
        driver.write_text(snapshot(a.corpus.resolve(), source.resolve()))
        result = subprocess.run([str(a.cetta.resolve()), '--lang', 'petta@1.0.6', str(driver.resolve())],
                                cwd=ROOT, capture_output=True, timeout=180)
        (a.output / (label + '.stdout')).write_bytes(result.stdout)
        (a.output / (label + '.stderr')).write_bytes(result.stderr)
        assert result.returncode == 0 and not result.stderr, (label, result.returncode, result.stderr)
        assert b'(PreparationSnapshot ' in result.stdout and result.stdout.count(b'CTN1') == 7, (label, result.stdout[:500])
        observations.append(result.stdout)
    assert observations[0] == observations[1], 'preparation observations differ'
    assert before == hashes(), 'qualification inputs changed'
    manifest = dict(inputs=before, bytes=len(observations[0]),
                    observation_sha256=hashlib.sha256(observations[0]).hexdigest(),
                    checks=['catalogue', 'weights', 'ordered totals', 'training occurrences', 'rank columns'])
    (a.output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('AiMathematicianPreparation 5 0', manifest['observation_sha256'])


if __name__ == '__main__':
    main()
