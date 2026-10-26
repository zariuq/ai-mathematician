#!/usr/bin/env python3
"""Record complete score observations, with optional same-schedule comparison.

The approved implementation sums union weights through ordered prepared totals.
Python sums the union's elements directly. Sparse Bayes also reassociates a
missing-feature baseline and corrections, which can reorder close Bayes scores
and change rank bonuses. An explicit reference compares every native score bit
when a change promises the same schedule. Without one this records a receipt,
not an immutable numerical policy or a claim of bitwise Python equivalence.
"""
import argparse
import hashlib
from pathlib import Path
import subprocess

from check_ai_mathematician_library import ROOT, quote

CORPUS_SHA256 = '2faadf2eb53d9b746e93f8ca89921fbba89b51f66c4ffc7471c6dd2c6e2484d6'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta', type=Path, required=True)
    parser.add_argument('--corpus', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=ROOT / '.cetta/score-schedule')
    parser.add_argument('--reference-output', type=Path,
                        help='Prior complete observation for an explicitly same-schedule change')
    parser.add_argument('--library-root', type=Path, default=ROOT,
                        help='working directory for standard-library discovery by a frozen executable')
    args = parser.parse_args()
    assert hashlib.sha256(args.corpus.read_bytes()).hexdigest() == CORPUS_SHA256, 'unqualified corpus'
    source = f'''!(import! &self {quote(ROOT / 'phase1/library.metta')})
!(import! &self (library list))
!(import! &self {quote(ROOT / 'phase1/search.metta')})
!(let* (($decls (ai-math:load-library {quote(args.corpus.resolve())}))
        ($search (ai-math:search $decls))
        ($goals (filter-atom $decls $decl
          (and (== (ai-math:declaration-kind $decl) THM)
               (> (size-atom (ai-math:declaration-dependencies $decl)) 0)))))
   (OrderedRankBits
     (map-atom $goals $goal
       (let* (($index (ai-math:declaration-index $goal))
              ($rows (ai-math:rank $search $index 64))
              ($scores (tensor:from-values f64 ((size-atom $rows))
                (map-atom $rows $entry (index-atom $entry 1)))))
         (RankAt $index (map-atom $rows $entry (index-atom $entry 0))
           (tensor:encode $scores))))))
'''
    args.output.mkdir(parents=True, exist_ok=True)
    result = subprocess.run([str(args.cetta.resolve()), '--lang', 'petta', '-e', source],
                            cwd=args.library_root, capture_output=True)
    (args.output / 'scores.bin').write_bytes(result.stdout)
    (args.output / 'stderr.log').write_bytes(result.stderr)
    assert result.returncode == 0 and not result.stderr, (result.returncode, result.stderr)
    assert result.stdout.count(b'(RankAt ') == result.stdout.count(b'CTN1') == 966
    digest = hashlib.sha256(result.stdout).hexdigest()
    if args.reference_output:
        assert result.stdout == args.reference_output.read_bytes(), ('same-schedule observation changed', digest)
    print('ScoreObservationSHA256', digest)
    print('AiMathematicianScoreSchedule 966 0')


if __name__ == '__main__':
    main()
