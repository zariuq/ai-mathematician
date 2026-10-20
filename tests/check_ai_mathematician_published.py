#!/usr/bin/env python3
"""Recheck published upstream scripts; no solver or model requests."""
import argparse
import json
from pathlib import Path
import shutil

from check_ai_mathematician_itp import execute, prelude
from check_ai_mathematician_library import ROOT, quote


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta', type=Path, required=True)
    parser.add_argument('--corpus', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--input', type=Path, action='append')
    parser.add_argument('--limit', type=int, default=0, help='Per-input sample size; zero checks all')
    parser.add_argument('--wall-ms', type=int, default=30000)
    parser.add_argument('--heartbeats', type=int, default=1000000)
    args = parser.parse_args()
    if min(args.limit, args.wall_ms, args.heartbeats) < 0:
        parser.error('counts must be nonnegative')
    files = args.input or [ROOT / 'results/llm_proofs_verified.json', ROOT / 'results/v6v7_verified.json']
    requests = []
    for path in files:
        rows = json.loads(path.read_text())['verified']
        selected = list(rows.items())[:args.limit or len(rows)]
        for target, row in selected:
            if row.get('prelude'):
                raise ValueError(f'{target}: a nonempty prelude requires separate reconstruction')
            requests.append((target, row['script']))
    if not requests:
        raise ValueError('no published proofs selected')
    directory = ROOT / '.cetta/published'
    directory.mkdir(parents=True, exist_ok=True)
    literal = '(' + ' '.join(f'({quote(target)} {quote(script)})' for target, script in requests) + ')'
    source = prelude() + f'''
!(let* (($declarations (ai-math:load-library {quote(args.corpus.resolve())}))
        ($context (ai-math:itp $declarations {quote(ROOT)} {quote(args.lean.resolve())})))
   (map-atom {literal} $row (let ($target $script) $row
     ($target (ai-math:itp-check-with $context $target $script
       (AiITP:Budget {args.wall_ms} {args.heartbeats} 8000))))))
'''
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    answers = execute(binary, source, directory)
    for (target, _), actual in zip(requests, answers, strict=True):
        assert actual[0] == target and actual[1][:2] == ['AiITP:Accepted', target], actual
    print(f'AiMathematicianPublished {len(requests)} 0')


if __name__ == '__main__':
    main()
