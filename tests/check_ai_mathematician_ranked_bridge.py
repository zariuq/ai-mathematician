#!/usr/bin/env python3
"""Compare real ranked, large-slice THF problems against the Python oracle."""
import argparse
import hashlib
from pathlib import Path
import shutil

from check_ai_mathematician_atp import compare_corpus, reference
from check_ai_mathematician_library import ROOT
from check_ai_mathematician_search import SEARCH_SHA256
from python_oracle import oracle_directory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta', type=Path, required=True)
    parser.add_argument('--corpus', type=Path, required=True)
    parser.add_argument('--all', action='store_true', help='Check every goal at all six slice sizes')
    args = parser.parse_args()
    directory = oracle_directory()
    assert hashlib.sha256((directory / 'search.py').read_bytes()).hexdigest() == SEARCH_SHA256
    library, oracle = reference(directory)
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    checks = compare_corpus(binary, args.corpus.resolve(), library, oracle,
                            ROOT / '.cetta/ranked-bridge', all_goals=args.all, ranked=True)
    print(f'AiMathematicianRankedBridge {checks} 0')


if __name__ == '__main__':
    main()
