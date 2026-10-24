#!/usr/bin/env python3
"""Python search timing with the same corpus, sampling and recall observation."""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import time

from check_ai_mathematician_search import load_reference, reference_decls
from python_oracle import PYTHON_V4, oracle_directory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--corpus', type=Path, required=True)
    parser.add_argument('--sample-goals', type=int, default=32)
    args = parser.parse_args()
    if args.sample_goals < 0:
        parser.error('--sample-goals must be nonnegative')
    directory = oracle_directory()
    library, search_type = load_reference(directory)
    corpus = args.corpus.resolve()
    cpu_start = resource.getrusage(resource.RUSAGE_SELF)
    started = time.perf_counter_ns()
    declarations = reference_decls(library, corpus)
    loaded = time.perf_counter_ns()
    search = search_type(declarations)
    prepared = time.perf_counter_ns()
    eligible = [d for d in declarations if d.kind == 'THM' and d.proof_deps]
    count = min(args.sample_goals, len(eligible)) if args.sample_goals else len(eligible)
    selected = [eligible[i * len(eligible) // count] for i in range(count)]
    cutoffs = (8, 16, 32, 64)
    columns = {k: [0.0, 0] for k in cutoffs}
    for goal in selected:
        ranked = [name for name, _ in search.rank(goal.index, limit=max(cutoffs))]
        for k in cutoffs:
            hit = set(ranked[:k]) & goal.proof_deps
            columns[k][0] += len(hit) / len(goal.proof_deps)
            columns[k][1] += hit == goal.proof_deps
    finished = time.perf_counter_ns()
    usage = resource.getrusage(resource.RUSAGE_SELF)
    result = ['RecallSummary', str(count),
              [['RecallAt', str(k), ['Mean', str(total / count if count else 0.0)],
                ['Complete', str(complete), str(complete / count if count else 0.0)]]
               for k, (total, complete) in columns.items()]]
    print(json.dumps(dict(
        engine='python', oracle_revision=PYTHON_V4,
        search_sha256=hashlib.sha256((directory / 'search.py').read_bytes()).hexdigest(),
        corpus_sha256=hashlib.sha256(corpus.read_bytes()).hexdigest(),
        sample_goals=args.sample_goals,
        load_ns=loaded-started, prepare_ns=prepared-loaded,
        work_ns=finished-prepared, whole_ns=finished-started,
        whole_scope='load_prepare_work',
        user_s=usage.ru_utime-cpu_start.ru_utime,
        system_s=usage.ru_stime-cpu_start.ru_stime,
        peak_rss_kib=usage.ru_maxrss, result=result)), flush=True)


if __name__ == '__main__':
    main()
