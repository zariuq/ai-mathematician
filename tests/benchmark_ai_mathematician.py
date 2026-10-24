#!/usr/bin/env python3
"""Measure application stages without printing the corpus or timing the oracle.

The runtime supplies in-process monotonic nanoseconds. On POSIX, wait4 adds
per-process CPU time and peak RSS. Source overrides allow matched comparisons
on the same binary. Timings are observations, never pass/fail thresholds.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

from check_ai_mathematician_library import ROOT, quote, read_atoms


def program(corpus, search_source, atp_source, component, sample_goals=0, library_source=None):
    source = (
        f'!(import! &self {quote(library_source or ROOT / "phase1/library.metta")})\n'
        '!(import! &self (library list))\n'
        '!(import! &self system)\n'
        f'!(import! &self {quote(search_source)})\n'
    )
    if component == "thf":
        source += ('!(import! &self (library lib_tptp))\n'
                   f'!(import! &self {quote(atp_source)})\n')
        # The primitive map is fixed input data, not timed Python translation.
        from check_ai_mathematician_atp import reference
        from python_oracle import oracle_directory
        library, oracle = reference(oracle_directory())
        translator = oracle.THF(library.load(str(corpus)))
        oracle.attach_prim_indices(translator, str(corpus))
        prims = "(" + " ".join(f"({key} {quote(name)})"
                               for key, name in translator._prim_idx.items()) + ")"
        prepare = f"(ai-math:thf-from-primitives $decls {prims})"
        work = """
(let* (($goals (map-atom (filter-atom $decls $decl
                          (== (ai-math:declaration-kind $decl) THM))
                  $decl (ai-math:declaration-index $decl)))
       ($premises (list:take 4 (map-atom (filter-atom $decls $decl
                                (ai-math:contains (AXIOM THM) (ai-math:declaration-kind $decl)))
                                $decl (ai-math:declaration-name $decl)))))
  (foldl-atom $goals (THF 0 0 0) $outer $index
    (foldl-atom (3 All) $outer $inner $depth
      (let (THF $profiles $bytes $requests) $inner
        (case (ai-math:thf-problem $context $index $premises $depth)
          (((AiTHF:Problem $records $ids $skipped $frontier)
            (THF (+ $profiles 1)
              (+ $bytes (str:byte-length (ai-math:thf-text $context
                (AiTHF:Problem $records $ids $skipped $frontier)))) $requests))
           ($request (THF (+ $profiles 1) $bytes (+ $requests 1)))))))))
"""
    else:
        prepare = "(ai-math:search $decls)"
        work = "(size-atom (ai-math:search-facts $context))"
        if component in ("recall", "recall-reference", "search-stages"):
            # Use operations shared by both source versions, including the
            # baseline before search-recall was introduced.
            selected = '(ai-math:search-facts $context)'
            if sample_goals:
                from check_ai_mathematician_search import load_reference
                from python_oracle import oracle_directory
                library, _ = load_reference(oracle_directory())
                goals = [d.index for d in library.load(str(corpus)) if d.kind == 'THM' and d.proof_deps]
                count = min(sample_goals, len(goals))
                indices = [goals[i * len(goals) // count] for i in range(count)]
                selected = ('(filter-atom (ai-math:search-facts $context) $fact '
                            '(ai-math:contains (' + ' '.join(map(str, indices)) + ') '
                            '(ai-math:declaration-index $fact)))')
            work = """
(let* (($cutoffs (8 16 32 64))
       ($samples (ai-math:recall-samples $context SAMPLED_FACTS $cutoffs)))
  (RecallSummary (size-atom $samples) (ai-math:recall-columns $samples $cutoffs 0)))
""".replace('SAMPLED_FACTS', selected)
            if component == "recall-reference":
                work = """
(let* (($cutoffs (8 16 32 64))
       ($theorems (filter-atom SAMPLED_FACTS $decl
         (and (== (ai-math:declaration-kind $decl) THM)
              (> (size-atom (ai-math:declaration-dependencies $decl)) 0))))
       ($maximum (foldl-atom $cutoffs 0 $best $k (if (> $k $best) $k $best)))
       ($samples (map-atom $theorems $decl
         (let* (($index (ai-math:declaration-index $decl))
                ($goal (ai-math:search-goal $context $index))
                ($truth (ai-math:declaration-dependencies $decl))
                ($ranked (ai-math:entry-names
                  (ai-math:rank-for $context $index $goal $maximum ()))))
           (map-atom $cutoffs $k
             (let $got (size-atom
                   (intersection-atom (list:take $k $ranked) $truth))
               (AiRecall $k (/ $got (size-atom $truth))
                 (if (== $got (size-atom $truth)) 1 0))))))))
  (RecallSummary (size-atom $samples)
    (ai-math:recall-columns $samples $cutoffs 0)))
""".replace('SAMPLED_FACTS', selected)
            if component == "search-stages":
                work = """
(let $goals (map-atom (filter-atom SAMPLED_FACTS $fact
                       (and (== (ai-math:declaration-kind $fact) THM)
                            (not (== (ai-math:declaration-dependencies $fact) ()))))
                     $fact (ai-math:declaration-index $fact))
  (SearchStages
    (map-atom (Bayes KNN Overlap Background ReferenceRank PackedRank) $stage
      (let* (($begin (system:monotonic-ns))
             ($rows (foldl-atom $goals 0 $rows $index
                      (let* (($goal (ai-math:search-goal $context $index))
                             ($answer (case $stage
                               ((Bayes (ai-math:naive-bayes-prefix $context $goal $index 10.0 -4.0 1.0))
                                (KNN (ai-math:knn-prefix $context
                                       (ai-math:declaration-symbols $goal) $index 24))
                                (Overlap (ai-math:overlap-contributions $context
                                           (ai-math:declaration-symbols $goal) $index))
                                (Background
                                  (foldl-atom (ai-math:search-before $context $index)
                                    () $out $fact
                                    (union-atom $out
                                      (ai-math:fact-background-contributions
                                        $context $goal $index $fact 0.0 1.0))))
                                (PackedRank
                                  (ai-math:rank-packed-default
                                    $context $index $goal 64))
                                (ReferenceRank
                                  (ai-math:rank-for
                                    $context $index $goal 64 ()))))))
                        (+ $rows (size-atom $answer)))))
             ($end (system:monotonic-ns)))
        (SearchStage $stage (- $end $begin) $rows)))))
""".replace('SAMPLED_FACTS', selected)
    expected_context = "AiTHF" if component == "thf" else "AiSearch"
    return source + f"""
!(let* (($start (system:monotonic-ns))
        ($decls (ai-math:load-library {quote(corpus)}))
        ($loaded (system:monotonic-ns)))
   (case $decls
     (((Error $reason $where) (AiMathBenchmarkFault $reason $where))
      ($items
       (let* (($context {prepare})
              ($prepared (system:monotonic-ns))
              ($result (if (== (index-atom $context 0) {expected_context})
                         {work} (AiMathBenchmarkFault UnpreparedContext)))
              ($finished (system:monotonic-ns)))
         (AiMathTiming (- $loaded $start) (- $prepared $loaded)
                       (- $finished $prepared) $result))))))
"""


def measure(binary, source, output, stem):
    script = output / f"{stem}.metta"
    script.write_text(source, encoding="utf-8")
    started = time.perf_counter_ns()
    with (output / f"{stem}.out").open("w") as stdout, (output / f"{stem}.err").open("w") as stderr:
        child = subprocess.Popen([str(binary), "--lang", "petta@1.0.6", str(script)],
                                 cwd=ROOT, stdout=stdout, stderr=stderr)
        _, status, usage = os.wait4(child.pid, 0)
        child.returncode = os.waitstatus_to_exitcode(status)
    whole_ns = time.perf_counter_ns() - started
    if child.returncode:
        diagnostic = (output / f"{stem}.err").read_text().strip()
        raise RuntimeError(f"benchmark failed: {stem}, status {child.returncode}: {diagnostic}")
    values = read_atoms((output / f"{stem}.out").read_text())
    if not values or values[-1][0] != "AiMathTiming":
        raise RuntimeError(f"incomplete benchmark: {stem}")
    _, load_ns, prepare_ns, work_ns, result = values[-1]
    if isinstance(result, list) and result and result[0] == "AiMathBenchmarkFault":
        raise RuntimeError(f"benchmark did not prepare its context: {stem}")
    return dict(load_ns=int(load_ns), prepare_ns=int(prepare_ns), work_ns=int(work_ns),
                whole_ns=whole_ns, whole_scope="parent_process_start_to_exit",
                user_s=usage.ru_utime, system_s=usage.ru_stime,
                peak_rss_kib=usage.ru_maxrss, result=result)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def semantic_result(result):
    """Stage durations are measurements, not part of the repeated answer."""
    if isinstance(result, list) and result and result[0] == "SearchStages":
        return [result[0], [[row[0], row[1], row[3]] for row in result[1]]]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", required=True, type=Path)
    parser.add_argument("--corpus", required=True, type=Path)
    parser.add_argument("--search-source", type=Path, default=ROOT / "phase1/search.metta")
    parser.add_argument("--library-source", type=Path, default=ROOT / "phase1/library.metta")
    parser.add_argument("--atp-source", type=Path, default=ROOT / "phase1/atp.metta")
    parser.add_argument("--component", choices=("setup", "recall", "recall-reference", "thf", "search-stages"), default="recall")
    parser.add_argument("--repeat", type=int, default=1)
    parser.add_argument("--sample-goals", type=int, default=0,
                        help="Evenly sample recall goals; zero measures all eligible goals")
    parser.add_argument("--output", type=Path, default=ROOT / ".cetta/performance")
    args = parser.parse_args()
    if args.repeat < 1:
        parser.error("--repeat must be positive")
    if args.sample_goals < 0:
        parser.error("--sample-goals must be nonnegative")
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    corpus, search_source, atp_source, library_source = (path.resolve() for path in
        (args.corpus, args.search_source, args.atp_source, args.library_source))
    if not corpus.is_file():
        parser.error("--corpus must name an existing file")
    metadata = dict(binary_sha256=digest(binary), corpus_sha256=digest(corpus),
                    search_sha256=digest(search_source), atp_sha256=digest(atp_source),
                    library_sha256=digest(library_source),
                    component=args.component, sample_goals=args.sample_goals)
    source = program(corpus, search_source, atp_source, args.component, args.sample_goals, library_source)
    args.output.mkdir(parents=True, exist_ok=True)
    observations = []
    for index in range(args.repeat):
        stem = f"{args.component}-{index}"
        observation = dict(metadata, **measure(binary, source, args.output, stem))
        if any(digest(path) != metadata[key] for path, key in (
                (binary, 'binary_sha256'), (corpus, 'corpus_sha256'),
                (search_source, 'search_sha256'), (atp_source, 'atp_sha256'),
                (library_source, 'library_sha256'))):
            raise RuntimeError('benchmark input changed during measurement')
        if observations and semantic_result(observation["result"]) != semantic_result(observations[0]["result"]):
            raise RuntimeError("repeated benchmark changed its answer")
        observations.append(observation)
        print(json.dumps(observation), flush=True)
    (args.output / "measurements.json").write_text(json.dumps(observations, indent=2) + "\n")


if __name__ == "__main__":
    main()
