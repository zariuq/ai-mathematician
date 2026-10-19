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


def program(corpus, search_source, atp_source, component):
    source = (
        f'!(import! &self {quote(ROOT / "phase1/library.metta")})\n'
        '!(import! &self (library list))\n'
        '!(import! &self system)\n'
        f'!(import! &self {quote(search_source)})\n'
    )
    if component == "thf":
        source += ('!(import! &self (library lib_tptp))\n'
                   f'!(import! &self {quote(atp_source)})\n')
        # The primitive map is fixed input data, not timed Python translation.
        from check_ai_mathematician_atp import reference
        library, oracle = reference(ROOT / "phase1")
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
        if component == "recall":
            # Use operations shared by both source versions, including the
            # baseline before search-recall was introduced.
            work = """
(let* (($cutoffs (8 16 32 64))
       ($samples (ai-math:recall-samples $context (ai-math:search-facts $context) $cutoffs)))
  (RecallSummary (size-atom $samples) (ai-math:recall-columns $samples $cutoffs 0)))
"""
    return source + f"""
!(let* (($start (system:monotonic-ns))
        ($decls (ai-math:load-library {quote(corpus)}))
        ($loaded (system:monotonic-ns)))
   (case $decls
     (((Error $reason $where) (AiMathBenchmarkFault $reason $where))
      ($items
       (let* (($context {prepare})
              ($prepared (system:monotonic-ns))
              ($result {work})
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
    return dict(load_ns=int(load_ns), prepare_ns=int(prepare_ns), work_ns=int(work_ns),
                whole_ns=whole_ns, user_s=usage.ru_utime, system_s=usage.ru_stime,
                peak_rss_kib=usage.ru_maxrss, result=result)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", required=True, type=Path)
    parser.add_argument("--corpus", required=True, type=Path)
    parser.add_argument("--search-source", type=Path, default=ROOT / "phase1/search.metta")
    parser.add_argument("--atp-source", type=Path, default=ROOT / "phase1/atp.metta")
    parser.add_argument("--component", choices=("setup", "recall", "thf"), default="recall")
    parser.add_argument("--repeat", type=int, default=1)
    parser.add_argument("--output", type=Path, default=ROOT / ".cetta/performance")
    args = parser.parse_args()
    if args.repeat < 1:
        parser.error("--repeat must be positive")
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    corpus, search_source, atp_source = (path.resolve() for path in
                                        (args.corpus, args.search_source, args.atp_source))
    if not corpus.is_file():
        parser.error("--corpus must name an existing file")
    metadata = dict(binary_sha256=digest(binary), corpus_sha256=digest(corpus),
                    search_sha256=digest(search_source), atp_sha256=digest(atp_source),
                    component=args.component)
    source = program(corpus, search_source, atp_source, args.component)
    args.output.mkdir(parents=True, exist_ok=True)
    observations = []
    for index in range(args.repeat):
        stem = f"{args.component}-{index}"
        observation = dict(metadata, **measure(binary, source, args.output, stem))
        if observations and observation["result"] != observations[0]["result"]:
            raise RuntimeError("repeated benchmark changed its answer")
        observations.append(observation)
        print(json.dumps(observation), flush=True)
    (args.output / "measurements.json").write_text(json.dumps(observations, indent=2) + "\n")


if __name__ == "__main__":
    main()
