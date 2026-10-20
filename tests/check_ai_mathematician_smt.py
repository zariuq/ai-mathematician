#!/usr/bin/env python3
"""Differential checks for the optional MeTTa SMT-LIB advice bridge."""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import time

from check_ai_mathematician_atp import generated_corpus, prelude as atp_prelude, read_values
from check_ai_mathematician_library import ROOT, quote
from python_oracle import UPSTREAM_V7, oracle_directory
from typed_export_oracle import accept_source_positions


def prelude():
    return atp_prelude() + ''.join(
        f'!(import! &self {quote(ROOT / "phase1" / name)})\n'
        for name in ('induction.metta', 'smt_bridge.metta'))


def execute(binary, source, output, *, extended=False):
    output.mkdir(parents=True, exist_ok=True)
    entry = output / (hashlib.sha256(source.encode()).hexdigest()[:20] + '.metta')
    entry.write_text(source, encoding='utf-8')
    command = [str(binary), '--no-results', '--lang', 'petta@1.0.6']
    if extended:
        command += ['--profile', 'extended']
    ran = subprocess.run(command + [str(entry)],
                         cwd=ROOT, text=True, capture_output=True, check=False)
    (entry.with_suffix('.out')).write_text(ran.stdout, encoding='utf-8')
    (entry.with_suffix('.err')).write_text(ran.stderr, encoding='utf-8')
    assert ran.returncode == 0, (entry, ran.returncode, ran.stderr, ran.stdout[:1000])
    values = read_values(ran.stdout)
    assert len(values) == 1, (entry, ran.stdout[:2000], ran.stderr)
    return values[0]


def load_oracle():
    directory = oracle_directory(UPSTREAM_V7)
    sys.path.insert(0, str(directory))
    import library
    accept_source_positions(library)
    spec = importlib.util.spec_from_file_location('pinned_smt_bridge', directory / 'smt_bridge.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return library, module


def strings(names):
    return '(' + ' '.join(quote(name) for name in names) + ')'


def commands(text):
    return read_values(text)


def canonical(rows):
    # Independent declarations/assertions commute, but occurrences inside
    # terms, binders and commands do not. Keep top-level multiplicity.
    return Counter(json.dumps(row, ensure_ascii=False) for row in rows)


def compare(binary, corpus, library, module, output, *, sample=24):
    declarations = library.load(str(corpus))
    identifiers = {d.name: f'c_{i}' for i, d in enumerate(declarations)}
    module.ident = lambda name: identifiers[name]
    import atp
    thf = atp.THF(declarations)
    atp.attach_prim_indices(thf, str(corpus))
    reference = module.SMT(declarations, thf._prim_idx)
    goals = [d for d in declarations if d.kind == 'THM']
    if sample:
        goals = goals[::max(1, len(goals) // sample)][:sample]
    requests, expected = [], []
    for goal in goals:
        premises = [d.name for d in declarations if d.kind in ('THM', 'AXIOM') and d.index < goal.index][:4]
        for depth in (0, 3):
            try:
                text, ids = reference.problem(goal, premises, None, max_def_depth=depth)
                expected.append((commands(text), ids, None))
            except (atp.Unsupported, KeyError, IndexError) as error:
                expected.append((None, None, str(error)))
            requests.append(f'({goal.index} {strings(premises)} {depth})')
    source = prelude() + f'''
!(let $context (ai-math:thf (ai-math:load-library {quote(corpus)}) {quote(corpus)})
   (println! (map-atom ({' '.join(requests)}) $row
     (let ($i $premises $depth) $row
       (let $problem (ai-math:smt-problem $context (ai-math:thf-lookup $context Ordinal $i)
                       $premises ((definition-depth $depth)))
         (case $problem
           (((AiSMT:Problem $commands $ids $skipped $unexpanded)
             (AiSMT:Rendered $problem (ai-math:smt-text $problem)))
            ($request $request))))))))
'''
    actual = execute(binary, source, output)
    checks, problems = 0, []
    for row, wanted, request in zip(actual, expected, requests, strict=True):
        trees, ids, unsupported = wanted
        if trees is None:
            assert row[0] == 'AiSMT:Request', (request, unsupported, row)
            problems.append(row)
        else:
            assert row[0] == 'AiSMT:Rendered', (request, row)
            _, row, text = row
            assert row[0] == 'AiSMT:Problem', (request, row)
            assert canonical(row[1]) == canonical(trees), (
                request, canonical(row[1]) - canonical(trees), canonical(trees) - canonical(row[1]))
            assert {entry[1]: entry[2] for entry in row[2]} == ids, (request, row[2], ids)
            assert text == '\n'.join(render(command) for command in row[1]) + '\n', request
            assert commands(text) == row[1], request
            checks += len(trees) + 3
            problems.append(row)
        checks += 1
    return checks, problems


def check_motives(binary, corpus, library, module, output):
    declarations = library.load(str(corpus))
    identifiers = {d.name: f'c_{i}' for i, d in enumerate(declarations)}
    module.ident = lambda name: identifiers[name]
    reference = module.SMT(declarations, {9: 'member'})
    import induction
    splits = induction.Inductor(declarations)
    cases, wanted = [], []
    for goal in declarations:
        if not goal.name.startswith('nat_goal_'):
            continue
        for _, xi, gi, _ in splits.splits(goal):
            for motive in (False, True):
                text, ids = reference.problem(goal, ['base_p'], xi, gi, motive=motive)
                cases.append(f'({goal.index} {xi} {gi} {str(motive).lower()})')
                wanted.append(commands(text))
    assert cases, 'missing source-derived nat_ind controls'
    source = prelude() + f'''
!(let $context (ai-math:thf (ai-math:load-library {quote(corpus)}) {quote(corpus)})
   (println! (map-atom ({' '.join(cases)}) $row
     (let ($i $xi $gi $motive) $row
       (ai-math:smt-problem $context (ai-math:thf-lookup $context Ordinal $i)
         ("base_p") ((bridge $xi) (guard $gi) (motive $motive)))))))
'''
    actual = execute(binary, source, output)
    checks = 0
    for row, trees in zip(actual, wanted, strict=True):
        assert row[0] == 'AiSMT:Problem', row
        assert canonical(row[1]) == canonical(trees), (
            canonical(row[1]) - canonical(trees), canonical(trees) - canonical(row[1]))
        checks += len(trees) + 1
    return checks, actual


def check_controls(binary, corpus, output):
    source = prelude() + f'''
!(let* (($context (ai-math:thf (ai-math:load-library {quote(corpus)}) {quote(corpus)}))
        ($goal (AiTHF:Fact 999 THM "control" (IMP (TMH "hp") (TMH "hp")) NoBody))
        ($initial (AiSMT:State () () () ())))
   (println! (
     (ai-math:smt-term $context (DB -1) () $initial)
     (ai-math:smt-term $context (DB 0) () $initial)
     (ai-math:smt-term $context (TPAP (TMH "hpoly") (SET)) () $initial)
     (ai-math:smt-term $context (TMH "missing") () $initial)
     (ai-math:smt-sort (TPVAR 0))
     (ai-math:smt-apply "x" (SET) ((AiSMT:Typed "y" (SET))) $initial)
     (ai-math:smt-problem $context $goal () ((bridge 0)))
     (ai-math:smt-problem $context $goal () ((bridge 90)))
     (ai-math:smt-problem $context $goal () ((motive true)))
     (ai-math:smt-problem $context $goal () ((definition-depth -1)))
     (ai-math:smt-problem $context $goal () ((motive invalid)))
     (ai-math:smt-problem $context $goal () ((unknown true)))
     (ai-math:smt-render ("assert" ("=" "c_1" "c_1")))
     (ai-math:natural 0) (ai-math:natural 1) (ai-math:natural 1.5))))
'''
    actual = execute(binary, source, output)
    assert all(row[0] == 'AiSMT:Request' for row in actual[:12]), actual
    assert actual[12:] == ['(assert (= c_1 c_1))', 'true', 'true', 'false'], actual
    return len(actual)


def check_format(binary, problems, output):
    texts = ['\n'.join(render(row) for row in p[1]) + '\n'
             for p in problems if p[0] == 'AiSMT:Problem']
    negatives = ['(assert)', '(assert (= x))', '(assert (forall () true))',
                 '(declare-fun x () Set)', '(assert true', '(check-sat) trailing)',
                 '(assert (not true false))', '(declare-sort Set 1)',
                 '(assert (exists ((x)) true))']
    # The declaration is a valid positive independently of the complete bridge.
    positives = texts + [negatives.pop(3), '(assert true) (assert (not false)) (check-sat)']
    source = '!(import! &self (library lib_module))\n' + f'''
!(let* (($reader (langdef:load-baked-parser "module-core-reader"))
        ($module (module:read-file $reader "smt-export" {quote(ROOT / 'formats/SMTLibExport.module')}))
        ($closed (langdef:close-parser $reader))
        ($theory (module:assemble $module "Script" LNil LNil OriginViewV1 "smt-export:1"))
        ($language (module:language $theory "SMTLibExport" "SMTScript" (SyntaxLexicalPolicyV1 bnfc-documented)))
        ($syntax (module:language-syntax $language))
        ($parser (langdef:compile-parser $syntax auto))
        ($answers (map-atom {strings(positives + negatives)} $text
          (let $answer (langdef:parser-parse-text $parser $text) (car-atom $answer))))
        ($done (langdef:close-parser $parser)))
   (println! $answers))
'''
    actual = execute(binary, source, output, extended=True)
    assert actual[:len(positives)] == ['ParserAcceptedV1'] * len(positives), actual
    assert all(row in ('ParserRejectedV1', 'ParserLexicalRejectedV1')
               for row in actual[len(positives):]), actual
    return len(actual)


def render(node):
    return '(' + ' '.join(render(item) for item in node) + ')' if isinstance(node, list) else node


def check_solver(binary, vampire, corpus, output):
    source = prelude() + f'''
!(let* (($context (ai-math:thf (ai-math:load-library {quote(corpus)}) {quote(corpus)}))
        ($rows (("identity" (IMP (TMH "hp") (TMH "hp")) ())
                ("modus-ponens" (TMH "hq") ("base_p" "base_imp"))
                ("no-premise" (TMH "hp") ()))) )
   (println! (map-atom $rows $row
     (let* ((($name $statement $premises) $row)
            ($problem (ai-math:smt-problem $context
              (AiTHF:Fact 999 THM $name $statement NoBody) $premises ()))
            ($report (ai-math:smt-vampire $context $problem {quote(vampire)} 2 ())))
       ($name (ai-math:smt-summary $report))))))
'''
    actual = execute(binary, source, output)
    assert [row[0] for row in actual] == ['identity', 'modus-ponens', 'no-premise'], actual
    assert actual[0][1] == ['AiATP:Advice', 'Theorem', [], []], actual
    assert actual[1][1][0:2] == ['AiATP:Advice', 'Theorem'], actual
    assert set(actual[1][1][2]) == {'base_p', 'base_imp'}, actual
    assert actual[2][1][0:2] != ['AiATP:Advice', 'Theorem'], actual
    return 6


def check_induction_solver(binary, vampire, corpus, library, output):
    declarations = library.load(str(corpus))
    goal = next(d for d in declarations if d.name == 'induction_goal')
    source = prelude() + f'''
!(let* (($context (ai-math:thf (ai-math:load-library {quote(corpus)}) {quote(corpus)}))
        ($problem (ai-math:smt-problem $context (ai-math:thf-lookup $context Ordinal {goal.index})
          ("property_zero" "property_step") ((bridge 0) (guard 1) (motive true))))
        ($report (ai-math:smt-vampire $context $problem {quote(vampire)} 5
                   ("-ind" "struct" "-updr" "off" "-nm" "0"))))
   (println! ((ai-math:smt-summary $report)
     (case $report
       (((AiATP:Report $s $p $d $r
           (proc:result $t $c $out $err $cap) $env $payloads)
         (== (get-type (str:find $out "structural_induction")) Number))
        ($other false))))))
'''
    summary, induction = execute(binary, source, output)
    assert summary[:2] == ['AiATP:Advice', 'Theorem'], summary
    assert set(summary[2]) == {'property_zero', 'property_step'}, summary
    assert induction == 'true', (summary, induction)
    return 3


def check_checked_reconstruction(binary, vampire, lean, corpus, output):
    from check_ai_mathematician_prover import prelude as prover_prelude
    adapter = output / 'smt-only-adviser'
    assert adapter.exists()
    source = prover_prelude() + f'''
!(let* (($declarations (ai-math:load-library {quote(corpus)}))
        ($context (ai-math:prover-with $declarations {quote(corpus)} {quote(ROOT)}
          {quote(lean)} {quote(adapter)}
          ((slices (1)) (vampire-seconds 3) (smt true) (induction false)
           (use-duper false) (lean-stages (base)))))
        ($result (ai-math:prove $context "andI")))
   (println! ((car-atom $result) (index-atom $result 5)
     (index-atom (index-atom $result 3) 4)
     (map-atom (index-atom (index-atom $result 3) 5) $slice (car-atom (index-atom $slice 2))))))
'''
    tag, verdict, status, routes = execute(binary, source, output)
    assert tag == 'AiProver:Result' and verdict[0] == 'AiProver:Proved', (tag, verdict)
    assert status == 'Theorem@1' and routes == ['AiATP:Advice', 'AiATP:SMTAdvice'], (status, routes)
    return 3


def benchmark(binary, corpus, library, module, output):
    """Time the same supported problems after one untimed warm-up pass."""
    declarations = library.load(str(corpus))
    identifiers = {d.name: f'c_{i}' for i, d in enumerate(declarations)}
    module.ident = lambda name: identifiers[name]
    import atp
    thf = atp.THF(declarations)
    atp.attach_prim_indices(thf, str(corpus))
    reference = module.SMT(declarations, thf._prim_idx)
    goals = [d for d in declarations if d.kind == 'THM']
    selected, requests, wanted_bytes = [], [], 0
    for goal in goals[::max(1, len(goals) // 24)][:24]:
        premises = [d.name for d in declarations if d.kind in ('THM', 'AXIOM') and d.index < goal.index][:4]
        try:
            text, _ = reference.problem(goal, premises, None)
        except (atp.Unsupported, KeyError, IndexError):
            continue
        selected.append((goal, premises))
        requests.append(f'({goal.index} {strings(premises)})')
        wanted_bytes += len(text.encode())
    assert selected, 'no supported benchmark problems'
    primitives = '(' + ' '.join(f'({i} {quote(n)})' for i, n in thf._prim_idx.items()) + ')'
    source = prelude() + '!(import! &self system)\n' + f'''
(= (smt-bench:work $context $requests)
   (foldl-atom $requests 0 $bytes $row
     (let* ((($i $premises) $row)
            ($goal (ai-math:thf-lookup $context Ordinal $i))
            ($problem (ai-math:smt-problem $context $goal $premises ())))
       (+ $bytes (str:byte-length (ai-math:smt-text $problem))))))
!(let* (($context (ai-math:thf-from-primitives (ai-math:load-library {quote(corpus)})
                    {primitives} (AiTHF:Formats None None)))
        ($requests ({' '.join(requests)}))
        ($warm (smt-bench:work $context $requests))
        ($begin (system:monotonic-ns))
        ($problems (map-atom $requests $row
          (let* ((($i $premises) $row) ($goal (ai-math:thf-lookup $context Ordinal $i)))
            (ai-math:smt-problem $context $goal $premises ()))))
        ($prepared (system:monotonic-ns))
        ($bytes (foldl-atom $problems 0 $n $problem
                  (+ $n (str:byte-length (ai-math:smt-text $problem)))))
        ($end (system:monotonic-ns)))
   (println! (AiSMTBenchmarkNs (- $end $begin) $bytes $warm
     (- $prepared $begin) (- $end $prepared))))
'''
    native, lower, emit, python = [], [], [], []
    for _ in range(3):
        reference_bytes = sum(len(reference.problem(g, p, None)[0].encode()) for g, p in selected)
        assert reference_bytes == wanted_bytes
        begin = time.perf_counter_ns()
        reference_bytes = sum(len(reference.problem(g, p, None)[0].encode()) for g, p in selected)
        python.append(time.perf_counter_ns() - begin)
        observed = execute(binary, source, output)
        assert observed[0] == 'AiSMTBenchmarkNs' and observed[2:4] == [str(wanted_bytes)] * 2, observed
        native.append(int(observed[1]))
        lower.append(int(observed[4])); emit.append(int(observed[5]))
    print(json.dumps({'benchmark': 'smt-prepare-and-render', 'problems': len(selected),
                      'emitted_bytes': wanted_bytes, 'metta_ns': native, 'python_ns': python,
                      'metta_lower_ns': lower, 'metta_render_ns': emit,
                      'cetta_sha256': hashlib.sha256(binary.read_bytes()).hexdigest(),
                      'smt_source_sha256': hashlib.sha256((ROOT / 'phase1/smt_bridge.metta').read_bytes()).hexdigest(),
                      'upstream_revision': UPSTREAM_V7}), flush=True)


def check_controller(binary, vampire, corpus, output):
    from check_ai_mathematician_prover import prelude as prover_prelude
    adapter = output / 'smt-only-adviser'
    adapter.write_text(
        '#!/bin/sh\n'
        'case " $* " in\n'
        '*" --input_syntax tptp "*)\n'
        '  while IFS= read -r line; do :; done\n'
        '  printf "%% SZS status GaveUp for control\\n";;\n'
        f'*) exec {shlex.quote(str(vampire))} "$@";;\n'
        'esac\n', encoding='utf-8')
    adapter.chmod(0o755)
    trace = output / 'smt-controller-traces'
    trace.mkdir(exist_ok=True)
    source = prover_prelude() + ''.join(
        f'!(import! &self {quote(ROOT / "phase1" / name)})\n'
        for name in ('experiment.metta', 'experiment_workers.metta')) + f'''
!(let* (($declarations (ai-math:load-library {quote(corpus)}))
        ($thf (ai-math:thf $declarations {quote(corpus)}))
        ($search (ai-math:search $declarations))
        ($base ((slices (1 2)) (vampire-seconds 2)))
        ($off (ai-math:prover-hints (AiProver $search $thf None {quote(adapter)} $base) "nat_goal_0"))
        ($on (ai-math:prover-hints (AiProver $search $thf None {quote(adapter)}
                (union-atom $base ((smt true) (trace-directory {quote(trace)})))) "nat_goal_0"))
        ($already (ai-math:prover-hints (AiProver $search $thf None {quote(vampire)}
                     (union-atom $base ((smt true)))) "nat_goal_0"))
        ($last-slice (car-atom (list:reverse (index-atom $on 5)))))
   (println! ($off $on $already
     (ai-math:run-trace-field $last-slice)
     (ai-math:workers-config-valid (JsonObject
       ((JsonPair "corpus" "input.sexpr")
        (JsonPair "output" "run") (JsonPair "smt" true))))
     (ai-math:workers-config-valid (JsonObject
       ((JsonPair "corpus" "input.sexpr")
        (JsonPair "output" "run") (JsonPair "smt" "true"))))
     (ai-math:workers-options (JsonObject ((JsonPair "smt" true))) "unused"))))
'''
    off, on, already, trace_field, valid, invalid, options = execute(binary, source, output)
    assert off[0] == on[0] == already[0] == 'AiProver:Hints', (off, on, already)
    assert off[4] == 'GaveUp' and len(off[5]) == 2, off
    assert on[4] == 'Theorem@1' and len(on[5]) == 3, on
    assert on[5][-1][2][0] == 'AiATP:SMTAdvice', on
    archived = on[5][-1][2][1]
    assert archived[0] == 'AiATP:ArchivedAdvice', archived
    assert archived[2][1] == 'ai-math.smtlib-tstp.v1', archived
    assert archived[2][4][1] == 'SMTProblem', archived
    digest = archived[2][4][2]
    problem_file = trace / f'{digest}.problem.smt2'
    assert problem_file.is_file() and hashlib.sha256(problem_file.read_bytes()).hexdigest() == digest
    assert len(already[5]) == 2 and all(s[2][0] != 'AiATP:SMTAdvice' for s in already[5]), already
    assert trace_field[0] == 'AiRun:TraceReference', trace_field
    assert valid == 'true' and invalid == 'false', (valid, invalid)
    assert ['smt', 'true'] in options, options
    return 14


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta', required=True, type=Path)
    parser.add_argument('--corpus', type=Path)
    parser.add_argument('--vampire', type=Path)
    parser.add_argument('--lean', type=Path)
    parser.add_argument('--generated', type=int, default=64)
    parser.add_argument('--output', type=Path, default=ROOT / '.cetta/smt')
    parser.add_argument('--benchmark', action='store_true')
    args = parser.parse_args()
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    library, module = load_oracle()
    fixture = output / 'generated.sexpr'
    fixture.write_text(
        '(PARAM "Empty" "hempty" 0 (SET))\n'
        '(PARAM "ordsucc" "hsucc" 0 (AR (SET) (SET)))\n'
        '(PARAM "nat_p" "hnat" 0 (AR (SET) (PROP)))\n' + generated_corpus(args.generated) +
        '(AXIOM "nat_ind" "hind" 0 (ALL (AR (SET) (PROP)) '
        '(IMP (AP (DB 0) (TMH "hempty")) '
        '(IMP (ALL (SET) (IMP (AP (TMH "hnat") (DB 0)) '
        '(IMP (AP (DB 1) (DB 0)) (AP (DB 1) (AP (TMH "hsucc") (DB 0)))))) '
        '(ALL (SET) (IMP (AP (TMH "hnat") (DB 0)) (AP (DB 1) (DB 0))))))))\n' +
        '(THM "nat_goal_0" "hng0" "png0" 0 (ALL (SET) '
        '(IMP (AP (TMH "hnat") (DB 0)) '
        '(AP (AP (TPAP (TMH "heq") (SET)) (DB 0)) (DB 0)))))\n'
        '(PROOF "nat_goal_0" (KNOWN "hind"))\n' +
        '(THM "nat_goal_1" "hng1" "png1" 0 (ALL (SET) (ALL (SET) '
        '(IMP (AP (TMH "hnat") (DB 1)) (IMP (AP (TMH "hnat") (DB 0)) '
        '(AP (AP (TPAP (TMH "heq") (SET)) (DB 0)) (DB 1)))))))\n'
        '(PROOF "nat_goal_1" (KNOWN "hind"))\n' +
        '(THM "nat_goal_2" "hng2" "png2" 0 (IMP (TMH "hp") (ALL (SET) '
        '(IMP (AP (TMH "hnat") (DB 0)) (TMH "hp")))))\n'
        '(PROOF "nat_goal_2" (KNOWN "hind"))\n' +
        '(THM "nat_goal_3" "hng3" "png3" 0 (ALL (AR (SET) (PROP)) (ALL (SET) '
        '(IMP (AP (TMH "hnat") (DB 0)) (AP (DB 1) (DB 0))))))\n'
        '(PROOF "nat_goal_3" (KNOWN "hind"))\n'
        '(PARAM "property" "hproperty" 0 (AR (SET) (PROP)))\n'
        '(AXIOM "property_zero" "hproperty0" 0 (AP (TMH "hproperty") (TMH "hempty")))\n'
        '(AXIOM "property_step" "hpropertyS" 0 (ALL (SET) '
        '(IMP (AP (TMH "hnat") (DB 0)) (IMP (AP (TMH "hproperty") (DB 0)) '
        '(AP (TMH "hproperty") (AP (TMH "hsucc") (DB 0)))))))\n'
        '(THM "induction_goal" "hindgoal" "pindgoal" 0 (ALL (SET) '
        '(IMP (AP (TMH "hnat") (DB 0)) (AP (TMH "hproperty") (DB 0)))))\n'
        '(PROOF "induction_goal" (KNOWN "hind"))\n',
        encoding='utf-8')
    assert len([d for d in library.load(str(fixture)) if d.kind == 'THM']) == args.generated + 5
    checks, problems = compare(binary, fixture, library, module, output, sample=0)
    count, motives = check_motives(binary, fixture, library, module, output)
    checks += count + check_controls(binary, fixture, output)
    problems += motives
    if args.corpus:
        count, extra = compare(binary, args.corpus.resolve(), library, module, output)
        checks += count
        problems += extra
    checks += check_format(binary, problems, output)
    if args.vampire:
        vampire = Path(shutil.which(str(args.vampire)) or args.vampire).resolve()
        checks += check_solver(binary, vampire, fixture, output)
        checks += check_controller(binary, vampire, fixture, output)
        checks += check_induction_solver(binary, vampire, fixture, library, output)
        if args.lean and args.corpus:
            checks += check_checked_reconstruction(binary, vampire, args.lean.resolve(), args.corpus.resolve(), output)
    print(f'AiSMT {checks}/0')
    if args.benchmark:
        benchmark(binary, args.corpus.resolve() if args.corpus else fixture, library, module, output)


if __name__ == '__main__':
    main()
