#!/usr/bin/env python3
"""Bounded experimental-algorithm controls; no model calls or discovery sweep."""
import argparse
import ast
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys
import tempfile
import threading
from types import ModuleType, SimpleNamespace

from check_ai_mathematician_atp import read_values
from check_ai_mathematician_library import ROOT, quote, read_atoms
from check_ai_mathematician_prover import prelude as core_prelude
from python_oracle import UPSTREAM_V9, oracle_directory


def prelude():
    return core_prelude() + '!(import! &self io)\n!(import! &self (library embedding))\n' + ''.join(
        f'!(import! &self {quote(ROOT / "phase1" / file)})\n' for file in
        ('experiment.metta', 'lean_export.metta', 'prop_synth.metta', 'research_strategies.metta',
         'http_transport.metta', 'llm_transport.metta', 'llm.metta', 'proof_state.metta',
         'incremental.metta', 'alternative_atp.metta', 'proof_plans.metta', 'decomposition.metta',
         'oracle_chains.metta', 'hybrid_induction.metta', 'embedding_python.metta', 'proof_advice.metta',
         'research_analysis.metta', 'research.metta'))


def execute(binary, source):
    ran = subprocess.run([str(binary), '--lang', 'petta', '-e', source],
                         cwd=ROOT, text=True, capture_output=True, check=False)
    assert ran.returncode == 0, ran.stderr or ran.stdout[:2000]
    values = read_values(ran.stdout)
    imports = source.count('!(import!')
    assert values[:imports] == ['true'] * imports and len(values) == imports + 1, ran.stdout[:3000]
    return values[-1]


def oracle(name, folder='phase1/experiments'):
    path = folder + '/' + name + '.py'
    source = subprocess.check_output(['git', 'show', UPSTREAM_V9 + ':' + path], cwd=ROOT, text=True)
    module = ModuleType('original_' + name)
    module.__file__ = str(ROOT / path)
    sys.modules[module.__name__] = module
    exec(compile(source, module.__file__, 'exec'), module.__dict__)
    return module


def term(node):
    if isinstance(node, list):
        return '(' + ' '.join(map(term, node)) + ')'
    return node if node.isidentifier() or node.lstrip('-').isdigit() else quote(node)


def prop_controls(binary, args):
    source = oracle('prop_synth')
    rng = random.Random(20261024)
    def formula(depth):
        if not depth or rng.randrange(3) == 0:
            return ['PRIM', str(rng.randrange(3))]
        return ['IMP', formula(depth - 1), formula(depth - 1)]
    goals = [['ALL', ['PROP'], ['IMP', ['DB', '0'], ['DB', '0']]],
             ['IMP', ['PRIM', '0'], ['PRIM', '1']]]
    for _ in range(24):
        a, b = formula(2), formula(1)
        goals.extend([['IMP', a, a], ['IMP', a, ['IMP', b, a]]])
    rows = ' '.join(term(goal) for goal in goals)
    observed = execute(binary, prelude() + f'''
!(let $synth (ai-math:prop-synth () 6)
   (map-atom ({rows}) $goal (ai-math:prop-prove $synth $goal)))
''')
    synth = source.Synth([], max_depth=6)
    for goal, answer in zip(goals, observed, strict=True):
        expected = synth.prove(goal)
        assert answer == (['AiProp:Built', expected] if expected else 'AiProp:NoProof'), (goal, answer, expected)
    checks = len(goals)
    shifted = ['ALL', ['PROP'], ['IMP', ['DB', '0'], ['AP', ['DB', '2'], ['DB', '1']]]]
    observed = execute(binary, prelude() + f'''!(Cases
      (ai-math:prop-shift {term(shifted)} 2 0)
      (ai-math:prop-substitute {term(shifted)} 0 (DB 3))
      (ai-math:prop-synth () -1))\n''')
    assert observed == ['Cases', source.shift(shifted, 2), source.subst(shifted, 0, ['DB', '3']),
                        ['AiProp:Fault', 'invalid-depth']], observed
    checks += 3
    if args.corpus:
        observed = execute(binary, prelude() + f'''
!(let* (($ds (ai-math:load-library {quote(args.corpus)}))
        ($synth (ai-math:prop-synth $ds 10))
        ($itp (ai-math:itp $ds {quote(ROOT)} {quote(args.lean)})))
   (map-atom ("andI" "orIL" "orIR") $target
     (ai-math:prop-check $synth $itp
       (car-atom (filter-atom $ds $d (== (ai-math:declaration-name $d) $target)))
       (AiITP:Budget 30000 200000 8000))))
''')
        for row in observed:
            assert row[0] == 'AiProp:Result' and row[-1][0] == 'AiITP:Accepted', row
            assert row[3].startswith('exact ') and 'grind' not in row[3], row
        checks += 6
    return checks


def strategy_controls(binary):
    sys.path.insert(0, str(oracle_directory(UPSTREAM_V9)))
    source = oracle('duper2')
    cases = [([], [], []), (['andI'], ['and'], []),
             (['orIL', 'andI', 'lamI'], ['or'], ['or']),
             (["x'", 'λ'], [], [])]
    observed = execute(binary, prelude() + '!(Cases ' + ' '.join(
        '(ai-math:duper2-tactics ' + ' '.join('(' + ' '.join(map(quote, xs)) + ')' for xs in case) + ')'
        for case in cases) + ')\n')
    for case, answer in zip(cases, observed[1:], strict=True):
        expected = [['AiITP:Candidate', name, script] for name, script in source.duper2_tactics(*case)]
        assert answer == expected, (case, answer, expected)
    return len(cases)


def state_controls(binary, args):
    if not args.corpus:
        return 0
    observed = execute(binary, prelude() + f'''
!(let* (($ds (ai-math:load-library {quote(args.corpus)}))
        ($itp (ai-math:itp $ds {quote(ROOT)} {quote(args.lean)})))
   (ai-math:probe-batch $itp "orIL"
     ((AiITP:Candidate "open" "intro P Q hp")
      (AiITP:Candidate "closed" "intro P Q hp r f g\\nexact f hp")
      (AiITP:Candidate "invalid" "exact nonexistent")
      (AiITP:Candidate "leaking" "exact orIL")) (AiITP:Budget 30000 200000 8000)))
''')
    assert observed[:2] == ['AiProbe:Batch', 'orIL'], observed
    rows = observed[2]
    assert [row[1] for row in rows] == ['open', 'closed', 'invalid', 'leaking'], rows
    assert rows[0][2][0] == 'AiProbe:Open' and len(rows[0][2][1]) == 1, rows[0]
    assert 'hp : P' in rows[0][2][1][0] and '⊢ or P Q' in rows[0][2][1][0], rows[0]
    assert rows[1][2][0] == 'AiProbe:Closed', rows[1]
    assert rows[2][2][0] == rows[3][2][0] == 'AiProbe:Error', rows[2:]
    return 6


def incremental_controls(binary, args):
    from check_ai_mathematician_itp import load_oracles
    from check_ai_mathematician_search import CanonicalSet, reference_decls
    from check_ai_mathematician_upstream import load
    directory = oracle_directory(UPSTREAM_V9)
    library, _ = load_oracles()
    fixture = ROOT / 'tests/fixtures/ai_mathematician_library.sexpr'
    declarations = reference_decls(library, fixture)
    search_module = load('search', directory)
    class CanonicalSearch(search_module.Search):
        @staticmethod
        def _toks(name):
            return CanonicalSet(search_module.Search._toks(name))
    search = CanonicalSearch(declarations)
    sys.path.insert(0, str(directory))
    original = oracle('incremental')
    prover = SimpleNamespace(search=search, by_name={d.name: d for d in declarations})
    goal = prover.by_name['replaced']
    samples = [('p✝ : Prop\nh : In\n⊢ «uses_future» -> p', 2, {'premise'}, 3, ['uses_future'], ['premise', 'later']),
               ('unknown : Prop\n⊢ unknown', 0, set(), 0, [], [])]
    def names(xs):
        return '(' + ' '.join(map(quote, xs)) + ')'
    observed = execute(binary, prelude() + f'''
!(let* (($ds (ai-math:load-library {quote(fixture)}))
        ($search (ai-math:search $ds)) ($catalog (new-space))
        ($indexed (map-atom $ds $d (ai-math:put $catalog (ai-math:declaration-name $d)
          (AiITP:Declaration (ai-math:declaration-index $d) (ai-math:declaration-kind $d)))))
        ($itp (AiITP $catalog "unused" "unused" core)))
  (Cases {' '.join(f'(ai-math:incremental-steps $search $itp "replaced" {quote(st)} {h} {names(sorted(u))} {k} {names(ds)} {names(seed)})' for st,h,u,k,ds,seed in samples)}))
''')
    for args_, actual in zip(samples, observed[1:], strict=True):
        state, have, used, k, definitions, seed = args_
        expected = [['AiITP:Candidate', label, script] for label, script in
                    original.steps(prover, goal, state, have, used, k=k, defs=definitions, seed=seed)]
        assert actual == expected, (actual, expected)
    checks = len(samples)
    if args.corpus:
        observed = execute(binary, prelude() + f'''
!(let* (($ds (ai-math:load-library {quote(args.corpus)}))
        ($itp (ai-math:itp $ds {quote(ROOT)} {quote(args.lean)}))
        ($context (AiProver (ai-math:search $ds) None $itp None ()))
        ($hints (AiProver:Hints (()) ("or") ("or") "fixture" ())))
  (Cases (ai-math:incremental-prove $context "orIL" $hints ((max-probes 2) (chunk-size 2) (k 1)))
         (ai-math:incremental-prove $context "orIL" $hints ((max-depth 0) (max-probes 1)))
         (ai-math:incremental-prove $context "orIL" $hints ((max-probes 0)))))
''')
        assert observed[1][0] == 'AiInc:Result' and observed[1][2][0] == 'AiProver:Proved', observed[1]
        assert int(observed[1][3][1]) <= 2 and len(observed[1][2]) == 7, observed[1]
        assert observed[2][0] == 'AiInc:Result' and observed[2][2][0] == 'AiProver:NotProved', observed[2]
        assert observed[2][3][1] == '1', observed[2]
        assert observed[3] == ['AiInc:Fault', 'invalid-policy'], observed[3]
        checks += 5
    return checks


def alternative_atp_controls(binary, args):
    declarations = '''((Decl 0 PARAM "p" "hp" (PROP) NoBody () () ())
      (Decl 1 AXIOM "premise" "ha" (TMH "hp") NoBody ("p") () ())
      (Decl 2 THM "goal" "hg" (TMH "hp") NoBody ("p") () ()))'''
    text = '% SZS status Theorem\n'
    observed = execute(binary, prelude() + f'''
!(let* (($context (ai-math:thf-from-primitives {declarations} ()))
        ($problem (ai-math:thf-problem $context 2 ("premise")))
        ($out {quote(text)}) ($size (str:byte-length $out)))
   (Cases (ai-math:zipper-observation $context $problem
       (proc:result (proc:exited 0) proc:normal $out ""
         (proc:capture $size $size 0 0 proc:eof proc:eof (proc:input 0 0))))
     (ai-math:zipper-observation $context $problem
       (proc:result (proc:signaled 15) proc:cancelled "" "" ()))
     (ai-math:zipperposition $context $problem "unused" -1 "")))
''')
    assert observed[1][0] == 'AiATP:ZipperReport' and observed[1][1][0] == 'AiATP:PayloadInterpretationNeeded', observed
    assert observed[2][1][0] == 'AiATP:UnfinishedOrFaulted', observed
    assert observed[3] == ['AiATP:ZipperFault', 'invalid-policy'], observed
    checks = 3
    if args.zipper:
        observed = execute(binary, prelude() + f'''
!(let* (($context (ai-math:thf-from-primitives {declarations} ()))
        ($problem (ai-math:thf-problem $context 2 ("premise"))))
   (ai-math:zipperposition $context $problem {quote(args.zipper)} 2 ""))
''')
        assert observed[0] == 'AiATP:ZipperReport' and observed[1] == ['AiATP:Advice', 'Theorem', ['premise'], []], observed
        checks += 1
    return checks


def plan_controls(binary, args):
    pure = execute(binary, prelude() + '''!(Cases
      (ai-math:plan-valid (AiProofPlan "intro P" ((AiClaim "h" "P"))))
      (ai-math:plan-valid (AiProofPlan "" ((AiClaim "h" "P") (AiClaim "h" "Q"))))
      (ai-math:plan-failure () (AiITP:Unfinished "g" cancelled ()))
      (ai-math:plan-failure () (AiITP:Fault "g" malformed ()))
      (ai-math:plan-failure () (unsupported-result 1))
      (ai-math:derived-winner ((AiITP:Candidate "x" "skip"))
        ((AiITP:CaseAttempt 0 "x" (AiITP:Unfinished "g" deadline ())))))\n''')
    assert pure[1:3] == ['true', 'false'], pure
    assert [row[0] for row in pure[3:]] == ['AiPlan:Unfinished', 'AiPlan:Fault', 'AiPlan:Fault', 'AiDerived:Unfinished'], pure
    # These are outcome-selection controls, not independent proof receipts.
    accepted = '(AiITP:CaseAccepted "g" 0 1 () ())'
    unfinished = '(AiITP:Unfinished "g" deadline ())'
    fault = '(AiITP:Fault "g" malformed ())'
    rejected = '(AiITP:Rejected "g" lean-errors ())'
    pairs = [(unfinished, accepted), (fault, accepted), (rejected, accepted),
             (accepted, accepted), (unfinished, rejected), (unfinished, fault), (rejected, rejected)]
    choices = execute(binary, prelude() + '!(Cases ' + ' '.join(
        '(ai-math:derived-winner ((AiITP:Candidate "first" "a") (AiITP:Candidate "later" "b")) '
        f'((AiITP:CaseAttempt 0 "first" {first}) (AiITP:CaseAttempt 0 "later" {later})))'
        for first, later in pairs) + ')\n')
    assert [row[0] for row in choices[1:7]] == ['AiDerived:Proved'] * 4 + [
        'AiDerived:Unfinished', 'AiDerived:Fault'], choices
    assert [row[1] for row in choices[1:5]] == ['later', 'later', 'later', 'first'], choices
    assert choices[-1] == 'AiDerived:NoProof', choices
    if not args.corpus:
        return 13
    observed = execute(binary, prelude() + f'''
!(let* (($ds (ai-math:load-library {quote(args.corpus)}))
        ($itp (ai-math:itp $ds {quote(ROOT)} {quote(args.lean)}))
        ($context (AiProver None None $itp None ()))
        ($hints (AiProver:Hints (()) ("or") ("or") "fixture" ()))
        ($options ((stages (base)) (candidate-limit 1) (use-duper false) (budget (AiITP:Budget 30000 200000 8000)))))
   (Cases
     (ai-math:decompose-plan $context "orIL" (AiProofPlan "intro P Q hp" ((AiClaim "h" "P"))) $hints $options)
     (ai-math:decompose-plan $context "orIL" (AiProofPlan "intro P Q hp" ((AiClaim "bad" "_root_.False"))) $hints $options)))
''')
    assert observed[1][0] == 'AiDecomp:Result' and observed[1][-1][0] == 'AiITP:Accepted', observed[1]
    assert 'have «h» : P := by' in observed[1][-2], observed[1]
    assert observed[2][-1][0] == 'AiPlan:NotProved', observed[2]
    observed = execute(binary, prelude() + f'''
(= (research-fixture-forged $context $goal $claim $hints $options $failed)
   (AiDerived:Proved "forged" "exact orIL _ _ hp" (AiITP:CaseAccepted "orIL" 0 1 () ())))
!(let* (($ds (ai-math:load-library {quote(args.corpus)}))
        ($itp (ai-math:itp $ds {quote(ROOT)} {quote(args.lean)}))
        ($context (AiProver None None $itp None ())) ($hints (AiProver:Hints (()) () () "fixture" ()))
        ($goal (AiDerivedGoal $itp "orIL" "intro P Q hp r f g" 0)) ($cache (new-space))
        ($options ((stages ()) (use-duper false) (budget (AiITP:Budget 30000 200000 8000))))
        ($bad (ai-math:put $cache $goal "exact orIL _ _ hp"))
        ($cached (ai-math:plan-prove-claim $context $goal (AiClaim "h" "r") $hints
           (ai-math:research-option $options cache $cache)))
        ($good (ai-math:put $cache $goal "exact f hp")))
   (Cases $cached
     (ai-math:plan-prove-claim $context $goal (AiClaim "h" "r") $hints
       (ai-math:research-option $options cache $cache))
     (ai-math:plan-external-claim $context $goal (AiClaim "h" "r") $hints
       (ai-math:research-option $options claim-handler (AiPlan:Handler &self research-fixture-forged))
       AiDerived:NoProof)))
''')
    assert observed[1][0] == observed[3][0] == 'AiDerived:NotProved', observed
    assert observed[2][0] == 'AiDerived:Proved' and observed[2][2] == 'exact f hp', observed
    return 19


def source_controls():
    counts = {'if': 4, 'case': 3, 'let': 4, 'let*': 3, 'map-atom': 4, 'foldl-atom': 6}
    def walk(value):
        if not isinstance(value, list) or not value:
            return
        if isinstance(value[0], str) and value[0] in counts:
            assert len(value) == counts[value[0]], value
            if value[0] == 'case':
                assert all(isinstance(branch, list) and len(branch) == 2 for branch in value[2]), value
            if value[0] == 'let*':
                assert all(isinstance(binding, list) and len(binding) == 2 for binding in value[1]), value
        for child in value:
            walk(child)
    files = ['itp', 'experiment', 'prop_synth', 'research_strategies', 'proof_state', 'incremental',
             'alternative_atp', 'proof_plans', 'decomposition', 'oracle_chains', 'hybrid_induction', 'embedding_python', 'research_analysis', 'research']
    for file in files:
        text = (ROOT / 'phase1' / (file + '.metta')).read_text()
        text = re.sub(r'"(?:\\.|[^"\\])*"|;[^\n]*',
                      lambda m: '' if m[0].startswith(';') else m[0], text)
        forms = read_atoms(text)
        assert forms and all(isinstance(form, list) and form[0] == '=' and len(form) == 3 for form in forms), file
        walk(forms)
    main = (ROOT / 'phase1/research_main.metta').read_text()
    walk(read_atoms(re.sub(r'"(?:\\.|[^"\\])*"|;[^\n]*',
                          lambda m: '' if m[0].startswith(';') else m[0], main)))
    return len(files) + 1


def decomposition_controls(binary, args):
    if not args.corpus:
        return 0
    directory = ROOT / '.cetta/research'
    directory.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix='plans-', dir=directory))
    calls = []
    plan = {'intro': 'intro P Q hp', 'claims': [{'name': 'h', 'type': 'P'}]}
    nested = {'intro': '', 'claims': [{'name': 'small', 'type': 'P'}]}
    answers = ['A short proof through the assumed P.', json.dumps(plan), '```lean\nexact orIL\n```',
               'Prove P via the local hypothesis.', json.dumps(nested), '```lean\nexact hp\n```',
               '```lean\nexact small\n```', '```lean\nintro r f g\nexact f h\n```']
    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *_args):
            pass
        def do_POST(self):
            row = json.loads(self.rfile.read(int(self.headers['Content-Length'])))
            count = sum(item['model'] == row['model'] for item in calls)
            calls.append(row)
            if row['model'] == 'nested':
                answer = answers[count] if count < len(answers) else 'unexpected extra call'
            else:
                answer = ['An invalid claim.', json.dumps({'intro': 'intro P Q hp',
                    'claims': [{'name': 'bad', 'type': '_root_.False'}]}), '```lean\nexact orIL\n```'][min(count, 2)]
            content = json.dumps({'choices': [{'message': {'content': answer}}]}).encode()
            self.send_response(200)
            self.send_header('Content-Type', 'application/json')
            self.send_header('Content-Length', str(len(content)))
            self.end_headers()
            self.wfile.write(content)
    server = ThreadingHTTPServer(('127.0.0.1', 0), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        def client(model, cap):
            return (f'(ai-math:llm-client {quote(ROOT)} (ai-math:http-session) '
                    f'{quote("http://127.0.0.1:" + str(server.server_port) + "/v1")} '
                    f'{quote(model)} "fixture-only" {quote(output / (model + ".jsonl"))} {cap} ((goal-state false)))')
        observed = execute(binary, prelude() + f'''
!(let* (($ds (ai-math:load-library {quote(args.corpus)}))
        ($itp (ai-math:itp $ds {quote(ROOT)} {quote(args.lean)}))
        ($context (AiProver None None $itp None ()))
        ($hints (AiProver:Hints (()) ("or") ("or") "fixture" ())) ($cache (new-space))
        ($options ((stages ()) (candidate-limit 1) (repair-rounds 0) (lemma-rounds 1) (depth 1) (use-duper false)
          (budget (AiITP:Budget 30000 200000 8000)) (cache $cache)
          (claim-handler (AiPlan:Handler &self ai-math:plan-extended-claim))))
        ($client {client('nested', 8)})
        ($result (ai-math:decompose-rounds $context $client "orIL" $hints $options))
        ($repeat (ai-math:decompose-plan $context "orIL"
          (AiProofPlan "intro P Q hp" ((AiClaim "h" "P"))) $hints
          (ai-math:research-option $options client $client))))
   (Cases $result $repeat
      (ai-math:decompose-rounds $context {client('unsafe', 3)} "orIL" $hints
        ((stages ()) (repair-rounds 0) (lemma-rounds 1) (depth 0) (use-duper false)
         (budget (AiITP:Budget 30000 200000 8000))))))
''')
        assert observed[1][-1][0] == observed[2][-1][0] == 'AiITP:Accepted', observed[:3]
        assert 'small' in observed[1][-2] and 'have «h»' in observed[1][-2], observed[1]
        assert observed[3][-1][0] != 'AiITP:Accepted', observed[3]
        assert len([item for item in calls if item['model'] == 'nested']) == 8, calls
        assert len([item for item in calls if item['model'] == 'unsafe']) == 3, calls
        assert all('127.0.0.1' not in item['messages'][-1]['content'] for item in calls)
        return 6
    finally:
        server.shutdown()
        server.server_close()
        thread.join()


def oracle_controls(binary, args):
    sys.path.insert(0, str(oracle_directory(UPSTREAM_V9)))
    original = oracle('oracle_haves')
    nodes = [
        ['PPFAP', ['PLAM', ['PRIM', '0'], ['HYP', '0']], ['KNOWN', 'ha']],
        ['TLAM', ['PROP'], ['PLAM', ['DB', '0'], ['PPFAP',
         ['PLAM', ['DB', '0'], ['HYP', '0']], ['HYP', '0']]]],
        ['PAIR', ['PPFAP', ['PLAM', ['PRIM', '1'], ['HYP', '0']], ['KNOWN', 'hb']],
         ['TLAM', ['SET'], ['PPFAP', ['PLAM', ['DB', '0'], ['HYP', '0']], ['KNOWN', 'hc']]]],
        ['KNOWN', 'ha']]
    observed = execute(binary, prelude() + '!(Cases ' + ' '.join(
        f'(ai-math:oracle-haves {term(node)} ())' for node in nodes) + ')\n')
    for node, actual in zip(nodes, observed[1:], strict=True):
        expected = []
        original.collect_haves(node, [], expected)
        assert actual == expected, (node, actual, expected)
    if not args.corpus:
        return len(nodes)
    observed = execute(binary, prelude() + f'''
!(let* (($ds (ai-math:load-library {quote(args.corpus)}))
        ($context (ai-math:prover-with $ds {quote(args.corpus)} {quote(ROOT)} {quote(args.lean)} "unused"
          ((slices ()) (use-duper false) (induction false)))) ($synth (ai-math:prop-synth $ds 10))
        ((Decl $i THM $n $h $s $b $ss $deps $fs)
          (car-atom (filter-atom $ds $d (== (ai-math:declaration-name $d) "orIL"))))
        ((Decl $j THM $m $ah $as $ab $ass $ad $af)
          (car-atom (filter-atom $ds $d (== (ai-math:declaration-name $d) "andI"))))
        ($example (Decl $i THM $n $h $s (PPFAP (PLAM $as $b) (KNOWN $ah)) $ss $deps $fs)))
   (ai-math:chain-prove $context $synth $example (AiProver:Hints (()) () () "fixture" ())
     ((stages (base)) (slices ()) (candidate-limit 1) (use-duper false) (budget (AiITP:Budget 30000 200000 8000)))))
''')
    assert observed[0] == 'AiOracle:Chain' and len(observed[1][2]) == 1, observed
    assert observed[-1][-1][0] == 'AiITP:Accepted', observed
    return len(nodes) + 2


def hybrid_controls(binary, args):
    if not args.corpus:
        return 0
    observed = execute(binary, prelude() + f'''
!(let* (($ds (ai-math:load-library {quote(args.corpus)}))
        ($context (ai-math:prover-with $ds {quote(args.corpus)} {quote(ROOT)} {quote(args.lean)} "unused"
          ((slices ()) (use-duper false) (induction false))))
        ($itp (index-atom $context 3))
        ((Decl $i $k $n $hash $s $b $ss $dep $f)
          (car-atom (filter-atom $ds $d (== (ai-math:declaration-name $d) "nat_p"))))
        ($statement (ALL (SET) (IMP (AP (TMH $hash) (DB 0)) (AP (TMH $hash) (DB 0)))))
        ($goal (AiDerivedGoal $itp "nat_inv"
           "refine (have witness : ∀ n : set, nat_p n → nat_p n := ?_; ?_)" 0))
        ($hints (AiProver:Hints (("nat_0" "nat_ordsucc")) ("nat_p") ("nat_p") "fixture" ())))
   (ai-math:hybrid-goal $context (ai-math:prop-synth $ds 10) (ai-math:research-source-aliases $context)
     $goal $statement 0 $hints ((slices ()) (smt-slices ()) (splits 1) (stages (base)) (candidate-limit 3)
       (use-duper false) (budget (AiITP:Budget 30000 200000 8000)))))
''')
    assert observed[0] == 'AiHybrid:Proved' and observed[2][0] == 'AiITP:CaseAccepted', observed
    assert 'nat_ind' in observed[1] and 'have «hc0»' in observed[1], observed
    return 2


def embedding_controls(binary, args):
    sys.path.insert(0, str(oracle_directory(UPSTREAM_V9)))
    original = oracle('embed_search')
    texts = {'eq_intro': 'theorem eq_intro : ∀ x144 : α, x144 = x144',
             'large': 'axiom large : ' + 'λ' * 1505,
             'def': 'noncomputable def def : Prop := x123'}
    observed = execute(binary, prelude() + '!(Cases ' + ' '.join(
        f'(ai-math:embedding-python-text {quote(name)} {quote(text)})' for name, text in texts.items()) + ')\n')
    for name, actual in zip(texts, observed[1:], strict=True):
        assert actual == original._text(name, SimpleNamespace(text=texts)), (name, actual)
    rankings = [['a', 'b', 'a'], ['c', 'b']]
    ranks = '(' + ' '.join('(' + ' '.join(map(quote, row)) + ')' for row in rankings) + ')'
    profile = '(EmbeddingProfile "fixture" "fixture" "OpenAIEmbeddingsV1" 2 "python-lean-v1" "http://fixture.invalid/v1")'
    rows = '''((AiPythonEmbeddingRow 0 THM "a" "A") (AiPythonEmbeddingRow 1 AXIOM "b" "B")
      (AiPythonEmbeddingRow 2 DEF "d" "D") (AiPythonEmbeddingRow 5 THM "goal" "G")
      (AiPythonEmbeddingRow 8 THM "future" "F"))'''
    observed = execute(binary, prelude() + f'''
!(let* (($profile {profile}) ($rows {rows})
    ($a (ai-math:embedding-python-from-matrix $profile $rows
      (tensor:from-values f64 (5 2) (1.0 0.0 1.0 0.0 0.0 1.0 1.0 0.0 1.0 0.0))))
    ($zero (ai-math:embedding-python-from-matrix $profile $rows
      (tensor:from-values f64 (5 2) (1.0 0.0 1.0 0.0 0.0 1.0 0.0 0.0 1.0 0.0)))))
   (Cases (ai-math:embedding-python-rank $a 5 2) (ai-math:embedding-python-rank $zero 5 2)
     (ai-math:embedding-python-rank $a 0 5) (ai-math:embedding-python-rank $a 5 2 (DEF))
     (ai-math:reciprocal-rank-fuse {ranks} 60 99)))
''')
    assert observed == ['Cases', ['b', 'a'], ['b', 'a'], [], ['d'], original.fuse(*rankings, limit=99)], observed
    decoded = {'model': 'fixture', 'data': [{'index': 1, 'embedding': [0.0, 0.0]},
                                          {'index': 0, 'embedding': [3.0, 4.0]}]}
    malformed = [dict(decoded, model='other'), dict(decoded, data=[decoded['data'][0]] * 2),
                 dict(decoded, data=decoded['data'] + [{'index': 2, 'embedding': [1, 2]}]),
                 dict(decoded, data=[{'index': 0, 'embedding': [1]}, decoded['data'][0]])]
    observed = execute(binary, prelude() + f'''!(Cases
      (let (AiOpenAIEmbeddingBatch $profile $key $texts $vectors)
        (ai-math:embedding-openai-decode {profile} ("A" "B") {quote(json.dumps(decoded))})
        (map-atom $vectors $vector (tensor:inspect $vector)))
      {' '.join(f'(ai-math:embedding-openai-decode {profile} ("A" "B") {quote(json.dumps(row))})' for row in malformed)})\n''')
    assert observed[1] == [['TensorData', 'f64', ['2'], [['0', '3.0'], ['1', '4.0']]],
                           ['TensorData', 'f64', ['2'], [['0', '0.0'], ['1', '0.0']]]], observed
    assert all(row[0] == 'AiEmbeddingFault' for row in observed[2:]), observed
    # Provider and cache exercise uses three packed rows, one HTTP request.
    base = ROOT / '.cetta/research'
    base.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix='embedding-', dir=base))
    requests = []
    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *_args):
            pass
        def do_POST(self):
            body = json.loads(self.rfile.read(int(self.headers['Content-Length'])))
            requests.append((self.path, body))
            vectors = [[3.0, 4.0], [0.0, 0.0], [3.0, 4.0]]
            data = json.dumps(dict(model='fixture', data=[{'index': i, 'embedding': vectors[i]}
                for i in reversed(range(3))], usage={'prompt_tokens': 5, 'total_tokens': 5})).encode()
            self.send_response(200)
            self.send_header('Content-Type', 'application/json')
            self.send_header('Content-Length', str(len(data)))
            self.end_headers()
            self.wfile.write(data)
    server = ThreadingHTTPServer(('127.0.0.1', 0), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        url = 'http://127.0.0.1:' + str(server.server_port) + '/v1'
        observed = execute(binary, prelude() + f'''
!(let* (($profile (EmbeddingProfile "fixture" "fixture" "OpenAIEmbeddingsV1" 2 "python-lean-v1" {quote(url)}))
  ($rows ((AiPythonEmbeddingRow 0 AXIOM "a" "A") (AiPythonEmbeddingRow 1 THM "b" "B")
    (AiPythonEmbeddingRow 2 THM "goal" "G"))) ($cache (embedding:cache-new))
  ($client (ai-math:llm-client {quote(ROOT)} (ai-math:http-session) {quote(url)} "fixture" "local-fixture"
    {quote(output / 'calls.jsonl')} 1 ()))
  ($first (ai-math:embedding-python-prepare $client $profile $rows $cache 64))
  ($second (ai-math:embedding-python-prepare $client $profile $rows $cache 64))
  ($saved (ai-math:embedding-cache-save $cache $profile ("A" "B" "G") {quote(output / 'cache.json')}))
  ($restored (ai-math:embedding-cache-load $profile {quote(output / 'cache.json')}))
  ($third (ai-math:embedding-python-prepare $client $profile $rows $restored 64)))
   (Cases (ai-math:embedding-python-rank $first 2 5) (ai-math:embedding-python-rank $second 2 5)
     (ai-math:embedding-python-rank $third 2 5)
     (ai-math:llm-usage-summary $client)))
''')
        assert observed == ['Cases', ['a', 'b'], ['a', 'b'], ['a', 'b'], ['AiLLM:Usage', '1', '5', '0']], observed
        assert len(requests) == 1 and requests[0] == ('/v1/embeddings', {'model': 'fixture', 'input': ['A', 'B', 'G']}), requests
    finally:
        server.shutdown()
        server.server_close()
        thread.join()
    return 3 + 5 + 5 + 3


def analysis_controls(binary, args):
    sys.path.insert(0, str(oracle_directory(UPSTREAM_V9)))
    original = oracle('witness_audit')
    stmt = ['AP', ['PRIM', '0'], ['DB', '0']]
    proofs = [['KNOWN', 'h'], ['PTMAP', ['KNOWN', 'h'], ['DB', '0']],
              ['PAIR', ['PTMAP', ['KNOWN', 'h'], stmt],
               ['PTMAP', ['KNOWN', 'h'], ['AP', ['PRIM', '0'], ['DB', '1']]]]]
    rows = ' '.join(f'(Decl 1 THM "g" "hash" {term(stmt)} {term(pf)} () () ())' for pf in proofs)
    actual = execute(binary, prelude() + f'!(map-atom ({rows}) $d (ai-math:witness-classify $d))\n')
    for proof, result in zip(proofs, actual, strict=True):
        counts, largest, size = original.classify(SimpleNamespace(stmt=stmt, body=proof))
        assert result == ['AiWitness:Analysis', [[k, str(v)] for k, v in sorted(counts.items())],
                          str(largest), str(size)], result
    profile = subprocess.check_output(['git', 'show', UPSTREAM_V9 + ':phase1/experiments/proof_profile.py'], cwd=ROOT, text=True)
    first_order = next(ast.literal_eval(node.value) for node in ast.parse(profile).body
                       if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'FIRST_ORDER' for t in node.targets))
    rules = execute(binary, prelude() + '!(ai-math:proof-first-order-rules)\n')
    assert set(rules) == first_order
    observed = execute(binary, prelude() + '''!(Cases
      (ai-math:proof-profile (AiATP:ProofDAG
        ((AiATP:ProofStep a FOF axiom p file () x)
         (AiATP:ProofStep b FOF plain p resolution (a) x)
         (AiATP:ProofStep c FOF plain p hol_choice (b) x)
         (AiATP:ProofStep d FOF plain p resolution (c) x))))
      (ai-math:recall-report ((("a" "b") ("a" "b")) (("a" "b") ("b"))) (1 2)))
''')
    assert observed[1] == ['AiProofProfile', '4', [['file', '1'], ['hol_choice', '1'], ['resolution', '2']], ['hol_choice']], observed
    assert observed[2][0:2] == ['RecallSummary', '2'], observed
    assert [float(r[2][1]) for r in observed[2][2]] == [0.25, 1.0], observed
    checks = 7
    if args.corpus and args.vampire:
        observed = execute(binary, prelude() + f'''
!(let* (($ds (ai-math:load-library {quote(args.corpus)}))
        ($context (ai-math:prover-with $ds {quote(args.corpus)} {quote(ROOT)} {quote(args.lean)} {quote(args.vampire)}
          ((slices ()) (use-duper false) (induction false))))
        ($declaration (car-atom (filter-atom $ds $d (== (ai-math:declaration-name $d) "orIL"))))
        ($report (ai-math:oracle-premise-advice $context $declaration ((seconds 2)))))
   (Cases $report (ai-math:proof-profile-report (index-atom $report 4))))
''')
        assert observed[1][:2] == ['AiOracle:Premises', 'orIL'], observed
        assert observed[1][3][:2] == ['AiATP:Advice', 'Theorem'], observed
        assert observed[2][0] == 'AiResearch:RuleProfile', observed
        summary = observed[2][2]
        if summary[0] == 'AiResearch:LexicalRuleProfile':
            assert summary[2][0] == 'AiATP:ProofRequest', summary
            summary = summary[1]
        steps = oracle('vampire_proof', 'phase1').parse_proof(observed[1][4][5][3])
        from collections import Counter
        assert summary[0] == 'AiProofProfile' and int(summary[1]) == len(steps) > 0, summary
        assert {key: int(n) for key, n in summary[2]} == Counter(step.rule for step in steps), summary
        checks += 4
    return checks


def runner_controls(binary, args):
    if not args.corpus:
        return 0
    directory = ROOT / '.cetta/research'
    directory.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix='runner-', dir=directory))
    entry = ROOT / 'phase1/research_main.metta'
    def run(config, code=0):
        path = output / 'config.json'
        path.write_text(json.dumps(config) + '\n')
        ran = subprocess.run([str(binary), '--no-results', '--lang', 'petta',
                              str(entry), str(path)], cwd=ROOT, text=True, capture_output=True)
        assert ran.returncode == code, (ran.returncode, ran.stdout[:3000], ran.stderr[:2000])
        assert 'AiResearch:Fault no-single-result' not in ran.stdout, ran.stdout
        return ran.stdout
    config = dict(mode='prop', corpus=str(args.corpus), output=str(output / 'prop.jsonl'),
                  vampire=str(args.vampire or 'unused'),
                  lean=str(args.lean), goals=['orIL'], options={'use_duper': False, 'max_depth': 10,
                  'budget': [30000, 200000, 8000]})
    for fields in (dict(mode='unknown'), dict(options={'max_depth': -1}), dict(goals=[]),
                   dict(options={'invented': 1})):
        invalid = dict(config, **fields)
        assert 'AiResearch:Request' in run(invalid, 2)
        assert not (output / 'prop.jsonl').exists(), invalid
    run(config)
    rows = [json.loads(line) for line in (output / 'prop.jsonl').read_text().splitlines() if line.strip()]
    assert len(rows) == 2 and rows[1]['outcome'] == 'proved', rows
    assert rows[1]['research_mode'] == 'prop' and rows[1]['proof_profile'] == 'core', rows[1]
    assert rows[1]['goal'] == 'orIL' and rows[1]['tactic'].startswith('exact '), rows[1]
    before = (output / 'prop.jsonl').read_bytes()
    assert 'AiRun:Reused' in run(dict(config, resume=True))
    assert (output / 'prop.jsonl').read_bytes() == before
    # Resume is a fresh witness check, not trust in the saved outcome tag.
    rows[1]['tactic'] = 'exact orIL'
    (output / 'prop.jsonl').write_text(''.join(json.dumps(row) + '\n' for row in rows))
    run(dict(config, resume=True))
    rows = [json.loads(line) for line in (output / 'prop.jsonl').read_text().splitlines() if line.strip()]
    assert len(rows) == 3 and rows[-1]['outcome'] == 'proved' and rows[-1]['tactic'] != 'exact orIL', rows
    incremental = dict(config, mode='incremental', output=str(output / 'incremental.jsonl'),
                       options={'slices': [], 'use_duper': False, 'max_depth': 0, 'max_probes': 1,
                                'budget': [30000, 200000, 8000]})
    run(incremental)
    inc_rows = [json.loads(line) for line in (output / 'incremental.jsonl').read_text().splitlines() if line.strip()]
    assert inc_rows[-1]['outcome'] == 'not-proved', inc_rows
    if args.zipper:
        run(dict(config, mode='zipper', output=str(output / 'zipper.jsonl'),
                 options={'slices': [], 'use_duper': False, 'seconds': 2, 'zipper': str(args.zipper),
                          'stages': ['base'], 'candidate_limit': 1, 'budget': [30000, 200000, 8000]}))
        zipper_rows = [json.loads(line) for line in (output / 'zipper.jsonl').read_text().splitlines() if line.strip()]
        assert zipper_rows[-1]['outcome'] in ('proved', 'not-proved'), zipper_rows
    if args.require_integrations:
        duper = dict(config, mode='duper2', output=str(output / 'duper.jsonl'),
                     options={'slices': [], 'use_duper': False, 'candidate_limit': 1, 'budget': [30000, 10, 8000]})
        run(duper, 3)
        duper_rows = [json.loads(line) for line in (output / 'duper.jsonl').read_text().splitlines() if line.strip()]
        assert duper_rows[-1]['outcome'] == 'unfinished' and duper_rows[-1]['proof_profile'] is None, duper_rows
        observed = execute(binary, prelude() + f'''
!(let* (($ds (ai-math:load-library {quote(args.corpus)}))
        ($context (ai-math:prover-with $ds {quote(args.corpus)} {quote(ROOT)} {quote(args.lean)} "unused"
           ((slices ()) (use-duper false) (induction false))))
        ($hints (AiProver:Hints (("Subq_Empty" "PowerI")) () () "fixture" ()))
        ($budget (AiITP:Budget 30000 1000000 8000))
        ($result (ai-math:research-one $context $ds "Empty_In_Power" duper2 $hints
                   ((candidate-limit 1) (budget $budget)) AiLLM:Disabled))
        ($owner (ai-math:research-open $context {quote(args.corpus)} {quote(output / 'duper-profile.jsonl')}
           duper2 () "fixture" Fresh))
        ($published (ai-math:research-publish $owner "Empty_In_Power" duper2 0 $result)))
   (Cases $published (ai-math:run-resume $owner "Empty_In_Power" $budget)))
''')
        assert observed[1][0] == 'AiRun:Recorded' and observed[2][0:3] == ['AiRun:Reused', 'Empty_In_Power', 'rechecked'], observed
        fields = dict((pair[1], pair[2]) for pair in observed[1][2][1])
        assert fields['outcome'] == 'proved' and fields['proof_profile'] == 'duper', fields
        assert fields['proved_by'] == 'd2-exact' and 'Subq_Empty' in fields['tactic'], fields
    if args.vampire:
        # Exercise advice through the public runner, not just prover-hints.
        advice = dict(config, mode='incremental', output=str(output / 'advice.jsonl'),
                      goals=['Empty_In_Power'], options={'slices': [16, 32], 'seconds': 1,
                      'definition_depth': 3, 'use_duper': False, 'max_depth': 0, 'max_probes': 1,
                      'budget': [30000, 200000, 8000]})
        run(advice)
        advice_rows = [json.loads(line) for line in (output / 'advice.jsonl').read_text().splitlines() if line.strip()]
        result = advice_rows[-1]
        assert result['vampire'].startswith('Theorem@'), result
        assert all(result['premise_sets']) and set(result['goal_defs']) <= set(result['defs']), result
        assert result['defs'], result  # Preserve definitions used by solver advice too.
        evidence = read_atoms(result['evidence'])[0]
        assert [int(row[1]) for row in evidence[3][-1]] == [16, 32], evidence[3]
        assert 'search-only' not in result['vampire'], result
    vectors = output / 'vectors.json'
    vectors.write_text(json.dumps(dict(names=['andI', 'orIL'], vectors=[[1.0, 0.0], [1.0, 0.0]])))
    embedding = dict(config, mode='embedding', output=str(output / 'embedding'), dimension=2,
                     vectors_file=str(vectors), options={'use_duper': False, 'limit': 5})
    run(embedding)
    path, = (output / 'embedding').glob('*.json')
    record = json.loads(path.read_text())
    assert record['value'] == ['andI'] and record['proof_authority'] == 'none', record
    assert record['mode'] == 'embedding' and record['goal'] == 'orIL', record
    assert 'reused' in run(dict(embedding, resume=True))
    vectors.write_text(json.dumps(dict(names=['andI', 'orIL'], vectors=[[0.0, 1.0], [1.0, 0.0]])))
    assert 'incompatible-observation' in run(dict(embedding, resume=True), 2)
    return 16 + bool(args.zipper) + 5 * args.require_integrations + 4 * bool(args.vampire)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta', type=Path, required=True)
    parser.add_argument('--corpus', type=Path)
    parser.add_argument('--lean', type=Path)
    parser.add_argument('--zipper', type=Path)
    parser.add_argument('--vampire', type=Path)
    parser.add_argument('--component', default='all',
                        choices=('all', 'source', 'prop', 'strategies', 'state', 'incremental', 'alternative', 'plans', 'decomposition', 'oracle', 'hybrid', 'embedding', 'analysis', 'runner'))
    parser.add_argument('--require-integrations', action='store_true',
                        help='Fail rather than omit the bounded native solver/checker controls')
    args = parser.parse_args()
    assert bool(args.corpus) == bool(args.lean), 'supply corpus and Lean together'
    if args.require_integrations:
        assert args.corpus and args.lean and args.zipper and args.vampire, 'qualification needs corpus, Lean, Vampire and Zipperposition'
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    controls = dict(source=source_controls, prop=lambda: prop_controls(binary, args), strategies=lambda: strategy_controls(binary),
                    state=lambda: state_controls(binary, args), incremental=lambda: incremental_controls(binary, args),
                    alternative=lambda: alternative_atp_controls(binary, args), plans=lambda: plan_controls(binary, args),
                    decomposition=lambda: decomposition_controls(binary, args),
                    oracle=lambda: oracle_controls(binary, args), hybrid=lambda: hybrid_controls(binary, args),
                    embedding=lambda: embedding_controls(binary, args), analysis=lambda: analysis_controls(binary, args),
                    runner=lambda: runner_controls(binary, args))
    checks = sum(run() for name, run in controls.items() if args.component in ('all', name))
    print('AiMathematicianResearch', checks, 0)


if __name__ == '__main__':
    main()
