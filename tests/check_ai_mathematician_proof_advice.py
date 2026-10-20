#!/usr/bin/env python3
"""Structural TSTP advice, broken-edge controls and a real solver observation."""
import argparse
from pathlib import Path
import random
import shutil

from check_ai_mathematician_library import ROOT, quote
from check_ai_mathematician_llm import execute, prelude


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta', type=Path, required=True)
    parser.add_argument('--corpus', type=Path)
    parser.add_argument('--vampire', type=Path)
    args = parser.parse_args()
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    output = ROOT / '.cetta/proof-advice'
    output.mkdir(parents=True, exist_ok=True)
    original = ("fof(a,axiom,p,file('private/input',c_4)).\n"
                "fof(b,plain,p,inference(copy,[status(thm)],[a])).\n"
                "fof(c,plain,p,inference(resolve,[status(thm)],[b,a,b])).\n")
    sources = [original, original.replace('[a]', '[absent]'),
               original.replace('fof(b,plain', 'fof(a,plain'),
               original.replace('[a]', '[b]'),
               "fof('a',axiom,p,file('input',c_4)). fof(b,plain,p,inference(copy,[],[a]))."]
    observed = execute(binary, prelude() + f'''
!(map-atom ({' '.join(quote(s) for s in sources)}) $text
  (ai-math:proof-dag (tptp:read-text $text)))
''', output)
    dag = observed[0]
    assert dag[0] == 'AiATP:ProofDAG', dag
    assert [s[1] for s in dag[1]] == ['a', 'b', 'c'], dag
    assert dag[1][-1][6] == ['b', 'a', 'b'], dag
    assert observed[1][:2] == ['AiATP:ProofRequest', 'missing-predecessors'], observed[1]
    assert observed[2][:2] == ['AiATP:ProofRequest', 'duplicate-step'], observed[2]
    assert observed[3][:2] == ['AiATP:ProofRequest', 'dependency-cycle'], observed[3]
    assert observed[4][0] == 'AiATP:ProofDAG', observed[4]
    checks = 7
    observed = execute(binary, prelude() + f'''
!(let $records (tptp:read-text {quote(original)})
  (ai-math:proof-dag (list:reverse $records)))
''', output)
    assert observed == ['AiATP:ProofDAG', list(reversed(dag[1]))], observed
    checks += 1
    rng = random.Random(20261019)
    texts, expected_graphs = [], []
    for size in range(1, 25):
        parents = {i: rng.choices(range(i), k=rng.randrange(4)) if i else []
                   for i in range(size)}
        order = rng.sample(range(size), size)
        records, expected_steps = [], []
        for i in order:
            refs = [f'n{p}' for p in parents[i]]
            records.append(f"fof(n{i},plain,p,inference(copy,[],[{','.join(refs)}])).")
            expected_steps.append(['AiATP:ProofStep', f'n{i}', 'fof', 'plain',
                                   'p', 'copy', refs, 'AiATP:Derived'])
        texts.append('\n'.join(records))
        expected_graphs.append(['AiATP:ProofDAG', expected_steps])
    observed = execute(binary, prelude() + f'''
!(map-atom ({' '.join(quote(s) for s in texts)}) $text
  (ai-math:proof-dag (tptp:read-text $text)))
''', output)
    assert observed == expected_graphs, observed
    checks += sum(1 + len(graph[1]) for graph in expected_graphs)
    cycle = ('fof(root,plain,p). fof(a,plain,p,inference(copy,[],[b])). '
             'fof(b,plain,p,inference(copy,[],[a])).')
    observed = execute(binary, prelude() + f'''
!(ai-math:proof-dag (tptp:read-text {quote(cycle)}))
''', output)
    assert observed[:2] == ['AiATP:ProofRequest', 'dependency-cycle'], observed
    checks += 1
    observed = execute(binary, prelude() + f'''
!(let* (($thf (AiTHF 0 (new-space) (AiTHF:Formats (tptp:open-reader strict) (tptp:open-record-printer))))
        ($dag (ai-math:proof-dag (tptp:read-text {quote(original)})))
        ($text (ai-math:proof-display $thf $dag 0))
        ($again (ai-math:proof-dag (tptp:read-text $text))))
   ($text $again (ai-math:proof-display $thf $dag 90)
     (ai-math:proof-dag ((thf x plain p (inference copy () ((: a detail))))))))
''', output)
    full, again, clipped, annotated = observed
    assert 'private/input' not in full and "file('problem',c_4)" in full, full
    assert again == dag, (again, dag)
    assert 'middle records omitted' in clipped, clipped
    assert annotated[0] == 'AiATP:ProofRequest', annotated
    checks += 4
    # Display lookup cannot disclose future names, and enumerates only symbols
    # that the proof actually mentions, not a copy of the whole catalogue.
    observed = execute(binary, prelude() + '''
!(let* (($index (new-space))
        ($earlier (add-atom $index (AiTHF:Entry Ordinal 4 4 (AiTHF:Fact 4 AXIOM "before" () NoBody))))
        ($later (add-atom $index (AiTHF:Entry Ordinal 5 5 (AiTHF:Fact 5 THM "held_out" () NoBody))))
        ($context (AiTHF 6 $index NoFormats))
        ($dag (AiATP:ProofDAG
          ((AiATP:ProofStep a thf axiom (c_4 c_5) file () (AiATP:Input c_4))))))
  ((ai-math:proof-legend $context 5 $dag)
   (ai-math:proof-display-name $context 5 c_04)
   (ai-math:proof-display-name $context 5 c_4_def)
   (ai-math:proof-display-name $context 5 ordinary)))
''', output)
    assert observed == [['c_4 = before'], [], [], []], observed
    checks += 4
    observed = execute(binary, prelude() + '''
!(let* (($index (new-space))
        ($stored (add-atom $index (AiTHF:Entry Ordinal 4 4 (AiTHF:Fact 4 AXIOM "before" () NoBody))))
        ($context (AiTHF 6 $index (AiTHF:Formats (tptp:open-reader strict) (tptp:open-record-printer))))
        ($dag (AiATP:ProofDAG
          ((AiATP:ProofStep a fof axiom (c_4 c_4) file () (AiATP:Input c_4))))))
  ((ai-math:proof-guidance $context 5 $dag 10)
   (ai-math:proof-guidance $context 5 $dag 0)))
''', output)
    assert 'before' not in observed[0] and 'identifier mappings omitted' in observed[0], observed[0]
    assert 'c_4 = before' in observed[1] and 'fof(a,axiom' in observed[1], observed[1]
    checks += 2
    observed = execute(binary, prelude() + '''
!((ai-math:proof-advice NoContext "goal" -1)
  (ai-math:proof-advice NoContext NotText 10)
  (ai-math:llm-finished "goal" ((AiLLM:ProofContextUnavailable
    (AiATP:ProofUnavailable ((AiATP:ProofSlice 16 unavailable)))))))
''', output)
    assert all(row[:2] == ['AiATP:ProofRequest', 'display-policy'] for row in observed[:2]), observed
    assert observed[2][0] == 'AiLLM:Result' and observed[2][-1][0] == 'AiProver:NotProved', observed[2]
    checks += 3
    if args.corpus and args.vampire:
        observed = execute(binary, prelude() + f'''
!(let* (($decls (ai-math:load-library {quote(args.corpus.resolve())}))
        ($search (ai-math:search $decls))
        ($thf (ai-math:thf $decls {quote(args.corpus.resolve())}))
        ($context (AiProver $search $thf NoChecker {quote(args.vampire.resolve())}
                    ((slices (16)) (vampire-seconds 2) (definition-depth 3))))
        ($advice (ai-math:proof-advice $context "andI" 12000)))
  (case $advice
    (((AiATP:ProofAdvice $name $k $text $premises $defs $evidence)
      (AdviceChecks $name $k (str:starts-with $text "Untrusted Vampire")
        (str:find $text "TPTP inference records:")
        (get-type $text) (get-metatype $evidence)))
     ($other $other))))
''', output)
        assert observed[:4] == ['AdviceChecks', 'andI', '16', 'true'], observed
        assert observed[-2:] == ['String', 'Expression'], observed
        assert observed[4] != '()', observed
        checks += 6
    print(f'AiMathematicianProofAdvice {checks} 0')


if __name__ == '__main__':
    main()
