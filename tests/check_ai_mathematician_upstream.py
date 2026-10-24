#!/usr/bin/env python3
"""Compare new pure strategies with pinned upstream; no model requests."""
import argparse
import importlib.util
from pathlib import Path
import random
import shutil
import sys

from check_ai_mathematician_library import ROOT, quote
from check_ai_mathematician_llm import execute, prelude
from python_oracle import UPSTREAM_V9, oracle_directory
from check_ai_mathematician_search import (CanonicalSet, execute as search_execute,
    prelude as search_prelude, reference_decls, score_pairs)


def load(name, directory):
    spec = importlib.util.spec_from_file_location("upstream_" + name, directory / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def names(items):
    return "(" + " ".join(quote(item) for item in items) + ")"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta', type=Path, required=True)
    args = parser.parse_args()
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    directory = oracle_directory(UPSTREAM_V9)
    sys.path.insert(0, str(directory))
    strategy, llm = load('prover', directory), load('llm', directory)
    output = ROOT / '.cetta/upstream'
    output.mkdir(parents=True, exist_ok=True)
    rng = random.Random(20261019)
    pool = ['orIL', 'andI', 'lamI', "x'", 'λ']
    samples = [([], [], 0), (['orIL'], [], 6)]
    samples += [([rng.choice(pool) for _ in range(rng.randrange(10))],
                 [rng.choice(pool) for _ in range(rng.randrange(4))],
                 rng.randrange(9)) for _ in range(64)]
    rows = ' '.join(f'({names(p)} {names(d)} {n})' for p, d, n in samples)
    observed = execute(binary, prelude() + f'''
!(map-atom ({rows}) $row (let ($p $d $n) $row (ai-math:apply2-tactics $p $d $n)))
''', output)
    checks = 0
    for (p, d, n), actual in zip(samples, observed, strict=True):
        wanted = [['AiITP:Candidate', label, text] for label, text in strategy.apply2_tactics(p, d, n)]
        assert actual == wanted, (p, d, n, actual[:1], wanted[:1])
        checks += len(wanted) + 1
    scripts = ['', 'intros', 'intro P\n  assumption', 'intro P\n    have h := P\n    exact h\n',
               'have h := by\n  trivial\nexact h', '-- comment\n  intro P\n  assumption',
               'simp only [b_or, b_eq] at *', 'simp only [not_a_bridge] at *',
               'intro P\r\n  assumption\r\n', 'intro λ\n  \n    assumption\n',
               'intro P\n  exact P  \n\n', '\n\n', 'intro P\u2028  assumption',
               '  intro P\n  assumption', 'intro P\n\tassumption']
    source = prelude() + f'''
!(let $parser (ai-math:llm-code-parser)
  (map-atom {names(scripts)} $script
    ((ai-math:llm-normalize $parser $script)
     (ai-math:llm-repair-variants $parser $script "unsolved goals" ("orIL" "λ") "proposal"))))
'''
    observed = execute(binary, source, output)
    for script, actual in zip(scripts, observed, strict=True):
        wanted = [llm.normalize(script),
                  [['AiITP:Candidate', label, text] for label, text in
                   llm.repair_variants(script, 'unsolved goals', ['orIL', 'λ'], 'proposal')]]
        assert actual == wanted, (repr(script), actual, wanted)
        checks += 2 + len(wanted[1])
    assert not strategy.apply2_tactics([], ['or'], 6)
    import library
    from typed_export_oracle import accept_source_positions
    accept_source_positions(library)
    source = ROOT / 'tests/fixtures/ai_mathematician_library.sexpr'
    declarations = reference_decls(library, source)
    module = load('search', directory)

    class CanonicalSearch(module.Search):
        @staticmethod
        def _toks(name):
            return CanonicalSet(module.Search._toks(name))

    search = CanonicalSearch(declarations)
    queries = [(cutoff, goal, limit) for cutoff in (0, 3, len(declarations))
               for goal in (0, 4, len(declarations) - 1) for limit in (0, 7)]
    rows = ' '.join(f'({cutoff} {goal} {limit})' for cutoff, goal, limit in queries)
    observed = search_execute(binary, search_prelude() + f'''
!(let $search (ai-math:search (ai-math:load-library {quote(source)}))
 (map-atom ({rows}) $row (let ($cutoff $goal $limit) $row
   (ai-math:rank-for $search $cutoff (ai-math:search-goal $search $goal) $limit ((name-weight 0.6))))))
''')
    for (cutoff, goal, limit), actual in zip(queries, observed, strict=True):
        wanted = search.rank(cutoff, limit=limit, name_w=0.6, goal_obj=declarations[goal])
        checks += score_pairs(actual, wanted, f'goal-object/{cutoff}/{goal}/{limit}', ranked=True)
        assert all(name in {d.name for d in declarations[:cutoff]} for name, _ in actual)
        checks += 1
    context = execute(binary, prelude() + '''
!(let $rows ((0 "a" "λλ") (1 "b" "abc") (2 "c" "x"))
 ((ai-math:llm-context-rows $rows 4) (ai-math:llm-context-rows $rows 0)
  (ai-math:llm-clip "λxé" 2)))
''', output)
    assert context == [[['0', 'a', 'λλ']], [['0', 'a', 'λλ'], ['1', 'b', 'abc'], ['2', 'c', 'x']], 'λx'], context
    checks += 4
    print(f'AiMathematicianUpstream {checks + 1} 0')


if __name__ == '__main__':
    main()
