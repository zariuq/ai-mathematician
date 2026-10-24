#!/usr/bin/env python3
"""Join complete, independently checked discovery cohorts by theorem identity."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

from check_ai_mathematician_atp import read_values


def check_induction_evidence(evidence):
    pending = [evidence]
    while pending:
        node = pending.pop()
        if not isinstance(node, list) or not node:
            continue
        head = node[0]
        if head == 'AiATP:Advice':
            assert len(node) == 4 and node[1] in ('Theorem', 'Unsatisfiable', 'Satisfiable',
                                                'CounterSatisfiable', 'Timeout', 'GaveUp'), (
                'unclassified induction solver status', node[1])
        elif head == 'AiATP:UnfinishedOrFaulted':
            assert len(node) == 4 and len(node[2]) == 6 and node[2][0] == 'proc:result'
            assert node[2][2] == 'proc:timed-out', 'induction solver did not exhaust a time budget'
        elif isinstance(head, str) and head.startswith('AiATP:'):
            assert head in ('AiATP:ArchivedAdvice', 'AiATP:SMTAdvice', 'AiATP:TraceRef', 'AiATP:TraceObject'), (
                'unclassified induction solver observation', head)
        assert head != 'AiITP:Fault', 'induction check fault hidden by earlier exhaustion'
        pending.extend(child for child in node if isinstance(child, list))


def budget_exhaustions(row):
    """Observe completed bounded search, without changing controller meaning.

    Only declared per-attempt time/Lean budgets qualify. Unknown causes,
    cancellation, truncated captures and memory exhaustion remain unfinished.
    This projection never accepts a proof or changes the native journal.
    """
    values = read_values(row['evidence'])
    assert len(values) == 1
    result = values[0]
    assert len(result) == 6 and result[:2] == ['AiProver:Result', row['goal']]
    assert result[2] == str(row['index'])
    attempts, outcome = result[4:]
    assert len(outcome) == 2 and outcome[0] == 'AiProver:Unfinished'
    unfinished = []
    for attempt in attempts:
        if len(attempt) == 2 and attempt[0] == 'AiProver:InductionEvidence':
            # The controller separately projects its check outcomes into
            # Attempt/StageFault rows; this entry retains explanatory syntax.
            check_induction_evidence(attempt[1])
            continue
        assert ((len(attempt) == 6 and attempt[0] == 'AiProver:Attempt') or
                (len(attempt) == 3 and attempt[0] == 'AiProver:StageFault'))
        answer = attempt[-1]
        assert answer[0] != 'AiITP:Fault', 'fault inside unfinished record'
        if attempt[0] == 'AiProver:StageFault':
            assert answer[0] == 'AiITP:Unfinished'
        if answer[0] == 'AiITP:Unfinished':
            unfinished.append(attempt)
    assert unfinished and unfinished == outcome[1], 'unfinished coverage differs'
    reasons = []
    for attempt in unfinished:
        answer = attempt[-1]
        assert len(answer) == 4 and answer[1] == row['goal']
        reason, detail = answer[2:]
        if reason == 'retry-deadline':
            assert detail == []
        elif reason == 'deadline':
            assert len(detail) == 6 and detail[0] == 'proc:result' and detail[2] == 'proc:timed-out'
        elif reason == 'vampire-resource':
            assert len(detail) == 2 and detail[1] == 'Timeout', 'non-time solver resource limit'
        elif reason == 'vampire-process':
            assert len(detail) == 4
            observation = detail[2]
            assert len(observation) == 6 and observation[0] == 'proc:result' and observation[2] == 'proc:timed-out'
        elif reason in ('lean-errors', 'lean-exception'):
            # CettaITP.messageFailure emits unfinished only for tagged
            # maxHeartbeats/maxRecDepth errors, not arbitrary message text.
            assert len(detail) == 2 and detail[0] == 'JsonObject'
            pairs = detail[1]
            assert all(len(pair) == 3 and pair[0] == 'JsonPair' for pair in pairs)
            fields = {pair[1]: pair[2] for pair in pairs}
            assert len(fields) == len(pairs)
            assert fields['schema'] == 'ai-math.itp.v1' and fields['target'] == row['goal']
            assert fields['kind'] == 'unfinished' and fields['reason'] == reason
            if reason == 'lean-exception':
                # In the pinned Lean 4.34 runner this kind is restricted to
                # heartbeat/depth exceptions or interrupt. The latter is not
                # a completed budget. Unknown renderings stay unclassified.
                first = fields['message'].splitlines()[0]
                assert (first == 'maximum recursion depth has been reached' or
                        re.fullmatch(r'\(deterministic\) timeout(?: at `[^`\n]+`)?'
                                     r', maximum number of heartbeats \([0-9]+\) has been reached', first)), (
                            row['goal'], 'not a recognized Lean budget exception')
        else:
            raise AssertionError(f'unclassified unfinished attempt: {row["goal"]}: {reason}')
        reasons.append(dict(stage=attempt[1], reason=reason))
    return reasons


def load(directory, profile):
    manifest = (directory / 'inputs.json').read_bytes()
    inputs = json.loads(manifest)
    inputs['toolchain'] = json.loads((directory / 'toolchain.json').read_text())
    summary = json.loads((directory / 'summary.json').read_text())
    rows = json.loads((directory / 'comparison-input.json').read_text())
    assert summary['input_manifest_sha256'] == hashlib.sha256(manifest).hexdigest(), 'input receipt changed'
    assert inputs['profile'] == summary['profile'] == profile
    assert inputs['full_corpus'] and summary['full_corpus'] and summary['targets'] == 999
    assert all(summary['counts'][key] == 0 for key in ('fault', 'missing'))
    assert len(rows) == len({row['goal'] for row in rows}) == 999
    assert {row['goal'] for row in rows} == set(inputs['targets'])
    observed = Counter(row['outcome'] for row in rows)
    assert set(observed) <= {'proved', 'not-proved', 'unfinished'}, 'nonterminal or unknown outcome'
    assert all(summary['counts'][key] == observed[key] for key in ('proved', 'not-proved', 'unfinished'))
    assert summary['complete'] == (observed['unfinished'] == 0), 'completion receipt differs'
    assert len({row['index'] for row in rows}) == len(rows), 'duplicate source identity'
    for row in rows:
        if row['outcome'] == 'unfinished':
            assert profile in ('PythonV4', 'CettaFull'), 'independent check did not finish'
            row['budget_exhaustions'] = budget_exhaustions(row)
            row['controller_outcome'] = row['outcome']
            row['outcome'] = 'not-proved'
        if row['outcome'] == 'proved':
            assert row.get('independent_check') == 'kernel-statement-and-source-order', row['goal']
            assert row.get('tactic') and isinstance(row.get('used'), list) and isinstance(row.get('axioms'), list)
    return inputs, {row['goal']: row for row in rows}


def main():
    if sys.flags.optimize:
        raise RuntimeError('qualification checks require Python assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--python', type=Path, required=True)
    parser.add_argument('--metta-v4', type=Path, required=True)
    parser.add_argument('--metta-full', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    profiles = [('python', args.python), ('PythonV4', args.metta_v4), ('CettaFull', args.metta_full)]
    loaded = {profile: load(path, profile) for profile, path in profiles}
    reference, python = loaded['python']
    for profile, (inputs, _) in loaded.items():
        assert inputs['targets'] == reference['targets'], (profile, 'goal roster differs')
        for tool in ('corpus', 'lean', 'vampire'):
            assert inputs['tools'][tool] == reference['tools'][tool], (profile, tool, 'identity differs')
        assert inputs['python_revision'] == reference['python_revision']
        assert inputs['toolchain']['duper_revision'] == reference['toolchain']['duper_revision']
    comparisons, differences = [], []
    for goal in reference['targets']:
        rows = {profile: records[goal] for profile, (_, records) in loaded.items()}
        assert all(record['index'] == python[goal]['index'] for record in rows.values()), 'source identity differs'
        row = dict(goal=goal, index=python[goal]['index'],
                   outcomes={profile: record['outcome'] for profile, record in rows.items()},
                   controller_outcomes={profile: record.get('controller_outcome', record['outcome'])
                                        for profile, record in rows.items()},
                   budget_exhaustions={profile: record.get('budget_exhaustions', [])
                                       for profile, record in rows.items()},
                   tactics={profile: record.get('proved_by') for profile, record in rows.items()},
                   seconds={profile: record.get('elapsed_ns', record.get('nanoseconds', 0)) / 1e9
                            for profile, record in rows.items()})
        comparisons.append(row)
        if rows['python']['outcome'] != rows['PythonV4']['outcome']:
            differences.append(dict(row, classification='requires-evidence-review'))
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'per-goal.json').write_text(json.dumps(comparisons, indent=2) + '\n')
    (args.output / 'differences.json').write_text(json.dumps(differences, indent=2) + '\n')
    summary = dict(goals=len(comparisons),
                   proved={profile: sum(r['outcome'] == 'proved' for r in records.values())
                           for profile, (_, records) in loaded.items()},
                   v4_outcome_differences=len(differences),
                   normalized_controller_unfinished={profile: sum('budget_exhaustions' in r for r in records.values())
                                                     for profile, (_, records) in loaded.items()},
                   cetta_full='separate capability cohort',
                   all_successes_independently_checked=True)
    (args.output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
