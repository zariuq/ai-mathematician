#!/usr/bin/env python3
"""Focused controls for the exact-script MeTTa replay entry point."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

from check_ai_mathematician_library import ROOT
from check_ai_mathematician_published import checkpoint, checked_receipts, unique_object, validate_record


def receipt_controls():
    source = [dict(goal='orIL', origin='control', script='unused fixture text', prelude='', duper=False)]
    record = dict(schema='ai-math.replay.result.v1', ordinal=0, goal='orIL', origin='control',
                  duper=False, ok=True, nanoseconds=1, used=['Megalodon.or'], axioms=[],
                  result='(AiITP:Accepted "orIL" ("Megalodon.or") ())')
    validate_record(record, source)
    count = 1
    def rejected(action):
        nonlocal count
        try:
            action()
        except ValueError:
            count += 1
            return
        raise AssertionError('invalid replay receipt accepted')
    for key, value in (('ordinal', True), ('duper', 0), ('ok', 1), ('nanoseconds', -1),
                       ('goal', 'orIR'), ('used', []), ('result', '(AiITP:Accepted "orIR" ("Megalodon.or") ())')):
        bad = copy.deepcopy(record)
        bad[key] = value
        rejected(lambda bad=bad: validate_record(bad, source))
    rejected(lambda: json.loads('{"ok":true,"ok":false}', object_pairs_hook=unique_object))
    base = ROOT / '.cetta/replay-controls'
    base.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix='receipt-', dir=base))
    attempt = output / 'attempt-fixture'
    attempt.mkdir()
    journal = attempt / 'results.jsonl'
    raw = (json.dumps(record) + '\n').encode()
    journal.write_bytes(raw)
    assert checked_receipts(output, source, 'inputs') == {}
    checkpoint(attempt / 'receipt.json', len(raw), hashlib.sha256(raw).hexdigest(), 'inputs')
    assert set(checked_receipts(output, source, 'inputs')) == {0}
    journal.write_bytes(raw + b'{"unfinished":')
    assert set(checked_receipts(output, source, 'inputs')) == {0}
    count += 3
    rejected(lambda: checked_receipts(output, source, 'changed-inputs'))
    journal.write_bytes(raw.replace(b'orIL', b'orIR'))
    rejected(lambda: checked_receipts(output, source, 'inputs'))
    journal.write_bytes(raw[:5])
    rejected(lambda: checked_receipts(output, source, 'inputs'))
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--lean", required=True)
    args = parser.parse_args()
    output = ROOT / ".cetta/replay-controls"
    output.mkdir(parents=True, exist_ok=True)
    binary, corpus = args.cetta.resolve(), args.corpus.resolve()
    lean = str(Path(subprocess.check_output([args.lean, "--print-prefix"], cwd=ROOT, text=True).strip()) / "bin/lean")
    env = dict(os.environ, CETTA_ITP_RUNTIME="native")
    count = receipt_controls()

    def row(goal="orIL", script="intro P Q hp r f g\nexact f hp", **extra):
        return dict(goal=goal, origin="replay control", script=script, prelude="", duper=False) | extra

    def run(name, values, *, shard=0, shards=1, ok=True, raw=None):
        nonlocal count
        bundle = output / (name + ".jsonl")
        bundle.write_text(raw if raw is not None else "".join(json.dumps(r) + "\n" for r in values))
        result = subprocess.run([str(binary), "--no-results", "--lang", "petta",
                                 str(ROOT / "phase1/replay_main.metta"), str(corpus), str(bundle),
                                 lean, str(shard), str(shards)], cwd=ROOT, env=env,
                                capture_output=True, text=True, timeout=60)
        (output / (name + ".stdout")).write_text(result.stdout)
        (output / (name + ".stderr")).write_text(result.stderr)
        records = [json.loads(line) for line in result.stdout.splitlines()]
        assert records and records[-1]["schema"] == "ai-math.replay.summary.v1", (name, result)
        assert (result.returncode == 0) is ok and records[-1]["ok"] is ok, (name, result, records)
        count += 1
        return records

    positive = [row(), row("andI", "intro P Q hp hq r f\nexact f hp hq")]
    result = run("valid", positive)
    assert [r["goal"] for r in result[1:-1]] == [r["goal"] for r in positive], result
    assert result[-1]["checked"] == 2 and all(r["ok"] for r in result[1:-1]), result
    for shard in (0, 1):
        result = run(f"shard-{shard}", positive, shard=shard, shards=2)
        assert len(result) == 3 and result[1]["ordinal"] == shard, result
    helper = "theorem replayControl : forall P Q : Prop, P -> or P Q := by\n  intro P Q hp r f g\n  exact f hp"
    result = run("helper", [row(script="exact replayControl", prelude=helper)])
    assert result[1]["ok"], result
    result = run("duper", [row(script="intro P Q hp\nsimp only [b_or]\nduper [*]", duper=True)])
    assert result[1]["ok"] and result[1]["duper"] is True, result

    invalid = [
        ("empty", []),
        ("duplicate-goal", [row(), row()]),
        ("unknown-goal", [row("no-such-theorem")]),
        ("non-theorem", [row("or")]),
        ("extra-field", [row(unexpected=True)]),
        ("missing-field", [{k: v for k, v in row().items() if k != "prelude"}]),
        ("invalid-duper", [row(duper="false")]),
        ("invalid-script", [row(script=17)]),
        ("invalid-helper", [row(prelude=None)]),
        ("empty-script", [row(script="")]),
        ("late-invalid", [row(), row("andI", unexpected=True)]),
    ]
    for name, values in invalid:
        result = run(name, values, ok=False)
        assert len(result) == 1 and result[0]["checked"] == 0, result
    for name, text in (("truncated", '{"goal":'), ("duplicate-key", json.dumps(row())[:-1] + ',"duper":true}')):
        assert len(run(name, [], ok=False, raw=text)) == 1
    assert len(run("invalid-shard", positive, shard=2, shards=2, ok=False)) == 1
    result = run("rejected-proof", [row(script="exact orIL"), positive[1]], ok=False)
    assert len(result) == 3 and result[1]["ok"] is False and result[-1]["checked"] == 0, result
    assert "AiITP:Rejected" in result[1]["result"], result
    print(f"AiMathematicianReplay {count} 0")


if __name__ == "__main__":
    main()
