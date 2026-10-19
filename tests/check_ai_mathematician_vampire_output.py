#!/usr/bin/env python3
"""Qualify the producer spelling adapter without relaxing the TPTP reader."""
import argparse
from pathlib import Path
import random
import re
import shutil
import sys

from check_ai_mathematician_atp import execute, prelude
from check_ai_mathematician_library import ROOT, quote


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path, required=True)
    args = parser.parse_args()
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    output = ROOT / ".cetta/vampire-output"
    samples = []
    protected = ["'inference(beta-eta,[],[a])'", '"inference(beta-eta,[],[a])"',
                 "% inference(beta-eta,[],[a])\n", "/* inference(beta-eta,[],[a]) */",
                 "'it\\'s inference(beta-eta,[],[a])'", "outerinference(beta-eta,[],[a])",
                 "inference(ordinary_rule,[],[a])"]
    for text in protected:
        samples.append((text, ["AiATP:ProducerText", text, []]))
    rng = random.Random(20261019)
    for i in range(128):
        prefix = rng.choice(protected) + " /* λ */ "
        rule = rng.choice(("beta-eta_normalization", "a-b-c", "valid_rule-step_2"))
        opening = rng.choice(("inference(", "inference (\n  ", "inference\t( "))
        text = prefix + opening + rule + ",[],[a])"
        start = len((prefix + opening).encode())
        end = start + len(rule)
        changed = prefix + opening + "'" + rule + "',[],[a])"
        samples.append((text, ["AiATP:ProducerText", changed,
                               [["AiATP:RuleNameQuote", str(start), str(end), rule]]]))
    negative = ["'unterminated", '"unterminated', "/* unfinished", "'escape\\"]
    actual = execute(binary, prelude() + "!(let $codec (ai-math:vampire-codec)\n" +
                     " (map-atom (" + " ".join(quote(s) for s, _ in samples) + " " +
                     " ".join(quote(s) for s in negative) +
                     ") $text (ai-math:vampire-normalize $codec $text)))\n", output)
    assert len(actual) == len(samples) + len(negative), actual[:2]
    for row, (source, expected) in zip(actual, samples):
        assert row == expected, (source, row, expected)
    assert all(row == ["AiATP:ProducerInterpretationNeeded", "incomplete-lexical-input"]
               for row in actual[len(samples):]), actual[len(samples):]
    valid = "fof(a,axiom,p,file('input',c_4)). fof(b,plain,p,inference(copy,[],[a]))."
    producer = valid.replace("inference(copy,", "inference(beta-eta_normalization,")
    malformed = producer.replace("fof(b,plain,p,", "fof(b,plain,,")
    actual = execute(binary, prelude() + f"""
!(let* (($reader (tptp:open-reader strict)) ($index (new-space))
        ($strict (tptp:read-text $reader {quote(valid)}))
        ($kept (ai-math:vampire-read-payload $index $reader {quote(valid)}))
        ($producer (ai-math:vampire-read-payload $index $reader {quote(producer)})))
   ((== $strict $kept) (list:is-list $kept)
    (tptp:read-text $reader {quote(producer)})
    $producer
    (tptp:input-references (ai-math:vampire-payload-records $producer))
    (ai-math:vampire-read-payload $index $reader {quote(malformed)})))
""", output)
    assert actual[:2] == ["true", "true"], actual[:2]
    assert actual[2][0] == "TPTP:NoParse" and actual[3][:2] == ["AiATP:ProducerPayload", "VampireRuleNames"], actual[2:4]
    assert actual[4] == [["TPTP:InputReference", "a", "input", "c_4"]], actual[4]
    assert actual[5][0] == "TPTP:NoParse", actual[5]
    checks = len(samples) + len(negative) + 6
    for name in ("vampire_thf_skolem.out", "vampire_thf_new_symbols.out"):
        fixture = ROOT / "tests/fixtures" / name
        expected = sorted(set(re.findall(r"file\(unknown,([A-Za-z0-9_]+)\)", fixture.read_text())))
        actual = execute(binary, prelude() + f"""
!(let* (($reader (tptp:open-reader strict)) ($index (new-space))
        ($envelope (tptp:szs-output (fs:read-text {quote(fixture)})))
        ((TPTP:SZSData $kind $body $start $end) (car-atom (tptp:szs-data $envelope)))
        ($payload (ai-math:vampire-read-advice-payload $index $reader $body)))
   ((ai-math:vampire-payload-advice-ready $payload)
    (list:is-list (ai-math:vampire-payload-records $payload))
    (sort-atom (unique-atom (map-atom (ai-math:vampire-payload-references $payload) $ref
      (ai-math:vampire-reference-name $ref))))))
""", output)
        assert actual[:2] == ["true", "false"], (name, actual)
        assert actual[2] == expected and expected, (name, actual[2], expected)
        checks += 3
    # Quoted text, comments and longer identifiers are not file references.
    body = ("'file(unknown,bad1)' /* file(unknown,bad2) */ "
            "% file(unknown,bad3)\n outerfile(unknown,bad4) "
            "file /* gap */ ( 'input', 'c_42' ) file(unknown,c_7)")
    actual = execute(binary, prelude() + f"""
!(let* (($index (new-space)) ($reader (tptp:open-reader strict))
        ($payload (ai-math:vampire-read-advice-payload $index $reader {quote(body)})))
   ((map-atom (ai-math:vampire-payload-references $payload) $ref
      (ai-math:vampire-reference-name $ref))
    (ai-math:vampire-read-advice-payload $index $reader {quote(body + " 'unterminated")})))
""", output)
    assert actual[0] == ["c_42", "c_7"], actual
    assert actual[1][0] in ("TPTP:NoParse", "TPTP:LexReject"), actual[1]
    checks += 2
    print(f"AiMathematicianVampireOutput {checks} 0")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ValueError, IndexError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        sys.exit(1)
