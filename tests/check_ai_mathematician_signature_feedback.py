#!/usr/bin/env python3
"""Source-ordered type-only feedback for v9 application errors; no model calls."""
import argparse
from pathlib import Path
import shutil

from check_ai_mathematician_llm import execute,prelude
from check_ai_mathematician_library import ROOT,quote


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta',type=Path,required=True)
    parser.add_argument('--corpus',type=Path)
    parser.add_argument('--lean',type=Path)
    args=parser.parse_args()
    binary=Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    output=ROOT/'.cetta/signature-feedback'
    output.mkdir(parents=True,exist_ok=True)
    samples=[('',[]),('Application type mismatch\nin the application\n  @Megalodon.andI P Q',['andI']),
             ('in the application\n andI\nin the application\n Megalodon.andI\nin the application\n orIL',['andI','orIL']),
             ('unknown identifier foo',[]),('in the application\n  @name.with.parts',['parts'])]
    source=prelude()+'!(Cases '+' '.join(f'(ai-math:llm-misused-lemmas {quote(why)})' for why,_ in samples)+')\n'
    actual=execute(binary,source,output)
    assert actual==['Cases']+[wanted for _,wanted in samples],actual
    checks=len(samples)
    why='Application type mismatch\nin the application\n @Megalodon.lamI'
    source=prelude()+f'''!(let* (($catalog (new-space))
       ($t (ai-math:put $catalog "andI" (AiITP:Declaration 35 THM)))
       ($late (ai-math:put $catalog "lamI" (AiITP:Declaration 441 THM)))
       ($context (AiITP $catalog "unused" "unused" core)))
      (ai-math:llm-signature-feedback $context "andI" {quote(why)} (AiITP:Budget 1 1 1) 2500))\n'''
    assert execute(binary,source,output)==why
    checks+=1
    source=prelude()+'''!(let* (($catalog (new-space))
       ($a (ai-math:put $catalog "andI" (AiITP:Declaration 35 THM)))
       ($b (ai-math:put $catalog "andE" (AiITP:Declaration 36 THM)))
       ($target (ai-math:put $catalog "orIL" (AiITP:Declaration 50 THM)))
       ($late (ai-math:put $catalog "andIL" (AiITP:Declaration 90 THM)))
       ($context (AiITP $catalog "unused" "unused" core)))
      (Cases (ai-math:llm-near-names $context "orIL" "andIL")
       (ai-math:llm-unknown-names "Unknown identifier `Megalodon.andIL`\\nunknown constant `orIntro`\\nUnknown identifier `Megalodon.andIL`")
       (ai-math:llm-select-examples None $context "orIL"
         ((AiLLM:Example "andI" "first") (AiLLM:Example "orIL" "target")
          (AiLLM:Example "andIL" "future") (AiLLM:Example "unknown" "missing")) 3)
       (ai-math:llm-example-pool (JsonObject ((JsonPair "andI" "a") (JsonPair "andI" "b"))))
       (ai-math:llm-example-pool (JsonArray ()))
       (ai-math:llm-options-valid ((examples ((AiLLM:Example "andI" 4)))))))\n'''
    actual=execute(binary,source,output)
    assert actual==['Cases',['andI','andE'],['andIL','orIntro'],[['AiLLM:Example','andI','first']],
                   ['AiLLM:Fault','invalid-example-pool'],['AiLLM:Fault','invalid-example-pool'],'false'],actual
    checks+=6
    if args.corpus:
        if not args.lean:
            parser.error('--corpus requires --lean')
        why='Application type mismatch\nin the application\n @Megalodon.andI P Q'
        source=prelude()+f'''!(let* (($decls (ai-math:load-library {quote(args.corpus.resolve())}))
          ($context (ai-math:itp $decls {quote(ROOT)} {quote(args.lean.resolve())})))
         (ai-math:llm-signature-feedback $context "orIL" {quote(why)}
           (AiITP:Budget 30000 1000000 8000) 2500))\n'''
        observed=execute(binary,source,output)
        assert observed.startswith(why+'\n\nThe arguments must follow') and '«andI» :' in observed,observed
        assert ':= ' not in observed,observed
        checks+=2
        source=source.replace('ai-math:llm-signature-feedback','ai-math:llm-feedback').replace(
            quote(why),quote('Unknown identifier `Megalodon.andIL`'))
        observed=execute(binary,source,output)
        assert 'Closest real earlier names (types only)' in observed and '«andI» :' in observed,observed
        assert ':= ' not in observed and '«lamI»' not in observed,observed
        checks+=2
    print(f'AiMathematicianSignatureFeedback {checks} 0')


if __name__=='__main__':
    main()
