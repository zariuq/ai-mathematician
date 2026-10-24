#!/usr/bin/env python3
"""Premise embedding adapter controls, with no model or memory requests."""
import argparse
from pathlib import Path
import shutil

from check_ai_mathematician_library import ROOT,quote,read_atoms
import subprocess


def prelude():
    return (f'!(import! &self {quote(ROOT/"phase1/library.metta")})\n'
            '!(import! &self (library list))\n!(import! &self (library embedding))\n'
            f'!(import! &self {quote(ROOT/"phase1/search.metta")})\n'
            f'!(import! &self {quote(ROOT/"phase1/embedding_search.metta")})\n')


def run(binary,source):
    result=subprocess.run([str(binary),'--lang','petta@1.0.6','-e',prelude()+source],cwd=ROOT,
                          text=True,capture_output=True,timeout=180)
    assert result.returncode==0,(result.stdout,result.stderr)
    values=read_atoms(result.stdout)
    assert values[:5]==['true']*5,(values,result.stderr)
    return values[5:]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta',type=Path,required=True)
    args=parser.parse_args()
    binary=Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    rows='((AiEmbeddingRow 0 "a" "type a") (AiEmbeddingRow 5 "b" "type b") (AiEmbeddingRow 8 "goal" "type goal") (AiEmbeddingRow 11 "future" "type future"))'
    profile='(EmbeddingProfile "fixture" "fixture" "fixture-v1" 3 "name-symbols-features-v1" "http://fixture.invalid")'
    vectors='(tensor:from-values f64 (4 3) (1.0 0.0 0.0 0.0 1.0 0.0 1.0 0.0 0.0 1.0 0.0 0.0))'
    query='(tensor:from-values f64 (1 3) (1.0 0.0 0.0))'
    observed=run(binary,f'''!(let* (($context (ai-math:embedding-build-rows {rows} {profile} {vectors}))
       ($ranked (ai-math:embedding-rank $context 8 {query} 99))
       ($none (ai-math:embedding-rank $context 0 {query} 99))
       ($unknown (ai-math:embedding-rank $context 7 {query} 2))
       ($closed (ai-math:embedding-close $context)))
       (Adapter $ranked $none $unknown (ai-math:embedding-rank $context 8 {query} 2)))\n''')
    assert observed==[['Adapter',['AiEmbeddingRanked',[
        ['AiEmbeddingHit','0','a','1.0'],['AiEmbeddingHit','5','b','0.0']]],
        ['AiEmbeddingRanked',[]],['AiEmbeddingFault','unknown-goal'],
        ['Embedding:Fault','retrieval','closed-or-forged-index']]],observed
    # A proof-only sentinel is not part of the provider recipe.
    declaration='(Decl 4 THM "lemma" "hash" (PROP) (SECRET_PROOF_BODY) ("p" "q") ("SECRET_PROOF_DEPENDENCY") ("concl:p"))'
    expected=quote('lemma\nSymbols: p q\nFeatures: concl:p')
    observed=run(binary,f'!(== (ai-math:embedding-rows ({declaration})) ((AiEmbeddingRow 4 "lemma" {expected})))\n')
    assert observed==['true'],observed
    # Both the goal and future row strictly outrank every eligible premise.
    # Filtering an unmasked top-1 afterwards would incorrectly return none.
    future_vectors='(tensor:from-values f64 (4 3) (0.0 1.0 0.0 0.0 0.0 1.0 1.0 0.0 0.0 1.0 0.0 0.0))'
    observed=run(binary,f'''!(let* (($context (ai-math:embedding-build-rows {rows} {profile} {future_vectors}))
        ((AiEmbeddingRanked $hits) (ai-math:embedding-rank $context 8 {query} 1))
        ($names (map-atom $hits $hit (index-atom $hit 2)))
        ($closed (ai-math:embedding-close $context))) $names)\n''')
    assert observed==[['a']],observed
    # Fusion consumes ranks, not incomparable raw scores.  A shared name gets
    # both reciprocal-rank contributions; embedding-only names remain eligible.
    symbolic='((a 99.0) (b -5.0) (c 1.0))'
    embedding='(AiEmbeddingRanked ((AiEmbeddingHit 2 c 0.9) (AiEmbeddingHit 1 b 0.8) (AiEmbeddingHit 0 d 0.7)))'
    observed=run(binary,f'''!(ai-math:embedding-fuse-ranks {symbolic} {embedding} 0.1 4)\n
!(ai-math:embedding-fuse-ranks {symbolic} {embedding} 0.0 2)\n
!(ai-math:embedding-fuse-ranks {symbolic} {embedding} -0.1 2)\n
!(ai-math:embedding-fuse-ranks {symbolic} (AiEmbeddingFault closed) 0.1 2)\n''')
    assert observed==[
        ['AiEmbeddingHybridRanked', [['a','1.0'],['b','0.55'],['c','0.43333333333333335'],['d','0.03333333333333333']]],
        ['AiEmbeddingHybridRanked', [['a','1.0'],['b','0.5']]],
        ['AiEmbeddingFault','invalid-fusion-policy'],
        ['AiEmbeddingFault','closed']],observed
    declarations='''(
      (Decl 0 AXIOM "a" "ha" (P a) () (a) () (fa))
      (Decl 1 THM "b" "hb" (P b) () (b) ("a") (fb))
      (Decl 2 THM "goal" "hg" (P goal) () (goal) ("a" "b") (fg)))'''
    integration_vectors='(tensor:from-values f64 (3 3) (1.0 0.0 0.0 0.0 1.0 0.0 1.0 0.0 0.0))'
    observed=run(binary,f'''!(let* (($declarations {declarations})
        ($search (ai-math:search $declarations))
        ($context (ai-math:embedding-build $declarations {profile} {integration_vectors}))
        ($symbolic (ai-math:rank $search 2 2))
        ($semantic (ai-math:embedding-rank $context 2 {query} 2))
        ($expected (ai-math:embedding-fuse-ranks $symbolic $semantic 0.1 2))
        ($actual (ai-math:embedding-hybrid-rank $search $context 2 {query} 2 0.1 2))
        ($closed (ai-math:embedding-close $context)))
      (== $actual $expected))\n''')
    assert observed==['true'],observed
    print('AiMathematicianEmbeddings 12 0')


if __name__=='__main__':
    main()
