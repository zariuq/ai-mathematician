#!/usr/bin/env python3
"""Optional premise-recall ablation using a configured embedding service.

Only the native adapter's name/symbol/feature descriptions are sent. Proof
bodies and dependency labels stay out of the provider packet; labels are read
locally afterwards to score retrieval. No persistent collection is modified.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import statistics
import subprocess
import time
from urllib.request import Request,urlopen

from check_ai_mathematician_embeddings import prelude,run
from check_ai_mathematician_library import ROOT,quote,read_atoms
from check_ai_mathematician_search import load_reference,reference_decls
from python_oracle import oracle_directory


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cetta',type=Path,required=True)
    parser.add_argument('--corpus',type=Path,required=True)
    parser.add_argument('--url',required=True)
    parser.add_argument('--protocol',required=True)
    parser.add_argument('--dimension',type=int,required=True)
    parser.add_argument('--model',required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--sample-goals',type=int,default=32)
    parser.add_argument('--batch-size',type=int,default=8)
    parser.add_argument('--response-cache',type=Path,
                        help='Read an existing profile/content-keyed response cache.')
    parser.add_argument('--cache-only',action='store_true',
                        help='Refuse missing cached batches without contacting a provider.')
    args=parser.parse_args()
    if min(args.dimension,args.sample_goals,args.batch_size)<1:
        parser.error('positive dimension, sample count and batch size required')
    # Reference pricing is explicitly single-threaded and recorded, not a
    # silently stronger or weaker BLAS configuration.
    os.environ['OPENBLAS_NUM_THREADS']='1'
    import numpy as np

    output=args.output.resolve(); output.mkdir(parents=True,exist_ok=True)
    binary=args.cetta.resolve(); corpus=args.corpus.resolve()
    recipe='name-symbols-features-v1'
    profile=['premise-recall',args.model,args.protocol,args.dimension,recipe,args.url]
    profile_text='(EmbeddingProfile '+' '.join(str(v) if isinstance(v,int) else quote(v) for v in profile)+')'
    metadata=output/'descriptions.json'
    source=f'''!(let $rows (ai-math:embedding-rows (ai-math:load-library {quote(corpus)}))
       (fs:write {quote(metadata)}
         (json:stringify (JsonArray (map-atom $rows $row
           (let (AiEmbeddingRow $source $name $text) $row
             (JsonArray ($source $name $text))))))))\n'''
    written=run(binary,source)
    assert written[-1:] in (['true'],[[]]) and metadata.is_file(),written
    rows=json.loads(metadata.read_text())
    assert rows and all(len(row)==3 and isinstance(row[2],str) for row in rows)
    library,search_type=load_reference(oracle_directory())
    declarations=reference_decls(library,corpus)
    expected_rows=[[d.index,d.name,d.name+'\nSymbols: '+' '.join(sorted(d.stmt_syms))+
                    '\nFeatures: '+' '.join(sorted(d.feats))]
                   for d in declarations if d.kind in ('AXIOM','THM')]
    assert rows==expected_rows,'provider descriptions differ from statement-only recipe'
    eligible=[d for d in declarations if d.kind=='THM' and d.proof_deps]
    count=min(args.sample_goals,len(eligible))
    selected=[eligible[i*len(eligible)//count] for i in range(count)]
    row_by_position={row[0]:row for row in rows}
    assert len(row_by_position)==len(rows)
    query_texts=[row_by_position[goal.index][2] for goal in selected]
    cache=output/'responses'; cache.mkdir(exist_ok=True)
    existing_cache=args.response_cache.resolve() if args.response_cache else cache
    if not existing_cache.is_dir():
        parser.error('response cache must be an existing directory')
    provider_ns=0; fresh_requests=0

    def embed(texts,kind):
        nonlocal provider_ns,fresh_requests
        vectors=[]
        for start in range(0,len(texts),args.batch_size):
            batch=texts[start:start+args.batch_size]
            key=hashlib.sha256(json.dumps(profile+[kind,batch],ensure_ascii=False,separators=(',',':')).encode()).hexdigest()
            path=existing_cache/(key+'.json')
            if not path.is_file():
                path=cache/(key+'.json')
            if path.is_file():
                payload=json.loads(path.read_text())
            else:
                if args.cache_only:
                    raise RuntimeError(f'missing cached {kind} batch {key}; provider access disabled')
                request=Request(args.url,json.dumps({'texts':batch,'kind':kind},ensure_ascii=False).encode(),
                                {'Content-Type':'application/json'})
                begin=time.perf_counter_ns()
                with urlopen(request,timeout=180) as response:
                    payload=json.load(response)
                provider_ns+=time.perf_counter_ns()-begin
                fresh_requests+=1
            assert payload.get('protocol')==args.protocol and payload.get('dim')==args.dimension
            data=payload['embeddings']
            assert len(data)==len(batch) and all(len(row)==args.dimension for row in data)
            assert all(isinstance(x,(int,float)) and not isinstance(x,bool) and math.isfinite(x) for row in data for x in row)
            if 'indices' in payload:
                assert payload['indices']==list(range(len(batch))) and all(type(x) is int for x in payload['indices'])
            if not path.is_file():
                path.write_text(json.dumps(payload,separators=(',',':')))
            vectors.extend(data)
            if start%max(args.batch_size,64)==0:
                print(f'EmbeddingProvider {kind} {min(start+len(batch),len(texts))}/{len(texts)}',flush=True)
        return vectors

    documents=embed([row[2] for row in rows],'document')
    questions=embed(query_texts,'query')
    documents_file=output/'documents.json'; queries_file=output/'queries.json'
    documents_file.write_text(json.dumps({'embeddings':documents,'protocol':args.protocol,'dim':args.dimension},separators=(',',':')))
    queries_file.write_text(json.dumps({'embeddings':questions,'protocol':args.protocol,'dim':args.dimension},separators=(',',':')))
    hybrid_policy={'kind':'weighted-reciprocal-rank','candidate_depth':64,
                   'embedding_weight':0.1,
                   'tie_policy':'symbolic-order-then-embedding-order'}
    requests='('+' '.join(f'({ordinal} {goal.index})' for ordinal,goal in enumerate(selected))+')'
    source=prelude()+'!(import! &self system)\n'+f'''
!(let* (($declarations (ai-math:load-library {quote(corpus)}))
        ($metadata (ai-math:embedding-rows $declarations))
        ($doc-text (fs:read-text {quote(documents_file)}))
        ($query-text (fs:read-text {quote(queries_file)}))
        ($start (system:monotonic-ns))
        ($docs (tensor:from-json f64 ({len(rows)} {args.dimension}) $doc-text ("embeddings")))
        ($queries (tensor:from-json f64 ({count} {args.dimension}) $query-text ("embeddings")))
        ($context (ai-math:embedding-build-rows $metadata {profile_text} $docs))
        ($prepared (system:monotonic-ns))
        ($results (map-atom {requests} $request
          (let* ((($ordinal $goal) $request)
                 ($query (tensor:view $queries (1 {args.dimension}) ({args.dimension} 1) (* $ordinal {args.dimension}))))
            (Goal $goal (ai-math:embedding-rank $context $goal $query 64)))))
        ($finished (system:monotonic-ns))
        ($search-start (system:monotonic-ns))
        ($search (ai-math:search $declarations))
        ($search-prepared (system:monotonic-ns))
        ($symbolic-results (map-atom {requests} $request
          (let ($ordinal $goal) $request
            (SymbolicGoal $goal (ai-math:rank $search $goal 64)))))
        ($symbolic-finished (system:monotonic-ns))
        ($hybrid-results (map-atom {requests} $request
          (let* ((($ordinal $goal) $request)
                 ((Goal $goal $embedding-ranked) (index-atom $results $ordinal))
                 ((SymbolicGoal $goal $symbolic-ranked)
                   (index-atom $symbolic-results $ordinal)))
            (HybridGoal $goal
              (ai-math:embedding-fuse-ranks $symbolic-ranked $embedding-ranked
                {hybrid_policy['embedding_weight']} 64)))))
        ($hybrid-finished (system:monotonic-ns))
        ($closed (ai-math:embedding-close $context)))
  (EmbeddingRecallTiming
    (- $prepared $start) (- $finished $prepared)
    (- $search-prepared $search-start) (- $symbolic-finished $search-prepared)
    (- $hybrid-finished $symbolic-finished)
    $results $hybrid-results))
'''
    script=output/'retrieval.metta'; script.write_text(source)
    begin=time.perf_counter_ns()
    result=subprocess.run([str(binary),'--lang','petta@1.0.6',str(script)],cwd=ROOT,text=True,capture_output=True,timeout=300)
    whole_ns=time.perf_counter_ns()-begin
    (output/'retrieval.stdout').write_text(result.stdout); (output/'retrieval.stderr').write_text(result.stderr)
    assert result.returncode==0,(result.stdout[-1000:],result.stderr)
    observed=read_atoms(result.stdout)[-1]
    assert observed[0]=='EmbeddingRecallTiming',observed
    def normalized(row):
        scale,squares=0.0,1.0
        for value in row:
            absolute=abs(value)
            if not absolute:
                continue
            if scale<absolute:
                ratio=scale/absolute; squares=1.0+squares*ratio*ratio; scale=absolute
            else:
                ratio=absolute/scale; squares+=ratio*ratio
        assert scale>0
        root=math.sqrt(squares)
        return [(value/scale)/root for value in row]
    normalize_start=time.perf_counter_ns()
    ordered_documents=[normalized(row) for row in documents]
    ordered_questions=[normalized(row) for row in questions]
    reference_prepare_ns=time.perf_counter_ns()-normalize_start
    matrix=np.asarray(ordered_documents,dtype=np.float64); q=np.asarray(ordered_questions,dtype=np.float64)
    positions=np.asarray([row[0] for row in rows],dtype=np.int64)
    search=search_type(declarations)
    summaries={k:{'embedding':[],'baseline':[],'hybrid':[]} for k in (8,16,32,64)}
    ordered_ns=0; numpy_ns=0; numpy_differences=0
    for ordinal,(goal,actual,actual_hybrid) in enumerate(
            zip(selected,observed[6],observed[7],strict=True)):
        assert actual[:2]==['Goal',str(goal.index)] and actual[2][0]=='AiEmbeddingRanked',actual
        hits=actual[2][1]
        assert all(int(hit[1])<goal.index and row_by_position[int(hit[1])][1]==hit[2] for hit in hits),hits
        begin=time.perf_counter_ns()
        scores=matrix@q[ordinal]
        numpy_ns+=time.perf_counter_ns()-begin
        expected=sorted(np.flatnonzero(positions<goal.index),key=lambda i:(-scores[i],i))[:64]
        numpy_differences+=int([hit[2] for hit in hits]!=[rows[i][1] for i in expected])
        begin=time.perf_counter_ns()
        ordered_scores=[]
        for vector in ordered_documents:
            score=0.0
            for coefficient,component in zip(vector,ordered_questions[ordinal],strict=True):
                product=coefficient*component; score+=product
            ordered_scores.append(score)
        ordered_ns+=time.perf_counter_ns()-begin
        expected=sorted((i for i,position in enumerate(positions) if position<goal.index),
                        key=lambda i:(-ordered_scores[i],i))[:64]
        assert [hit[2] for hit in hits]==[rows[i][1] for i in expected],(goal.name,hits[:3],expected[:3])
        assert all(float(hit[3])==ordered_scores[i] for hit,i in zip(hits,expected,strict=True)),goal.name
        baseline=[name for name,_ in search.rank(goal.index,limit=64)]
        names=[hit[2] for hit in hits]
        baseline_rank={name:rank for rank,name in enumerate(baseline,1)}
        embedding_rank={name:rank for rank,name in enumerate(names,1)}
        candidates=list(dict.fromkeys(baseline+names))
        def fusion_score(name):
            symbolic=(1.0/baseline_rank[name]) if name in baseline_rank else 0.0
            semantic=(hybrid_policy['embedding_weight']/embedding_rank[name]
                      if name in embedding_rank else 0.0)
            return symbolic+semantic
        hybrid=sorted(candidates,key=lambda name:(-fusion_score(name),
                      baseline_rank.get(name,len(baseline)+1),
                      embedding_rank.get(name,len(names)+1)))
        assert actual_hybrid[:2]==['HybridGoal',str(goal.index)],actual_hybrid
        assert actual_hybrid[2][0]=='AiEmbeddingHybridRanked',actual_hybrid
        native_hybrid=actual_hybrid[2][1]
        assert [entry[0] for entry in native_hybrid]==hybrid[:64],(goal.name,native_hybrid[:8],hybrid[:8])
        assert all(float(entry[1])==fusion_score(entry[0]) for entry in native_hybrid),goal.name
        for k in summaries:
            summaries[k]['embedding'].append(len(set(names[:k])&goal.proof_deps)/len(goal.proof_deps))
            summaries[k]['baseline'].append(len(set(baseline[:k])&goal.proof_deps)/len(goal.proof_deps))
            summaries[k]['hybrid'].append(len(set(hybrid[:k])&goal.proof_deps)/len(goal.proof_deps))
    report={'profile':profile,'candidate_rows':len(rows),'goals':count,
            'corpus_sha256':hashlib.sha256(corpus.read_bytes()).hexdigest(),
            'binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest(),
            'source_recipe':'statement-derived names/symbols/features; no proof labels',
            'fresh_provider_requests':fresh_requests,'provider_ns':provider_ns,
            'cache_only':args.cache_only,
            'native_prepare_ns':int(observed[1]),'native_retrieval_ns':int(observed[2]),
            'native_symbolic_prepare_ns':int(observed[3]),'native_symbolic_rank_ns':int(observed[4]),
            'native_fusion_ns':int(observed[5]),
            'whole_native_ns':whole_ns,
            'reference_ordered_python_ns':ordered_ns,'reference_numpy_matvec_ns':numpy_ns,
            'reference_normalize_ns':reference_prepare_ns,
            'all_rankings_equal_ordered_reference':True,'numpy_ranking_difference_count':numpy_differences,
            'hybrid_policy':hybrid_policy,
            'recall':{k:{name:statistics.mean(values) for name,values in columns.items()} for k,columns in summaries.items()}}
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)
    print('A measured optional ablation; embedding retrieval remains off by default.')


if __name__=='__main__':
    main()
