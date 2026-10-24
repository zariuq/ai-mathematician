; Optional cosine retrieval over type-derived premise descriptions. Import
; library.metta, search.metta, and the shared embedding library first.
; Cached rows contain neither proof bodies nor proof-dependency labels.
; The recipe uses declaration names and statement-derived symbols/features;
; it is an explicit retrieval ablation, not a claim of an optimal text model.

(= (ai-math:embedding-text $declaration)
   (str:join "\n"
     ((ai-math:declaration-name $declaration)
      (str:concat "Symbols: " (str:join " " (sort-atom (ai-math:declaration-symbols $declaration))))
      (str:concat "Features: " (str:join " " (sort-atom (ai-math:declaration-features $declaration)))))))
(= (ai-math:embedding-rows $declarations)
   (map-atom (filter-atom $declarations $declaration
     (ai-math:contains (AXIOM THM) (ai-math:declaration-kind $declaration))) $declaration
     (AiEmbeddingRow (ai-math:declaration-index $declaration)
       (ai-math:declaration-name $declaration) (ai-math:embedding-text $declaration))))
(= (ai-math:embedding-row-texts $rows)
   (map-atom $rows $row (index-atom $row 3)))
(= (ai-math:embedding-build $declarations $profile $vectors)
   (ai-math:embedding-build-rows (ai-math:embedding-rows $declarations) $profile $vectors))
(= (ai-math:embedding-build-rows $rows $profile $vectors)
   (let $texts (ai-math:embedding-row-texts $rows)
     (case (embedding:from-tensor $profile "document" $texts $vectors)
       (((Embedding:Batch $same-profile $kind $key $packed)
          (case (embedding:retrieval-index (Embedding:Batch $same-profile $kind $key $packed))
            (((Embedding:RetrievalIndex $identity $content $owner)
               (AiEmbeddingSearch $profile
                 (Embedding:RetrievalIndex $identity $content $owner) $rows))
             ($failure $failure))))
        ($failure $failure)))))
(= (ai-math:embedding-rank (AiEmbeddingSearch $profile $index $rows) $goal-index $query $k)
   (case (filter-atom $rows $row (== (index-atom $row 1) $goal-index))
     ((($goal)
        (let* (($query-batch (embedding:from-tensor $profile "query" ((index-atom $goal 3)) $query))
               ($mask-items (map-atom $rows $row (< (index-atom $row 1) $goal-index)))
               ($mask (tensor:from-values bool ((size-atom $rows)) $mask-items))
               ($ranked (embedding:retrieve-cosine $index $query-batch $mask $k))
               ($identities (map-atom $rows $row (index-atom $row 2))))
          (case $ranked
            (((Embedding:Retrieved $identity $key $row-count $indices $scores)
               (AiEmbeddingRanked
                 (map-atom (embedding:matches $ranked $identities) $hit
                   (let* (((Embedding:Match $row-index $name $score) $hit)
                          ((AiEmbeddingRow $source $same-name $text) (index-atom $rows $row-index)))
                     (AiEmbeddingHit $source $name $score)))))
             ($failure $failure)))))
      (() (AiEmbeddingFault unknown-goal))
      ($ambiguous (AiEmbeddingFault ambiguous-source-position)))))

; Weighted reciprocal-rank fusion combines ordering evidence without
; comparing the unrelated numeric scales of the symbolic and embedding
; scorers.  Both candidate depths and the embedding weight remain explicit
; at the call site.  First occurrence order supplies the final tie break:
; symbolic order first, followed by embedding-only names.
(= (ai-math:reciprocal-rank-contributions $names $weight)
   (map-atom (collapse (ai-math:positions 0 (size-atom $names))) $index
     ((index-atom $names $index) (/ $weight (+ $index 1.0)))))
(= (ai-math:embedding-fuse-ranks $symbolic (AiEmbeddingRanked $hits)
      $embedding-weight $limit)
   (if (or (< $embedding-weight 0.0) (< $limit 0))
     (AiEmbeddingFault invalid-fusion-policy)
     (let* (($symbolic-names (ai-math:entry-names $symbolic))
            ($embedding-names
              (map-atom $hits $hit (index-atom $hit 2)))
            ($scores (list:group-sums-number-blocks
              ((ai-math:reciprocal-rank-contributions $symbolic-names 1.0)
               (ai-math:reciprocal-rank-contributions
                 $embedding-names $embedding-weight)))))
       (AiEmbeddingHybridRanked
         (list:take $limit (ai-math:sort-scores $scores))))))
(= (ai-math:embedding-fuse-ranks $symbolic
      (AiEmbeddingFault $reason) $embedding-weight $limit)
   (AiEmbeddingFault $reason))
(= (ai-math:embedding-hybrid-rank $search $embedding-search
      $goal-index $query $candidate-limit $embedding-weight $limit)
   (let* (($symbolic (ai-math:rank $search $goal-index $candidate-limit))
          ($embedding (ai-math:embedding-rank
            $embedding-search $goal-index $query $candidate-limit)))
     (case $symbolic
       (((Error $reason $where) (Error $reason $where))
        ($ranked (ai-math:embedding-fuse-ranks
          $ranked $embedding $embedding-weight $limit))))))
(= (ai-math:embedding-close (AiEmbeddingSearch $profile $index $rows))
   (embedding:index-close $index))
