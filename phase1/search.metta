; Premise selection from yenat/ai-mathematician phase1/search.py,
; revision 5e73833790d43d066f72be1548be2ee0fcab192d. Target: PeTTa 1.0.6.
; Entry points load library.metta and the shared list library.
;
; (ai-math:search declarations) prepares reusable corpus weights and training.
; (ai-math:rank search goal-index) returns up to 32 (name score) pairs.
; rank-with accepts a limit and a tuple of named options, for example
; ((name-weight 0.5) (nb-weight 2.0)). Other defaults match the Python source.
;
; Documents and training uses are indexed facts, not overwritten counters.
; Only proofs before the goal train a query. Corpus-wide statement statistics
; are intentional. Set sums are canonical; equal scores keep introduction order.

!(import! &self (library postings))
!(import! &self (library tensor))

(= (ai-math:declaration-index (Decl $i $k $n $h $s $b $ss $ds $fs)) $i)
(= (ai-math:declaration-symbols (Decl $i $k $n $h $s $b $ss $ds $fs)) $ss)
(= (ai-math:declaration-features (Decl $i $k $n $h $s $b $ss $ds $fs)) $fs)
(= (ai-math:search-fact (Decl $i $kind $name $hash $stmt $body $syms $deps $features))
   (AiSearchFact $i $kind $name $syms $deps $features))
(= (ai-math:declaration-index (AiSearchFact $i $k $n $ss $ds $fs)) $i)
(= (ai-math:declaration-kind (AiSearchFact $i $k $n $ss $ds $fs)) $k)
(= (ai-math:declaration-name (AiSearchFact $i $k $n $ss $ds $fs)) $n)
(= (ai-math:declaration-symbols (AiSearchFact $i $k $n $ss $ds $fs)) $ss)
(= (ai-math:declaration-dependencies (AiSearchFact $i $k $n $ss $ds $fs)) $ds)
(= (ai-math:declaration-features (AiSearchFact $i $k $n $ss $ds $fs)) $fs)
(= (ai-math:search-facts (AiSearch $count $facts $weights $training))
   (map-atom (sort-atom (collapse (match $facts (AiSearchItem $ordinal $fact)
                                               ($ordinal $fact))))
     $entry (index-atom $entry 1)))
(= (ai-math:search-before (AiSearch $count $facts $weights $training) $index)
   (map-atom
     (sort-atom (filter-atom
       (collapse (match $facts (AiSearchItem $ordinal $fact) ($ordinal $fact)))
       $entry (< (index-atom $entry 0) $index)))
     $entry (index-atom $entry 1)))
(= (ai-math:ln $x) (log-math 2.718281828459045 $x))
(= (ai-math:name-tokens $name)
   (sort-atom (unique-atom
     (remove-all-atom "" (str:split "_" $name)))))

; Per-declaration batches have the same occurrence order as index-document.
; The map/concatenate/add-atoms composition can stream through the generic
; ingress consumer; its authored route remains an ordinary finite batch.
(= (ai-math:document-feature-rows $kind $keys $ordinal $tail)
   (if (== (size-atom $keys) 0) $tail
     (let* (($key (car-atom $keys)) ($rest (cdr-atom $keys)))
       (cons-atom (AiDocument $kind $key $ordinal)
         (ai-math:document-feature-rows $kind $rest $ordinal $tail)))))
(= (ai-math:document-overlap-rows $keys $ordinal $tail)
   (if (== (size-atom $keys) 0) $tail
     (let* (($key (car-atom $keys)) ($rest (cdr-atom $keys)))
       (cons-atom (AiOverlapSymbol $key $ordinal)
         (ai-math:document-overlap-rows $rest $ordinal $tail)))))
(= (ai-math:document-statement-rows $keys $ordinal $tail)
   (if (== (size-atom $keys) 0) $tail
     (let* (($key (car-atom $keys)) ($rest (cdr-atom $keys)))
       (cons-atom (AiDocument Symbol $key $ordinal)
         (cons-atom (AiStatementSymbol $key $ordinal)
           (ai-math:document-statement-rows $rest $ordinal $tail))))))
(= (ai-math:document-rows (AiDocumentInput $ordinal $decl))
   (let* (($name (ai-math:declaration-name $decl))
          ($statement (sort-atom (unique-atom (ai-math:declaration-symbols $decl))))
          ($overlap (sort-atom (unique-atom (cons-atom $name $statement))))
          ($statement-group (* 2 $ordinal))
          ($name-group (+ $statement-group 1))
          ($features (ai-math:document-feature-rows Feature
            (ai-math:declaration-features $decl) $ordinal ()))
          ($tokens (ai-math:document-feature-rows Token
            (ai-math:name-tokens $name) $ordinal $features))
          ($named (cons-atom (AiNameOrder $name $ordinal) $tokens))
          ($overlaps (ai-math:document-overlap-rows $overlap $ordinal $named))
          ($symbols (ai-math:document-statement-rows $statement $ordinal $overlaps))
          ($name-block (if (> (size-atom $overlap) (size-atom $statement))
            (cons-atom (AiSymbolPosting (cons-atom $name ()) $name-group $ordinal) $symbols)
            $symbols)))
     (cons-atom (AiSymbolPosting $statement $statement-group $ordinal) $name-block)))
(= (ai-math:ingest-documents $documents $inputs)
   (let $rows
     (foldl-atom (map-atom $inputs $input (ai-math:document-rows $input))
       () $out $batch (union-atom $out $batch))
     (add-atoms $documents $rows)))

(= (ai-math:index-document $space $ordinal $decl)
   (let* (($name (ai-math:declaration-name $decl))
          ($kind (ai-math:declaration-kind $decl))
          ($statement-symbols
            (sort-atom (unique-atom (ai-math:declaration-symbols $decl))))
          ($overlap-symbols
            (sort-atom (unique-atom
              (cons-atom $name $statement-symbols))))
          ($statement-group (* 2 $ordinal))
          ($name-group (+ $statement-group 1))
          ($statement-block (add-atom $space
            (AiSymbolPosting $statement-symbols $statement-group $ordinal)))
          ($name-block (if (ai-math:contains $statement-symbols $name) ()
            (add-atom $space
              (AiSymbolPosting ($name) $name-group $ordinal))))
          ($symbols (map-atom $statement-symbols $key
                      (let* (($document
                               (add-atom $space
                                 (AiDocument Symbol $key $ordinal)))
                              ($posting
                               (add-atom $space
                                 (AiStatementSymbol $key $ordinal))))
                        ())))
          ($overlap (map-atom $overlap-symbols $key
                      (add-atom $space (AiOverlapSymbol $key $ordinal))))
          ($name-order (add-atom $space (AiNameOrder $name $ordinal)))
          ($tokens (map-atom (ai-math:name-tokens $name) $key
                     (add-atom $space (AiDocument Token $key $ordinal)))))
     (map-atom (ai-math:declaration-features $decl) $key
       (add-atom $space (AiDocument Feature $key $ordinal)))))

(= (ai-math:search $decls)
   (case $decls
     (((Error $reason $where) $decls)
      ($items
       (let* (($size (size-atom $items))
              ($facts (map-atom $items $decl (ai-math:search-fact $decl)))
              ($catalog (new-space))
              ($stored (foldl-atom $facts 0 $ordinal $fact
                         (let $entry
                           (add-atom $catalog (AiSearchItem $ordinal $fact))
                           (+ $ordinal 1))))
              ($document-inputs (sort-atom (collapse (match $catalog
                (AiSearchItem $ordinal $fact) (AiDocumentInput $ordinal $fact)))))
              ($documents (new-space))
              ($indexed (ai-math:ingest-documents $documents $document-inputs))
              ($frequencies (ai-math:document-frequencies-attempt $documents))
              ($keys (case $frequencies
                (((List:GroupedSums $key-counts)
                   (map-atom $key-counts $entry (index-atom $entry 0)))
                 ($keys-declined
                   (unique-atom (collapse (match $documents
                     (AiDocument $kind $key $index) (AiFeature $kind $key))))))))
              ($weights $documents)
              ($prepared (case $frequencies
                (((List:GroupedSums $weight-counts)
                   (map-atom $weight-counts $entry
                     (let ($feature $occurrences) $entry
                       (ai-math:prepare-weight-count $weights $size $feature $occurrences))))
                 ($weights-declined
                   (map-atom $keys $feature
                     (ai-math:prepare-weight $weights $documents $size $feature))))))
              ($symbol-table (postings:prepare-space-blocks-attempt $weights
                (Postings:BlockLayout AiSymbolPosting 4 1 2 3 () ())))
              ($totals (case
                (ai-math:prepare-totals-attempt $weights $facts $keys $size $symbol-table)
                ((AiTotals:Prepared ())
                 ($totals-declined
                   (foldl-atom $facts 0 $ordinal $fact
                     (let $stored
                       (ai-math:prepare-fact-totals $weights $ordinal $fact)
                       (+ $ordinal 1)))))))
              ($rank-facts (filter-atom $facts $fact
                (ai-math:contains (THM AXIOM)
                  (ai-math:declaration-kind $fact))))
              ($rank-positions (map-atom $rank-facts $fact
                (ai-math:declaration-index $fact)))
              ($rank-coordinates (tensor:from-values index
                ((size-atom $rank-positions)) $rank-positions))
              ($rank-name-items (map-atom $rank-facts $fact
                (ai-math:name-order-get $weights
                  (ai-math:declaration-name $fact))))
              ($rank-prefix (postings:prepare ((RankCandidates $rank-positions))))
              ($rank-plans (new-space))
              ($saved-plan-space (add-atom $weights
                (AiEntry RankPlanSpace $rank-plans)))
              ($rank-guards
                (($catalog (_minimal-space-revision $catalog))
                 ($weights (_minimal-space-revision $weights))))
              ($rank-plan (if (== $rank-name-items $rank-positions)
                (AiRankPlan $rank-prefix $rank-coordinates $rank-guards)
                NoRankPlan))
              ($saved-rank-plan (add-atom $rank-plans
                (AiEntry RankPlan $rank-plan)))
              ($saved-symbol-plan (add-atom $rank-plans
                (AiEntry SymbolPlan (AiSymbolPlan $symbol-table $rank-guards))))
              ($training (ai-math:training $facts))
              ($bayes-rank-plan (if (== $rank-plan NoRankPlan) NoBayesRankPlan
                (ai-math:prepare-bayes-rank-plan $weights $training)))
              ($saved-bayes-rank-plan (add-atom $rank-plans
                (AiEntry BayesRankPlan $bayes-rank-plan)))
              ($symbol-rank-plan (if (== $rank-plan NoRankPlan) NoSymbolRankPlan
                (ai-math:prepare-symbol-rank-plan $facts $weights $rank-guards)))
              ($saved-symbol-rank-plan (add-atom $rank-plans
                (AiEntry SymbolRankPlan $symbol-rank-plan))))
         (AiSearch $size $catalog $weights $training))))))
(= (ai-math:document-frequencies-attempt $documents)
   (let $occurrences (collapse (match $documents
          (AiDocument $kind $key $index) ((AiFeature $kind $key) 1)))
     (__cetta_lib_list_group_sums $occurrences)))
(= (ai-math:prepare-weight $weights $documents $size (AiFeature $kind $key))
   (let $count (size-atom
          (collapse (match $documents (AiDocument $kind $key $index) $index)))
     (ai-math:prepare-weight-count $weights $size (AiFeature $kind $key) $count)))
(= (ai-math:prepare-weight-count $weights $size (AiFeature $kind $key) $count)
   (let* (($log (ai-math:ln (/ (+ $size 1.0) (+ $count 1.0))))
          ($value (if (== $kind Symbol)
                    (* (+ $log 1.0)
                       (if (ai-math:contains (ai-math:logical-vocabulary) $key) 0.2 1.0))
                    $log)))
     (add-atom $weights (AiEntry (Weight $kind $key) $value))))
(= (ai-math:weight (AiSearch $count $facts $weights $training) $kind $key $default)
   (ai-math:get $weights (Weight $kind $key) $default))
(= (ai-math:weight-in $weights $kind $key $default)
   (ai-math:get $weights (Weight $kind $key) $default))
(= (ai-math:sum-weights-in $weights $kind $items $default)
   (foldl-atom (sort-atom (unique-atom $items)) 0.0 $sum $key
     (+ $sum (ai-math:weight-in $weights $kind $key $default))))
(= (ai-math:prepare-fact-totals $weights $ordinal $fact)
   (let* (($statement-symbols
            (sort-atom (unique-atom (ai-math:declaration-symbols $fact))))
          ($overlap-symbols
            (sort-atom (unique-atom
              (cons-atom (ai-math:declaration-name $fact) $statement-symbols))))
          ($statement-total
            (ai-math:sum-weights-in $weights Symbol $statement-symbols 1.0))
          ($overlap-total
            (ai-math:sum-weights-in $weights Symbol $overlap-symbols 1.0))
          ($first (add-atom $weights
                    (AiEntry (StatementTotal $ordinal) $statement-total))))
     (add-atom $weights (AiEntry (OverlapTotal $ordinal) $overlap-total))))

; A globally sorted key traversal restricts to the same sorted sequence for
; each fact. Name-only keys keep their original default weight. No total is
; published until the numeric fold has returned every source ordinal once.
(= (ai-math:prepare-totals-attempt $weights $facts $features $size $table)
   (case $table
     (((NativeHandle "postings-table-v1" $id)
        (let* (($symbols (collapse
                  (let (AiFeature $kind $key) (superpose $features)
                    (if (== $kind Symbol) $key (superpose ())))))
               ($names (map-atom $facts $fact (ai-math:declaration-name $fact)))
               ($keys (sort-atom (unique-atom (union-atom $symbols $names))))
               ($queries (map-atom $keys $key
                 ($key ((ai-math:weight-in $weights Symbol $key 1.0) 0))))
               ($space (context-space))
               ($summary (postings:try-table-counts
                 (NativeHandle "postings-table-v1" $id) table-fold-before
                 ($space $queries $size ai-math:symbol-group
                   (AiSymbolSums 0.0 0.0 -1) ai-math:symbol-step))))
          (case $summary
            ((Postings:Fallback AiTotals:Decline)
             ((Postings:Fault $reason) AiTotals:Decline)
             ($rows
               (let* (($ordered (sort-atom $rows))
                      ($ordinals (map-atom $ordered $row (index-atom $row 0)))
                      ($expected (list:to-expression (list:range $size))))
                 (if (not (== $ordinals $expected)) AiTotals:Decline
                   (let* (($totals (collapse
                             (let ($ordinal (AiSymbolSums $overlap $statement $first))
                               (superpose $ordered)
                               (superpose
                                 ((AiEntry (StatementTotal $ordinal) $statement)
                                  (AiEntry (OverlapTotal $ordinal) $overlap))))))
                          ($published (add-atoms $weights $totals)))
                     AiTotals:Prepared))))))))
      ($unsupported AiTotals:Decline))))
(= (ai-math:sum-weights $search $kind $items $default)
   (foldl-atom (sort-atom (unique-atom $items)) 0.0 $sum $key
     (+ $sum (ai-math:weight $search $kind $key $default))))

; Group additive evidence through a space's existing key index. Ordinals
; retain floating-addition and tie order; they do not constrain result bags.
(= (ai-math:group-sums $entries)
   (list:group-sums-number $entries))
(= (ai-math:store-contributions $space $entries $ordinal)
   (foldl-atom $entries $ordinal $index $entry
     (let ($key $amount) $entry
       (let $stored (add-atom $space (AiContribution $key $index $amount))
         (+ $index 1)))))
(= (ai-math:contribution-score $space $key)
   (ai-math:sum-indexed
     (collapse (match $space (AiContribution $key $index $amount)
                             ($index $amount)))))
(= (ai-math:sum-indexed $entries)
   (foldl-atom (sort-atom $entries) 0 $sum $entry (+ $sum (index-atom $entry 1))))
; Ordered positions stream into collapse once. Growing a flat tuple in a
; left fold copies every earlier element at every step.
(= (ai-math:positions $index $end)
   (if (< $index $end) $index (superpose ())))
(= (ai-math:positions $index $end)
   (if (< (+ $index 1) $end)
     (ai-math:positions (+ $index 1) $end) (superpose ())))
(= (ai-math:sort-scores $entries)
   (let* (($count (size-atom $entries))
          ($values (map-atom $entries $entry (index-atom $entry 1)))
          ($packed (tensor:from-values f64 ($count) $values))
          ($order (tensor:inspect (tensor:top-k $packed $count))))
     (case $order
       (((TensorData index ($count) $indices)
          (map-atom $indices $entry
            (index-atom $entries (index-atom $entry 1))))
        ($other (ai-math:sort-scores-keyed $entries))))))
(= (ai-math:sort-scores-keyed $entries)
   (let $rows
     (map-atom (collapse (ai-math:positions 0 (size-atom $entries))) $index
       (let $entry (index-atom $entries $index)
         ((AiSortKey (- 0.0 (index-atom $entry 1)) $index) $entry)))
     (unkey-atom (sort-atom $rows))))
(= (ai-math:name-order-get $order $name)
   (let $ordinals
     (sort-atom
       (collapse (match $order (AiNameOrder $name $ordinal) $ordinal)))
     (if (== $ordinals ()) NoName (car-atom $ordinals))))
(= (ai-math:sort-scores-with-order $order $cutoff $scores)
   (let $decorated
     (map-atom $scores $entry
       (let $ordinal (ai-math:name-order-get $order (car-atom $entry))
         (if (== $ordinal NoName) NoName
           (if (< $ordinal $cutoff)
             (let ($name $score) $entry
               ((AiSortKey (- 0.0 $score) $ordinal) $entry))
             NoName))))
     (unkey-atom (sort-atom
       (filter-atom $decorated $entry (not (== $entry NoName)))))))
(= (ai-math:entry-names $entries) (map-atom $entries $entry (car-atom $entry)))
(= (ai-math:maximum-score $entries)
   (foldl-atom $entries 0.0 $maximum $entry
     (let $value (index-atom $entry 1) (if (> $value $maximum) $value $maximum))))
(= (ai-math:name-similarity $search $a $b)
   (let* (($left (ai-math:name-tokens $a))
          ($right (ai-math:name-tokens $b))
          ($total (ai-math:sum-weights $search Token (union-atom $left $right) 0.0)))
     (if (== $total 0.0) 0.0
       (/ (ai-math:sum-weights $search Token (intersection-atom $left $right) 0.0) $total))))
(= (ai-math:overlap $search $goal-symbols $fact)
   (let* (($symbols (unique-atom
                     (cons-atom (ai-math:declaration-name $fact)
                                (ai-math:declaration-symbols $fact))))
          ($total (ai-math:sum-weights $search Symbol $symbols 1.0)))
     (if (== $total 0.0) 0.0
       (/ (ai-math:sum-weights $search Symbol (intersection-atom $symbols $goal-symbols) 1.0)
          $total))))
(= (ai-math:similarity $search $goal-symbols $fact)
   (let* (($symbols (ai-math:declaration-symbols $fact))
          ($shared (ai-math:sum-weights $search Symbol
                     (intersection-atom $goal-symbols $symbols) 1.0)))
     (if (== $shared 0.0) 0.0
       (/ $shared (ai-math:sum-weights $search Symbol (union-atom $goal-symbols $symbols) 1.0)))))
(= (ai-math:search-fact-at (AiSearch $count $facts $weights $training) $ordinal)
   (case (collapse (match $facts (AiSearchItem $ordinal $fact) $fact))
     ((($fact) $fact))))
(= (ai-math:overlap-shared (AiSearch $count $facts $weights $training)
      $goal-symbols $cutoff)
   (let $search (AiSearch $count $facts $weights $training)
     (list:group-sums-number-blocks
       (map-atom (sort-atom (unique-atom $goal-symbols)) $symbol
         (let $ordinals
           (filter-atom
             (collapse (match $weights (AiOverlapSymbol $symbol $ordinal) $ordinal))
             $ordinal (< $ordinal $cutoff))
           (if (== $ordinals ()) ()
             (let $weight (ai-math:weight $search Symbol $symbol 1.0)
               (map-atom $ordinals $ordinal ($ordinal $weight)))))))))
(= (ai-math:statement-shared (AiSearch $count $facts $weights $training)
      $goal-symbols $cutoff)
   (let $search (AiSearch $count $facts $weights $training)
     (list:group-sums-number-blocks
       (map-atom (sort-atom (unique-atom $goal-symbols)) $symbol
         (let $ordinals
           (filter-atom
             (collapse (match $weights (AiStatementSymbol $symbol $ordinal) $ordinal))
             $ordinal (< $ordinal $cutoff))
           (if (== $ordinals ()) ()
             (let $weight (ai-math:weight $search Symbol $symbol 1.0)
               (map-atom $ordinals $ordinal ($ordinal $weight)))))))))

; Even source groups describe statement symbols; the adjacent odd group is
; the declaration name only when it is not a statement symbol. Projection
; joins those roles without visiting statement evidence twice. The callback
; retains each signal's own addition order and the first statement query.
(= (ai-math:symbol-group $group $payload) (/ (- $group (% $group 2)) 2))
(= (ai-math:symbol-add $sum $weight $count)
   (if (== $count 0) $sum
     (ai-math:symbol-add (+ $sum $weight) $weight (- $count 1))))
(= (ai-math:symbol-step (AiSymbolSums $overlap $statement $first)
      $group $count ($weight $query))
   (let $next (ai-math:symbol-add $overlap $weight $count)
     (if (== (% $group 2) 0)
       (AiSymbolSums $next (ai-math:symbol-add $statement $weight $count)
         (if (< $first 0) $query $first))
       (AiSymbolSums $next $statement $first))))
(= (ai-math:symbol-shared-attempt
      (AiSearch $count $facts $weights $training) $goal-symbols $cutoff)
   (let* (($plans (ai-math:get $weights RankPlanSpace NoRankPlanSpace))
          ($symbols (sort-atom (unique-atom $goal-symbols))))
     (if (or (== $plans NoRankPlanSpace)
             (not (== (filter-atom $symbols $symbol
                        (not (== (get-type $symbol) String))) ()))) AiSymbols:Decline
       (case (ai-math:get $plans SymbolPlan NoSymbolPlan)
         (((AiSymbolPlan (NativeHandle "postings-table-v1" $id) $guards)
            (if (not (postings:sources-current $guards)) AiSymbols:Decline
              (let* (($queries
                       (map-atom (collapse (ai-math:positions 0 (size-atom $symbols))) $query
                         (let $symbol (index-atom $symbols $query)
                           ($symbol ((ai-math:weight-in $weights Symbol $symbol 1.0) $query)))))
                     ($space (context-space))
                     ($summary (postings:try-table-counts
                       (NativeHandle "postings-table-v1" $id) table-fold-before
                       ($space $queries $cutoff ai-math:symbol-group
                         (AiSymbolSums 0.0 0.0 -1) ai-math:symbol-step))))
                (case $summary
                  ((Postings:Fallback AiSymbols:Decline)
                   ((Postings:Fault $reason) AiSymbols:Decline)
                   ($rows (AiSymbols $rows)))))))
          ($other AiSymbols:Decline))))))
(= (ai-math:symbol-overlap (AiSymbols $rows))
   (map-atom $rows $row
     (let ($ordinal (AiSymbolSums $overlap $statement $first)) $row
       ($ordinal $overlap))))
(= (ai-math:symbol-statement (AiSymbols $rows))
   (unkey-atom (sort-atom
     (map-atom (filter-atom $rows $row
                 (let ($ordinal (AiSymbolSums $overlap $statement $first)) $row
                   (>= $first 0))) $row
       (let ($ordinal (AiSymbolSums $overlap $statement $first)) $row
         ((AiSymbolOrder $first $ordinal) ($ordinal $statement)))))))
(= (ai-math:symbol-shared $search $goal-symbols $cutoff)
   (case (ai-math:symbol-shared-attempt $search $goal-symbols $cutoff)
     (((AiSymbols $rows)
        ((ai-math:symbol-overlap (AiSymbols $rows))
         (ai-math:symbol-statement (AiSymbols $rows))))
      ($other
        ((ai-math:overlap-shared $search $goal-symbols $cutoff)
         (ai-math:statement-shared $search $goal-symbols $cutoff))))))
(= (ai-math:overlap-rows (AiSearch $count $facts $weights $training)
      $goal-symbols $cutoff)
   (ai-math:overlap-rows-from-shared (AiSearch $count $facts $weights $training)
     (ai-math:overlap-shared (AiSearch $count $facts $weights $training) $goal-symbols $cutoff)))
(= (ai-math:overlap-rows-from-shared (AiSearch $count $facts $weights $training) $shared-rows)
   (let $search (AiSearch $count $facts $weights $training)
     (map-atom $shared-rows $entry
       (let ($ordinal $shared) $entry
         (let* (($fact (ai-math:search-fact-at $search $ordinal))
                ($total (ai-math:get $weights (OverlapTotal $ordinal) 0.0)))
           (AiOverlapScore $ordinal $fact
             (if (== $total 0.0) 0.0 (/ $shared $total))))))))
(= (ai-math:overlap-rows-from-symbols
      (AiSearch $count $facts $weights $training) (AiSymbols $rows))
   (let $search (AiSearch $count $facts $weights $training)
     (map-atom $rows $entry
       (let ($ordinal (AiSymbolSums $shared $statement $first)) $entry
         (let* (($fact (ai-math:search-fact-at $search $ordinal))
                ($total (ai-math:get $weights (OverlapTotal $ordinal) 0.0)))
           (AiOverlapScore $ordinal $fact
             (if (== $total 0.0) 0.0 (/ $shared $total))))))))
(= (ai-math:overlap-contributions $search $goal-symbols $cutoff)
   (let $blocks (ai-math:overlap-contribution-blocks $search $goal-symbols $cutoff)
     (collapse (let $block (superpose $blocks) (superpose $block)))))
; Keep each row's ordered definition/overlap contributions together. Consumers
; that fold blocks need not repeatedly copy a growing flat result.
(= (ai-math:overlap-contribution-blocks $search $goal-symbols $cutoff)
   (map-atom (ai-math:overlap-rows $search $goal-symbols $cutoff) $row
     (let (AiOverlapScore $ordinal $fact $score) $row
       (let* (($name (ai-math:declaration-name $fact))
              ($shared (if (> $score 0.0) (($name $score)) ()))
              ($definition
                (if (and (== (ai-math:declaration-kind $fact) DEF)
                         (ai-math:contains $goal-symbols $name))
                  (($name 2.0)) ())))
         (union-atom $definition $shared)))))
(= (ai-math:overlap-coordinate-blocks $search $goal-symbols $cutoff)
   (ai-math:overlap-coordinates-from-rows $search $goal-symbols
     (ai-math:overlap-rows $search $goal-symbols $cutoff)))
(= (ai-math:overlap-coordinates-from-rows $search $goal-symbols $rows)
   (map-atom $rows $row
     (let (AiOverlapScore $ordinal $fact $score) $row
       (let* (($name (ai-math:declaration-name $fact))
              ((AiSearch $count $facts $weights $training) $search)
              ($coordinate (ai-math:name-order-get $weights $name))
              ($shared (if (> $score 0.0) (($coordinate $score)) ()))
              ($definition
                (if (and (== (ai-math:declaration-kind $fact) DEF)
                         (ai-math:contains $goal-symbols $name))
                  (($coordinate 2.0)) ())))
         (union-atom $definition $shared)))))
(= (ai-math:neighbors-prefix (AiSearch $count $facts $weights $training)
      $goal-symbols $cutoff)
   (ai-math:neighbors-from-shared (AiSearch $count $facts $weights $training)
     $goal-symbols
     (ai-math:statement-shared (AiSearch $count $facts $weights $training) $goal-symbols $cutoff)))
(= (ai-math:neighbors-from-shared (AiSearch $count $facts $weights $training)
      $goal-symbols $shared-rows)
   (let* (($search (AiSearch $count $facts $weights $training))
          ($goal-total (ai-math:sum-weights $search Symbol $goal-symbols 1.0)))
     (ai-math:sort-scores
       (filter-atom
         (map-atom $shared-rows $entry
           (let ($ordinal $shared) $entry
             (let* (($fact (ai-math:search-fact-at $search $ordinal))
                    ($fact-total
                      (ai-math:get $weights (StatementTotal $ordinal) 0.0))
                    ($union (- (+ $goal-total $fact-total) $shared)))
               ($fact
                 (if (and (== (ai-math:declaration-kind $fact) THM)
                          (> $union 0.0))
                   (/ $shared $union) 0.0)))))
         $entry (> (index-atom $entry 1) 0.0)))))
; Score order and the statement signal's introduction order form one key.
; This consumes the shared state directly instead of first rebuilding and
; sorting a separate statement-pair collection.
(= (ai-math:neighbors-from-symbols
      (AiSearch $count $facts $weights $training) $goal-symbols (AiSymbols $rows))
   (let* (($search (AiSearch $count $facts $weights $training))
          ($goal-total (ai-math:sum-weights $search Symbol $goal-symbols 1.0))
          ($keyed (collapse
            (let ($ordinal (AiSymbolSums $overlap $shared $first)) (superpose $rows)
              (if (< $first 0) (superpose ())
                (let* (($fact (ai-math:search-fact-at $search $ordinal))
                       ($fact-total (ai-math:get $weights (StatementTotal $ordinal) 0.0))
                       ($union (- (+ $goal-total $fact-total) $shared)))
                  (if (and (== (ai-math:declaration-kind $fact) THM) (> $union 0.0))
                    (let $score (/ $shared $union)
                      (if (> $score 0.0)
                        ((AiNeighborKey (- 0.0 $score) $first $ordinal) ($fact $score))
                        (superpose ())))
                    (superpose ()))))))))
     (unkey-atom (sort-atom $keyed))))
(= (ai-math:neighbors $search $goal-symbols $earlier)
   (ai-math:sort-scores
     (filter-atom
       (map-atom (filter-atom $earlier $decl (== (ai-math:declaration-kind $decl) THM))
         $decl ($decl (ai-math:similarity $search $goal-symbols $decl)))
       $entry (> (index-atom $entry 1) 0.0))))
(= (ai-math:knn $search $goal-symbols $earlier $count)
   (ai-math:knn-from-neighbors
     (ai-math:neighbors $search $goal-symbols $earlier) $count))
(= (ai-math:knn-prefix $search $goal-symbols $cutoff $count)
   (ai-math:knn-from-neighbors
     (ai-math:neighbors-prefix $search $goal-symbols $cutoff) $count))
(= (ai-math:knn-from-neighbors $neighbors $count)
   (list:group-sums-number-blocks
     (map-atom (list:take $count $neighbors) $entry
       (let ($decl $similarity) $entry
         (cons-atom ((ai-math:declaration-name $decl) $similarity)
           (map-atom (sort-atom (ai-math:declaration-dependencies $decl)) $name
             ($name $similarity)))))))

; Preparation records evidence once. A premise owns a local ledger, so a
; query does not scan other premises' feature rows. Keys remain strings.
; Source ordinals delimit training; event ordinals retain addition/tie order.
; Self/citation events stay distinct, allowing any query's self-weight without
; rebuilding or regrouping floating additions.
(= (ai-math:training $facts)
   (let* (($events (ai-math:training-events $facts))
          ($names (map-atom $events $event (index-atom $event 2))))
     ; The attempt certifies closed matching-compatible keys. A type query
     ; per occurrence would neither establish that law nor preserve its cost.
       (case (__cetta_lib_list_factorize $names)
         (((List:Factorization $keys $codes $firsts)
            (let* (($training (new-space))
                   ($positions (list:to-expression (list:range (size-atom $names))))
                   ($stored (ai-math:ingest-training $training $events $positions
                              $codes $firsts (size-atom $keys))))
              (AiTraining $training (_minimal-space-revision $training)
                (ai-math:prepare-training-prefixes $training))))
          ($unsupported (ai-math:training-reference $facts))))))

; Self evidence precedes sorted citation occurrences. Sorting does not remove
; repeated citations. Source ordinals and event ordinals remain separate.
(= (ai-math:training-citation-events $names $source $features $tail)
   (if (== (size-atom $names) 0) $tail
     (cons-atom (AiTrainingEvent $source (car-atom $names) Citation $features)
       (ai-math:training-citation-events (cdr-atom $names) $source $features $tail))))
(= (ai-math:training-source-events $facts $source)
     (let* (($fact (index-atom $facts $source))
            ($kind (ai-math:declaration-kind $fact))
            ($features (ai-math:declaration-features $fact))
            ($self (if (== $kind THM) true (== $kind AXIOM)))
            ($citations (if (== $kind THM)
              (sort-atom (ai-math:declaration-dependencies $fact)) ()))
            ($after-self (ai-math:training-citation-events
              $citations $source $features ())))
       (if $self
         (cons-atom (AiTrainingEvent $source
                      (ai-math:declaration-name $fact) Self $features) $after-self)
         $after-self)))
(= (ai-math:training-events $facts)
   (let* (($sources (list:to-expression (list:range (size-atom $facts))))
          ($blocks (map-atom $sources $source (ai-math:training-source-events $facts $source))))
     (foldl-atom $blocks () $out $block (union-atom $out $block))))
(= (ai-math:training-event-rows $events $codes $firsts $key-count $position)
   (let* (($event (index-atom $events $position))
          ($source (index-atom $event 1)) ($ordinal $position)
          ($name (index-atom $event 2)) ($kind (index-atom $event 3))
          ($features (index-atom $event 4))
          ($premise (index-atom $codes $position))
          ($first (index-atom $firsts $premise))
          ($posting (cons-atom
            (AiTrainingPostingBlock $features $name $premise $ordinal $source $kind) ())))
     (if (== $position $first)
       (let $introduced
         (cons-atom (AiTrainingCandidate $name $source $ordinal $premise)
           (cons-atom (AiTrainingPremise $name $premise) $posting))
         ; Earlier counters were removed by singular insertion. Only the
         ; counter inserted at the final first introduction remains.
         (if (== $premise (- $key-count 1))
           (cons-atom (AiTrainingNext $key-count) $introduced) $introduced))
       $posting)))
(= (ai-math:ingest-training $training $events $positions $codes $firsts $key-count)
   (if (== $key-count 0) (add-atom $training (AiTrainingNext 0))
     (let $rows
       (foldl-atom (map-atom $positions $position
         (ai-math:training-event-rows $events $codes $firsts $key-count $position))
         () $out $batch (union-atom $out $batch))
       (add-atoms $training $rows))))

(= (ai-math:training-reference $facts)
   (let* (($training (new-space))
          ($counter (add-atom $training (AiTrainingNext 0)))
          ($indexed (foldl-atom $facts (AiTrainingPosition 0 0) $position $fact
                      (let (AiTrainingPosition $source $ordinal) $position
                        (AiTrainingPosition (+ $source 1)
                          (ai-math:train-declaration $training $source $ordinal $fact))))))
     (AiTraining $training (_minimal-space-revision $training)
       (ai-math:prepare-training-prefixes $training))))

; Immutable sorted columns prepare the unit-evidence observation once.
; Uses and explicit feature overlays form one occurrence relation tagged by
; premise identity. A source-revision change makes the query use the ordinary
; occurrence-count route.
; Feature columns are populated on demand; a one-goal run need not prepare
; the features of every other theorem. Memoization never mutates the source.
(= (ai-math:prepare-training-prefixes $training)
   (let* (($prefixes (new-space))
          ($source-revision (_minimal-space-revision $training))
          ($saved-source
            (add-atom $prefixes
              (AiPrefixSource $training $source-revision)))
          ($candidates (sort-atom (collapse (match $training
            (AiTrainingPremise $name $premise) ($premise $name)))))
          ($names (map-atom $candidates $entry (index-atom $entry 1)))
          ($saved-names (add-atom $prefixes (AiPrefixNames $names)))
          ($feature-table
            (case
              (postings:prepare-space-blocks-attempt $training
                (Postings:BlockLayout AiTrainingPostingBlock
                  7 1 3 5 (AiTraining:Uses) (AiTrainingPosting)))
              (((NativeHandle "postings-table-v1" $id)
                 (NativeHandle "postings-table-v1" $id))
               ($unsupported
                 (postings:prepare-blocks
                   (ai-math:training-posting-blocks $training))))))
          ($feature-size (match $training (AiTrainingNext $next) $next))
          ($saved-features
            (add-atom $prefixes
              (AiPrefixFeatureTable $feature-table $feature-size))))
     $prefixes))
(= (ai-math:training-posting-blocks $training)
   (union-atom
     (collapse (match $training
       (AiTrainingPostingBlock $features $name $premise $event $source $kind)
       ((cons-atom AiTraining:Uses $features) $premise $source)))
     (collapse (match $training
       (AiTrainingPosting $feature $name $premise $event $source $kind)
       (($feature) $premise $source)))))
(= (ai-math:training-feature-events $training $feature)
   (union-atom
     (collapse (match $training
       (AiTrainingPostingBlock $features $name $premise $event $source $kind)
       (if (ai-math:contains $features $feature)
         ($name $premise $event $source $kind) (superpose ()))))
     (collapse (match $training
       (AiTrainingPosting $feature $name $premise $event $source $kind)
       ($name $premise $event $source $kind)))))
(= (ai-math:prepare-feature-prefixes $training $feature)
   (let* (($events (ai-math:training-feature-events $training $feature))
          ($names (unique-atom
            (map-atom $events $event (index-atom $event 0)))))
     (map-atom $names $name
       ($name (map-atom
         (filter-atom $events $event (== (index-atom $event 0) $name))
         $event (index-atom $event 3))))))
(= (ai-math:prefix-count $positions $cutoff)
   (if (== $cutoff All) (size-atom $positions)
     (list:lower-bound-number $positions $cutoff)))
(= (ai-math:training-premise $training $name $source $ordinal)
   (case (collapse (match $training (AiTrainingPremise $name $id) $id))
     ((() (let* (($id (match $training (AiTrainingNext $next) $next))
                 ($next-id (+ $id 1))
                 ($removed (remove-atom $training (AiTrainingNext $id)))
                 ($advanced (add-atom $training (AiTrainingNext $next-id)))
                 ($stored (add-atom $training
                            (AiTrainingCandidate $name $source $ordinal $id)))
                 ($identity (add-atom $training (AiTrainingPremise $name $id))))
            $id))
      (($id) $id))))
(= (ai-math:train-event $training $source $ordinal $name $kind $features)
   (let* (($premise (ai-math:training-premise $training $name $source $ordinal))
          ($indexed (add-atom $training
                      (AiTrainingPostingBlock $features $name $premise
                        $ordinal $source $kind))))
     (+ $ordinal 1)))
(= (ai-math:train-declaration $training $source $ordinal $decl)
   (let* (($kind (ai-math:declaration-kind $decl))
          ($features (ai-math:declaration-features $decl))
          ($next (if (ai-math:contains (THM AXIOM) $kind)
                   (ai-math:train-event $training $source $ordinal
                     (ai-math:declaration-name $decl) Self $features) $ordinal)))
     (if (== $kind THM)
       (foldl-atom (sort-atom (ai-math:declaration-dependencies $decl)) $next $event $name
         (ai-math:train-event $training $source $event $name Citation $features))
       $next)))
(= (ai-math:training-before $source $cutoff)
   (if (== $cutoff All) true (< $source $cutoff)))
(= (ai-math:training-sum $entries $cutoff $self-weight)
   (foldl-atom (sort-atom $entries) 0 $sum $entry
     (let ($ordinal $source $kind) $entry
       (if (ai-math:training-before $source $cutoff)
         (+ $sum (if (== $kind Self) $self-weight 1.0)) $sum))))
; Unit evidence can be counted without sorting or changing its multiplicity.
; Above binary64's exact-integer range, or at any other weight, replay the
; original events in their original floating-addition order.
(= (ai-math:training-use-entries $training $premise)
   (union-atom
     (collapse (match $training
       (AiTrainingPostingBlock $features $name $premise $event $source $kind)
       ($event $source $kind)))
     (collapse (match $training
       (AiTrainingUse $premise $event $source $kind)
       ($event $source $kind)))))
(= (ai-math:training-entries $training $premise $key)
   (case $key
     ((Uses (ai-math:training-use-entries $training $premise))
      ((Feature $feature) (collapse (match $training
        (AiTrainingFeature $premise $feature $ordinal $origin $role)
        ($ordinal $origin $role)))))))
(= (ai-math:training-evidence-count $training $premise $key $cutoff $policy)
   (case $policy
    ((AiTraining:Unit
     (let* (($sources (case $key
               ((Uses (map-atom
                  (ai-math:training-use-entries $training $premise)
                  $entry (index-atom $entry 1)))
                ((Feature $feature) (collapse (match $training
                  (AiTrainingFeature $premise $feature $ordinal $origin $role)
                  $origin))))))
            ($count (size-atom (filter-atom $sources $position (ai-math:training-before $position $cutoff)))))
       (if (<= $count 9007199254740992)
         (if (== $count 0) 0 (+ 0.0 $count))
         (ai-math:training-sum
           (ai-math:training-entries $training $premise $key)
           $cutoff 1.0))))
     ((AiTraining:Weighted $self-weight)
       (ai-math:training-sum
         (ai-math:training-entries $training $premise $key)
         $cutoff $self-weight)))))
(= (ai-math:training-feature-entries
      $training $premise $feature)
   (union-atom
     (collapse (match $training
       (AiTrainingPostingBlock $features $name $observed-premise $event $source $kind)
       (if (== $observed-premise $premise)
         (if (ai-math:contains $features $feature)
           ($event $source $kind) (superpose ()))
         (superpose ()))))
     (collapse (match $training
       (AiTrainingFeature $premise $feature $event $source $kind)
       ($event $source $kind)))))
(= (ai-math:training-feature-evidence-count
      $training $premise $feature $cutoff $policy)
   (let $entries
     (ai-math:training-feature-entries $training $premise $feature)
     (case $policy
       ((AiTraining:Unit
          (let $count (size-atom
                (filter-atom $entries $entry
                  (ai-math:training-before (index-atom $entry 1) $cutoff)))
            (if (<= $count 9007199254740992)
              (if (== $count 0) 0 (+ 0.0 $count))
              (ai-math:training-sum $entries $cutoff 1.0))))
        ((AiTraining:Weighted $self-weight)
          (ai-math:training-sum $entries $cutoff $self-weight))))))
(= (ai-math:bayes-from-training $search
      (AiTraining $training $revision $prefixes) $goal $cutoff $sigma $penalty $self-weight)
   (let* (($policy (if (== (str:number->string $self-weight) "1.0")
                     AiTraining:Unit (AiTraining:Weighted $self-weight)))
          ($features (map-atom (sort-atom (ai-math:declaration-features $goal)) $feature
                       ($feature (ai-math:weight $search Feature $feature 1.0)))))
     (if (== $policy AiTraining:Unit)
       (ai-math:bayes-unit-sparse
         $training $features $cutoff $sigma $penalty
         (if (== $revision (_minimal-space-revision $training)) $prefixes NoPrefix))
       (map-atom (ai-math:training-candidates-before $training $cutoff) $candidate
         (let* ((($ordinal $first $name $premise) $candidate)
                ($total (ai-math:training-evidence-count
                          $training $premise Uses $cutoff $policy)))
           ($name
             (foldl-atom $features (ai-math:ln $total) $score $entry
               (let ($feature $weight) $entry
                 (let $seen (ai-math:training-feature-evidence-count
                       $training $premise $feature $cutoff $policy)
                   (+ $score (* $weight (if (== $seen 0.0) $penalty
                                           (ai-math:ln (/ (* $sigma $seen) $total))))))))))))))

; The dense candidate/feature fold is the reference route for unit evidence.
; It also remains the fallback above binary64's exact-integer range.
(= (ai-math:bayes-unit $training $candidates $features $cutoff $sigma $penalty)
   (map-atom $candidates $candidate
     (let* ((($ordinal $first $name $premise) $candidate)
            ($sources (map-atom
               (ai-math:training-use-entries $training $premise)
               $entry (index-atom $entry 1)))
            ($count (size-atom (if (== $cutoff All) $sources
                                 (filter-atom $sources $position (< $position $cutoff)))))
            ($total (if (<= $count 9007199254740992) (+ 0.0 $count)
                      (ai-math:training-sum
                        (ai-math:training-entries $training $premise Uses)
                        $cutoff 1.0))))
       ($name
         (foldl-atom $features (ai-math:ln $total) $score $entry
           (let ($feature $weight) $entry
             (let $origins (map-atom
                   (ai-math:training-feature-entries
                     $training $premise $feature)
                   $feature-entry (index-atom $feature-entry 1))
               (if (== $origins ()) (+ $score (* $weight $penalty))
                 (let* (($feature-count (size-atom
                             (if (== $cutoff All) $origins
                               (filter-atom $origins $position (< $position $cutoff)))))
                    ($seen (if (<= $feature-count 9007199254740992) (+ 0.0 $feature-count)
                             (ai-math:training-sum
                               (ai-math:training-entries
                                 $training $premise (Feature $feature))
                               $cutoff 1.0))))
               (+ $score (* $weight (if (== $seen 0) $penalty
                                       (ai-math:ln (/ (* $sigma $seen) $total))))))))))))))

; Unit evidence is sparse: most candidate premises have never been observed
; with most goal features.  Start every candidate at the missing-feature
; baseline, then add corrections only for indexed nonzero postings:
;
;   log(t_p) + penalty * sum_f w_f
;     + sum_{s_pf>0} w_f * (log(sigma * s_pf / t_p) - penalty).
;
; This is the same real-valued score as the dense fold.  Contributions retain
; feature order, and every posting retains its source position, so prefix
; queries neither train on nor reveal the goal or later proofs.  Counts beyond
; binary64's exact-integer range decline to the reference route.
(= (ai-math:training-unit-total $training $premise $cutoff)
   (let $sources
     (map-atom (ai-math:training-use-entries $training $premise)
       $entry (index-atom $entry 1))
     (size-atom
       (if (== $cutoff All) $sources
         (filter-atom $sources $position (< $position $cutoff))))))
(= (ai-math:bayes-unit-summary $training $candidate $cutoff $prefixes)
   (ai-math:bayes-unit-summary-with-counts
     $training $candidate $cutoff $prefixes
     (ai-math:prefix-use-counts $training $prefixes $cutoff)))
(= (ai-math:bayes-unit-summary-with-counts
      $training $candidate $cutoff $prefixes $counts)
   (let ($ordinal $first $name $premise) $candidate
     (AiBayesUnitCandidate $ordinal $first $name $premise
       (if (== $prefixes NoPrefix)
         (ai-math:training-unit-total $training $premise $cutoff)
         (if (== $counts NoPrefix)
           (ai-math:training-unit-total $training $premise $cutoff)
           (ai-math:get $counts (PrefixCount $name) 0))))))
(= (ai-math:feature-entry-weight ($feature $weight)) $weight)
(= (ai-math:training-posting-counts $training $feature $cutoff)
   (let* (($eligible
            (filter-atom (ai-math:training-feature-events $training $feature)
              $event (ai-math:training-before (index-atom $event 3) $cutoff)))
          ($names (unique-atom
            (map-atom $eligible $event (index-atom $event 0)))))
     (map-atom $names $name
       ($name (size-atom
         (filter-atom $eligible $event
           (== (index-atom $event 0) $name)))))))
(= (ai-math:training-table-named-counts $training $rows)
   (map-atom $rows $row
     (let ($premise $count) $row
       (let $name
         (match $training (AiTrainingPremise $name $premise) $name)
         ($name $count)))))
(= (ai-math:training-posting-counts-prepared $training $prefixes $feature $cutoff)
   (if (== $prefixes NoPrefix)
     (ai-math:training-posting-counts $training $feature $cutoff)
     (case (collapse (match $prefixes
              (AiPrefixFeatureTable $table $size) ($table $size)))
       (((($table $size))
          (ai-math:training-table-named-counts $training
            (if (== $cutoff All)
              (postings:table-counts $table $feature $size)
              (postings:table-counts-before $table $feature $cutoff $size))))
        (()
          (case (collapse (match $prefixes
                   (AiPrefixPosting $feature $groups) $groups))
            ((($groups) (ai-math:prefix-group-counts $groups $cutoff))
             (()
               (let* (($groups (postings:prepare
                                  (ai-math:prepare-feature-prefixes
                                    $training $feature)))
                      ($stored (add-atom $prefixes
                                 (AiPrefixPosting $feature $groups))))
                 (ai-math:prefix-group-counts $groups $cutoff))))))))))
(= (ai-math:prefix-group-counts $groups $cutoff)
   (if (== $cutoff All) (postings:counts $groups)
     (postings:counts-before $groups $cutoff)))

; All candidate totals share one prepared observation and one query. The
; outer training revision decides whether the snapshot remains current.
(= (ai-math:prefix-use-counts $training $prefixes $cutoff)
   (if (== $prefixes NoPrefix) NoPrefix
     (case (collapse (match $prefixes
              (AiPrefixFeatureTable $table $size) ($table $size)))
       (((($table $size))
          (let* (($rows (ai-math:training-table-named-counts $training
                           (if (== $cutoff All)
                             (postings:table-counts
                               $table AiTraining:Uses $size)
                             (postings:table-counts-before
                               $table AiTraining:Uses $cutoff $size))))
                 ($counts (new-space))
                 ($stored (map-atom $rows $row
                    (let ($name $count) $row
                      (add-atom $counts
                        (AiEntry (PrefixCount $name) $count))))))
            $counts))
        (() NoPrefix)))))
(= (ai-math:bayes-feature-deltas
      $training $totals $feature $weight $cutoff $sigma $penalty $prefixes)
   (map-atom
     (ai-math:training-posting-counts-prepared $training $prefixes $feature $cutoff)
     $entry
     (let ($name $seen-count) $entry
       (let* (($seen (+ 0.0 $seen-count))
              ($total (ai-math:get $totals (BayesTotal $name) 0.0)))
         ($name (* $weight
           (- (ai-math:ln (/ (* $sigma $seen) $total)) $penalty)))))))
; Successful packed scoring never reads candidate records. Keep their
; materialization on the weighted and fallback branches where it is needed.
(= (ai-math:training-candidates-before $training $cutoff)
   (sort-atom (filter-atom
     (collapse (match $training
       (AiTrainingCandidate $name $first $ordinal $premise)
       ($ordinal $first $name $premise)))
     $entry (ai-math:training-before (index-atom $entry 1) $cutoff))))
(= (ai-math:bayes-unit-sparse
      $training $features $cutoff $sigma $penalty $prefixes)
   (case (ai-math:bayes-unit-packed
           $training $features $cutoff $sigma $penalty $prefixes)
     (((AiBayes:Packed $rows) $rows)
      (AiBayes:Stale
        (ai-math:bayes-unit $training
          (ai-math:training-candidates-before $training $cutoff)
          $features $cutoff $sigma $penalty))
      ($other (ai-math:bayes-unit-sparse-reference
                $training (ai-math:training-candidates-before $training $cutoff)
                $features $cutoff $sigma $penalty $prefixes)))))

; The ordinary sparse route remains authoritative on any declined packed
; observation. Prefix snapshots never confer proof-acceptance authority.
(= (ai-math:bayes-unit-sparse-reference
      $training $candidates $features $cutoff $sigma $penalty $prefixes)
   (let* (($counts (ai-math:prefix-use-counts $training $prefixes $cutoff))
          ($summaries (map-atom $candidates $candidate
                         (ai-math:bayes-unit-summary-with-counts
                           $training $candidate $cutoff $prefixes $counts)))
          ($unsafe (filter-atom $summaries $summary
                     (> (index-atom $summary 5) 9007199254740992))))
     (if (not (== $unsafe ()))
       (ai-math:bayes-unit $training $candidates $features $cutoff $sigma $penalty)
       (let* (($totals (if (== $counts NoPrefix) (new-space) $counts))
              ($stored-totals (map-atom $summaries $summary
                (let (AiBayesUnitCandidate $ordinal $first $name $premise $count) $summary
                  (let $total (+ 0.0 $count)
                    (add-atom $totals
                      (AiEntry (BayesTotal $name) $total))))))
              ($weight-sum (list:sum-by ai-math:feature-entry-weight $features))
              ($base
                (map-atom $summaries $summary
                  (let (AiBayesUnitCandidate $ordinal $first $name $premise $count) $summary
                    (let $total (+ 0.0 $count)
                      ($name (+ (ai-math:ln $total)
                                (* $penalty $weight-sum)))))))
              ($blocks (map-atom $features $entry
                (let ($feature $weight) $entry
                  (ai-math:bayes-feature-deltas
                    $training $totals $feature $weight $cutoff $sigma $penalty $prefixes)))))
         (list:group-sums-number-blocks (cons-atom $base $blocks))))))

; Dense introduction IDs identify premises in packed data; event ordinals
; retain evidence occurrence order. Names remain in
; the existing training relation. These caches contain immutable snapshots
; guarded by the shared source revision.
(= (ai-math:numeric-use-prefix $training $prefixes)
   (case (collapse (match $prefixes (AiNumericUse $table $size $names $guards) ($table $size $names $guards)))
     (((($table $size $names $guards)) (AiNumericUse $table $size $names $guards))
      (()
        (let* ((($table $size) (case (collapse (match $prefixes
                  (AiPrefixFeatureTable $table $size) ($table $size)))
                  (((($table $size)) ($table $size)))))
               ($names (case (collapse (match $prefixes
                  (AiPrefixNames $recorded) $recorded))
                  ((($recorded) $recorded))))
               ($guards (collapse (match $prefixes
                  (AiPrefixSource $owner $revision) ($owner $revision))))
               ($saved (add-atom $prefixes
                         (AiNumericUse $table $size $names $guards))))
          (AiNumericUse $table $size $names $guards))))))
(= (ai-math:numeric-feature-prefix $training $prefixes $feature)
   (case (collapse (match $prefixes (AiNumericFeature $feature $index) $index))
     ((($index) $index)
      (()
        (let* (($events (map-atom
                   (ai-math:training-feature-events $training $feature)
                   $event ((index-atom $event 1) (index-atom $event 3))))
               ($index (postings:prepare-events $events))
               ($saved (add-atom $prefixes (AiNumericFeature $feature $index))))
          $index)))))
(= (ai-math:numeric-prefix-counts $index $size $cutoff)
   (if (== $cutoff All) (postings:counts-tensor $index $size)
     (postings:counts-tensor-before $index $cutoff $size)))
(= (ai-math:numeric-use-counts $table $size $cutoff)
   (if (== $cutoff All)
     (postings:table-counts-tensor $table AiTraining:Uses $size)
     (postings:table-counts-tensor-before
       $table AiTraining:Uses $cutoff $size)))
(= (ai-math:numeric-feature-counts
      $training $prefixes $feature $size $cutoff)
   (case (collapse (match $prefixes
            (AiPrefixFeatureTable $table $recorded-size) ($table $recorded-size)))
     (((($table $recorded-size))
        (if (== $recorded-size $size)
          (if (== $cutoff All)
            (postings:table-counts-tensor $table $feature $size)
            (postings:table-counts-tensor-before
              $table $feature $cutoff $size))
          (Tensor:Fault feature-table-size)))
      (()
        (ai-math:numeric-prefix-counts
          (ai-math:numeric-feature-prefix $training $prefixes $feature)
          $size $cutoff)))))
(= (ai-math:bayes-packed-base $penalty $weight-sum $count)
   (+ 0 (+ (ai-math:ln (+ 0.0 $count)) (* $penalty $weight-sum))))
(= (ai-math:bayes-packed-delta $sigma $weight $penalty $seen $total)
   (* $weight (- (ai-math:ln (/ (* $sigma (+ 0.0 $seen)) (+ 0.0 $total))) $penalty)))
(= (ai-math:bayes-packed-feature
      $state $training $prefixes $totals $size $cutoff $sigma $penalty $entry)
   (case $state
     (((Tensor:Fault $reason) $state)
      ($current
        (let* ((($feature $weight) $entry)
               ($counts (ai-math:numeric-feature-counts
                          $training $prefixes $feature $size $cutoff)))
          (case (tensor:entries $counts)
            (((TensorEntries $coordinates $seen)
               (let* (($denominators (tensor:gather $totals $coordinates))
                      ($deltas (tensor:zip-map f64 ($seen $denominators)
                                  ai-math:bayes-packed-delta ($sigma $weight $penalty)))
                      ($indexed (tensor:from-coordinates ($size) $coordinates $deltas)))
                 (tensor:merge $current $indexed sum)))
             ($other (Tensor:Fault packed-counts)))))))))
(= (ai-math:bayes-unit-score-tensor
      $training $features $cutoff $sigma $penalty $prefixes)
   (if (== $prefixes NoPrefix) AiBayes:Decline
     (let* (((AiNumericUse $table $size $names $guards)
              (ai-math:numeric-use-prefix $training $prefixes))
            ($current (postings:sources-current $guards)))
       (if (not $current) AiBayes:Stale
         (let* (($totals (ai-math:numeric-use-counts $table $size $cutoff))
                ($mass (case (tensor:dtype $totals)
                         ((i64 (tensor:sum $totals)) ($other (Tensor:Fault packed-counts))))))
           (case $mass
             (((Tensor:Fault $reason) AiBayes:Decline)
              ($amount
                (if (> $amount 9007199254740992) AiBayes:Decline
                  (let* (($weight-sum (list:sum-by ai-math:feature-entry-weight $features))
                         ($base (tensor:zip-map f64 ($totals) ai-math:bayes-packed-base ($penalty $weight-sum)))
                         ($scores (foldl-atom $features $base $state $entry
                           (ai-math:bayes-packed-feature
                             $state $training $prefixes $totals $size $cutoff $sigma $penalty $entry))))
                    (case (tensor:dtype $scores)
                      ((f64 $scores)
                       ($other AiBayes:Decline)))))))))))))
(= (ai-math:bayes-unit-packed $training $features $cutoff $sigma $penalty $prefixes)
   (let $scores (ai-math:bayes-unit-score-tensor $training $features $cutoff $sigma $penalty $prefixes)
     (case (tensor:dtype $scores)
       ((f64
          (let (AiNumericUse $table $size $names $guards)
            (ai-math:numeric-use-prefix $training $prefixes)
            (case (tensor:inspect $scores)
              (((TensorData f64 ($size) $entries)
                 (AiBayes:Packed
                   (map-atom $entries $entry
                     (let ($ordinal $score) $entry
                       (let $name (index-atom $names $ordinal) ($name $score))))))
               ($other AiBayes:Decline)))))
        ($other $scores)))))
(= (ai-math:naive-bayes-prefix-unit-reference
      (AiSearch $count $facts $weights (AiTraining $training $revision $prefixes))
      $goal $index $sigma $penalty)
   (let* (($search (AiSearch $count $facts $weights (AiTraining $training $revision $prefixes)))
          ($candidates (sort-atom (filter-atom
            (collapse (match $training
              (AiTrainingCandidate $name $first $ordinal $premise)
              ($ordinal $first $name $premise)))
            $entry (< (index-atom $entry 1) $index))))
          ($features (map-atom
            (sort-atom (ai-math:declaration-features $goal)) $feature
            ($feature (ai-math:weight $search Feature $feature 1.0)))))
     (ai-math:bayes-unit $training $candidates $features $index $sigma $penalty)))
; Arbitrary training subsets retain their meaning. Corpus queries use the
; already prepared ledger with a prefix cutoff, not an assumed subset match.
(= (ai-math:naive-bayes $search $goal $earlier $sigma $penalty $self-weight)
   (ai-math:bayes-from-training $search (ai-math:training $earlier) $goal All
     $sigma $penalty $self-weight))
(= (ai-math:naive-bayes-prefix (AiSearch $count $facts $weights $training)
      $goal $index $sigma $penalty $self-weight)
   (ai-math:bayes-from-training (AiSearch $count $facts $weights $training)
     $training $goal $index $sigma $penalty $self-weight))

(= (ai-math:search-goal (AiSearch $count $facts $weights $training) $index)
   (if (or (< $index 0) (>= $index $count))
     (Error (AiMathGoalIndex $index) ai-math:search-goal)
     (match $facts (AiSearchItem $index $fact) $fact)))
(= (ai-math:fact-contributions $search $goal $index $fact $name-weight $recency-weight)
   (let* (($name (ai-math:declaration-name $fact))
          ($kind (ai-math:declaration-kind $fact))
          ($symbols (ai-math:declaration-symbols $goal))
          ($definition (if (and (== $kind DEF) (ai-math:contains $symbols $name))
                         (($name 2.0)) ()))
          ($overlap (ai-math:overlap $search $symbols $fact))
          ($shared (if (> $overlap 0.0) (($name $overlap)) ()))
          ($named (if (and (ai-math:contains (THM AXIOM) $kind)
                           (not (== $name-weight 0.0)))
                    (($name (* $name-weight (ai-math:name-similarity $search
                                            (ai-math:declaration-name $goal) $name)))) ()))
          ($recent (if (and (ai-math:contains (THM AXIOM) $kind)
                            (not (== $recency-weight 0.0)))
                     (($name (/ $recency-weight
                                (+ 1.0 (/ (- $index (ai-math:declaration-index $fact)) 10.0))))) ())))
     (union-atom $definition (union-atom $shared (union-atom $named $recent)))))
(= (ai-math:fact-background-contributions
      $search $goal $index $fact $name-weight $recency-weight)
   (let* (($name (ai-math:declaration-name $fact))
          ($kind (ai-math:declaration-kind $fact))
          ($named (if (and (ai-math:contains (THM AXIOM) $kind)
                           (not (== $name-weight 0.0)))
                    (($name (* $name-weight (ai-math:name-similarity $search
                                            (ai-math:declaration-name $goal) $name)))) ()))
          ($recent (if (and (ai-math:contains (THM AXIOM) $kind)
                            (not (== $recency-weight 0.0)))
                     (($name (/ $recency-weight
                                (+ 1.0 (/ (- $index (ai-math:declaration-index $fact)) 10.0))))) ())))
     (union-atom $named $recent)))
(= (ai-math:bayes-bonuses $ranked $weight $decay $index)
   (if (== $ranked ()) ()
     (let ($entry $rest) (decons-atom $ranked)
       (let $bonus ((car-atom $entry) (/ $weight (+ 1.0 (/ $index $decay))))
         (cons-atom $bonus (ai-math:bayes-bonuses $rest $weight $decay (+ $index 1)))))))

; The packed default rank keeps source identity numeric until the final top-k
; observation. Each signal remains separately authored and is merged in the
; same order as the ordinary contribution fold: overlap, background, kNN,
; then Bayes. Unsupported observations decline to the ordinary rank below.
(= (ai-math:rank-recency $cutoff $weight $ordinal)
   (/ $weight (+ 1.0 (/ (- $cutoff $ordinal) 10.0))))

; Catalog positions can replace names only under the complete first-name
; correspondence. Totals and kind flags are immutable, owner-guarded columns.
(= (ai-math:prepare-symbol-rank-plan $facts $weights $guards)
   (let* (($size (size-atom $facts))
          ($rows (map-atom $facts $fact
            (let* (($name (ai-math:declaration-name $fact))
                   ($ordinal (ai-math:name-order-get $weights $name))
                   ($kind (ai-math:declaration-kind $fact)))
              ($ordinal
                (ai-math:get $weights (OverlapTotal $ordinal) 0.0)
                (ai-math:get $weights (StatementTotal $ordinal) 0.0)
                (if (== $kind THM) 1 0) (if (== $kind DEF) 1 0)))))
          ($ordinals (map-atom $rows $row (index-atom $row 0)))
          ($expected (list:to-expression (list:range $size))))
     (if (not (== $ordinals $expected)) NoSymbolRankPlan
       (let* (($overlap (tensor:from-values f64 ($size)
                 (map-atom $rows $row (index-atom $row 1))))
              ($statement (tensor:from-values f64 ($size)
                 (map-atom $rows $row (index-atom $row 2))))
              ($theorems (tensor:from-values i64 ($size)
                 (map-atom $rows $row (index-atom $row 3))))
              ($definitions (tensor:from-values i64 ($size)
                 (map-atom $rows $row (index-atom $row 4))))
              ($zeroes (tensor:from-values f64 ($size) (map-atom $facts $fact 0.0))))
         (if (and (== (tensor:dtype $overlap) f64)
               (and (== (tensor:dtype $statement) f64)
                 (and (== (tensor:dtype $theorems) i64)
                      (== (tensor:dtype $definitions) i64))))
           (AiSymbolRankPlan $overlap $statement $theorems $definitions $zeroes $guards)
           NoSymbolRankPlan)))))
(= (ai-math:rank-symbol-columns-attempt
      (AiSearch $count $facts $weights $training) $goal-symbols $cutoff)
   (let* (($plans (ai-math:get $weights RankPlanSpace NoRankPlanSpace))
          ($symbols (sort-atom (unique-atom $goal-symbols)))
          ($dimension (* $count (size-atom $symbols))))
     (if (or (== $plans NoRankPlanSpace)
           (or (> $dimension 9007199254740992)
             (not (== (filter-atom $symbols $symbol
               (not (== (get-type $symbol) String))) ())))) AiSymbols:Decline
       (case (ai-math:get $plans SymbolRankPlan NoSymbolRankPlan)
         (((AiSymbolRankPlan $overlap $statement $theorems $definitions $zeroes $metadata-guards)
            (case (ai-math:get $plans SymbolPlan NoSymbolPlan)
              (((AiSymbolPlan $table $guards)
                 (if (not (and (postings:sources-current $guards)
                               (postings:sources-current $metadata-guards))) AiSymbols:Decline
                   (let* (($queries (map-atom
                            (collapse (ai-math:positions 0 (size-atom $symbols))) $query
                            (let* (($symbol (index-atom $symbols $query))
                                   ($weight (ai-math:weight-in $weights Symbol $symbol 1.0)))
                              ($symbol ($weight $query)))))
                          ($space (context-space)))
                     (let $column-result (postings:try-table-counts $table table-fold-columns-before
                       ($space $queries $cutoff ai-math:symbol-group
                         (AiSymbolSums 0.0 0.0 -1) ai-math:symbol-step (f64 f64 i64)))
                       (case $column-result
                       (((Postings:Columns $left $right)
                          $column-result)
                        ($other AiSymbols:Decline)))))))
               ($other AiSymbols:Decline))))
          ($other AiSymbols:Decline))))))

(= (ai-math:rank-overlap-ratio $shared $total)
   (if (== $total 0.0) 0.0 (/ $shared $total)))
(= (ai-math:rank-overlap-enabled $ratio $definition)
   (if (or (> $ratio 0.0) (== $definition 1.0)) 1.0 0.0))
(= (ai-math:rank-overlap-value $ratio $definition)
   (if (== $definition 1.0)
     (if (> $ratio 0.0) (+ (+ 0 2.0) $ratio) (+ 0 2.0)) (+ 0 $ratio)))
; All enabled values are one, so top-k retains their original row order.
(= (ai-math:rank-keep-indices $enabled)
   (tensor:top-k $enabled (tensor:cast $enabled bool) (car-atom (tensor:shape $enabled))))
(= (ai-math:rank-gather-dense $values $indices)
   (tensor:convert (tensor:gather $values $indices) dense))
(= (ai-math:rank-definition-entries $weights $definitions $goal-symbols $cutoff)
   (let $symbols (sort-atom (unique-atom $goal-symbols))
     (collapse
     (let $symbol (superpose $symbols)
       (let $ordinal (ai-math:name-order-get $weights $symbol)
         (if (== $ordinal NoName) (superpose ())
           (if (>= $ordinal $cutoff) (superpose ())
             (case (tensor:at $definitions $ordinal)
               (((tensor:present 1) ($ordinal 1.0)) ($other (superpose ())))))))))))
(= (ai-math:rank-overlap-columns
      (AiSearch $count $facts $weights $training) $goal-symbols $cutoff $columns)
   (let* (($plans (ai-math:get $weights RankPlanSpace NoRankPlanSpace))
          ((AiSymbolRankPlan $overlap-totals $statement-totals $theorems $definitions $zeroes $guards)
            (ai-math:get $plans SymbolRankPlan NoSymbolRankPlan))
          ($labels (postings:column-labels $columns))
          (($overlap $statement $first) (postings:column-values $columns))
          ($coordinates (tensor:cast $labels index))
          ($totals (ai-math:rank-gather-dense $overlap-totals $coordinates))
          ($definition-entries (ai-math:rank-definition-entries $weights $definitions $goal-symbols $cutoff))
          ($definition-mask (tensor:merge $zeroes (tensor:from-coo f64 ($count) $definition-entries reject) sum))
          ($definition-flags (ai-math:rank-gather-dense $definition-mask $coordinates))
          ($ratios (tensor:convert (tensor:zip-map f64 ($overlap $totals) ai-math:rank-overlap-ratio ()) dense))
          ($enabled (tensor:convert (tensor:zip-map f64 ($ratios $definition-flags) ai-math:rank-overlap-enabled ()) dense))
          ($values (tensor:convert (tensor:zip-map f64 ($ratios $definition-flags) ai-math:rank-overlap-value ()) dense))
          ($selected (ai-math:rank-keep-indices $enabled)))
     (tensor:from-coordinates ($count)
       (ai-math:rank-gather-dense $coordinates $selected) (ai-math:rank-gather-dense $values $selected))))
(= (ai-math:rank-neighbor-score $goal-total $shared $total $theorem $first)
   (let $union (- (+ $goal-total $total) $shared)
     (if (and (>= $first 0) (and (== $theorem 1) (> $union 0.0))) (/ $shared $union) 0.0)))
(= (ai-math:rank-positive $value) (if (> $value 0.0) 1.0 0.0))
; The mixed-radix coordinate is the statement introduction/ordinal tie key.
; The caller bounds its entire range within exact binary64 integers.
(= (ai-math:rank-neighbor-coordinate $width $ordinal $first)
   (if (< $first 0) 0 (+ (* $first $width) $ordinal)))
(= (ai-math:rank-neighbors-columns
      (AiSearch $count $facts $weights $training) $goal-symbols $columns $limit)
   (let* (($search (AiSearch $count $facts $weights $training))
          ($plans (ai-math:get $weights RankPlanSpace NoRankPlanSpace))
          ((AiSymbolRankPlan $overlap-totals $statement-totals $theorems $definitions $zeroes $guards)
            (ai-math:get $plans SymbolRankPlan NoSymbolRankPlan))
          ($labels (postings:column-labels $columns))
          (($overlap $statement $first) (postings:column-values $columns))
          ($coordinates (tensor:cast $labels index))
          ($totals (ai-math:rank-gather-dense $statement-totals $coordinates))
          ($theorem-flags (ai-math:rank-gather-dense $theorems $coordinates))
          ($goal-total (ai-math:sum-weights $search Symbol $goal-symbols 1.0))
          ($scores (tensor:convert (tensor:zip-map f64 ($statement $totals $theorem-flags $first)
            ai-math:rank-neighbor-score ($goal-total)) dense))
          ($enabled (tensor:convert (tensor:zip-map f64 ($scores) ai-math:rank-positive ()) dense))
          ($selected (ai-math:rank-keep-indices $enabled))
          ($key-values (tensor:zip-map f64 ($labels $first) ai-math:rank-neighbor-coordinate ($count)))
          ($keys (tensor:cast $key-values index))
          ($dimension (* $count (size-atom (unique-atom $goal-symbols))))
          ($ranked (tensor:from-coordinates ($dimension)
            (ai-math:rank-gather-dense $keys $selected) (ai-math:rank-gather-dense $scores $selected)))
          ($retained (tensor:top-k $ranked $limit)))
     (case (tensor:inspect $retained)
       (((TensorData index $shape $entries)
          (map-atom $entries $entry
            (let* (($key (index-atom $entry 1))
                   ($ordinal (% $key $count))
                   ($fact (ai-math:search-fact-at $search $ordinal))
                   ((tensor:present $score) (tensor:at $ranked $key)))
              ($fact $score))))
        ($other AiSymbols:Decline)))))
; The prepared renaming is total and injective. Its guards bind both the
; training identities and the catalog's first-name coordinates to their owners.
(= (ai-math:prepare-bayes-rank-plan $weights (AiTraining $training $revision $prefixes))
   (if (== $prefixes NoPrefix) NoBayesRankPlan
     (case (ai-math:numeric-use-prefix $training $prefixes)
       (((AiNumericUse $table $size $names $source-guards)
          (let* (($coordinates (map-atom $names $name (ai-math:name-order-get $weights $name)))
                 ($missing (filter-atom $coordinates $coordinate (== $coordinate NoName))))
            (if (not (== $missing ())) NoBayesRankPlan
              (if (not (== (size-atom (unique-atom $coordinates)) $size)) NoBayesRankPlan
                (let* (($mapping (tensor:from-values index ($size) $coordinates))
                       ($positions (tensor:from-values i64 ($size)
                         (list:to-expression (list:range $size)))))
                  (if (and (== (tensor:dtype $mapping) index) (== (tensor:dtype $positions) i64))
                    (AiBayesRankPlan $mapping $positions
                      (($weights (_minimal-space-revision $weights))
                       ($training $revision)))
                    NoBayesRankPlan))))))
        ($other NoBayesRankPlan)))))
; Grouping each unique coordinate used to add its contribution to integer
; zero. Keep that scalar operation, including its floating-point behavior.
(= (ai-math:rank-bayes-bonus $weight $decay $position)
   (+ 0 (/ $weight (+ 1.0 (/ $position $decay)))))
(= (ai-math:rank-bayes-from-scores $size $scores $mapping $positions)
   (let $order (tensor:top-k $scores (car-atom (tensor:shape $scores)))
     (case (tensor:dtype $order)
       ((index
          (let* (($count (car-atom (tensor:shape $order)))
                 ($selected (tensor:view $positions ($count) (1) 0))
                 ($bonuses (tensor:zip-map f64 ($selected) ai-math:rank-bayes-bonus (3.0 8.0)))
                 ($coordinates (tensor:gather $mapping $order))
                 ($result (tensor:from-coordinates ($size) $coordinates $bonuses)))
            (case (tensor:dtype $result)
              ((f64 $result) ($other AiRank:Decline)))))
        ($other AiRank:Decline)))))
(= (ai-math:rank-bayes-tensor
      (AiSearch $count $facts $weights (AiTraining $training $revision $prefixes)) $index $goal)
   (let* (($search (AiSearch $count $facts $weights (AiTraining $training $revision $prefixes)))
          ($plans (ai-math:get $weights RankPlanSpace NoRankPlanSpace)))
     (case (if (== $plans NoRankPlanSpace) NoBayesRankPlan
             (ai-math:get $plans BayesRankPlan NoBayesRankPlan))
       (((AiBayesRankPlan $mapping $positions $guards)
          (if (not (postings:sources-current $guards)) AiRank:Decline
            (let* (($features (map-atom (sort-atom (ai-math:declaration-features $goal)) $feature
                               ($feature (ai-math:weight $search Feature $feature 1.0))))
                   ($scores (ai-math:bayes-unit-score-tensor
                     $training $features $index 10.0 -4.0 $prefixes)))
              (case (tensor:dtype $scores)
                ((f64 (ai-math:rank-bayes-from-scores $count $scores $mapping $positions))
                 ($other AiRank:Decline))))))
        ($other AiRank:Decline)))))
(= (ai-math:rank-prefix-count $handle $cutoff)
   (case (postings:counts-before $handle $cutoff)
     ((() 0)
      (((RankCandidates $count)) $count)
      ($other AiRank:Decline))))
(= (ai-math:rank-background-tensor $size $weights $cutoff $weight)
   (let $plans (ai-math:get $weights RankPlanSpace NoRankPlanSpace)
   (case (if (== $plans NoRankPlanSpace) NoRankPlan
           (ai-math:get $plans RankPlan NoRankPlan))
     (((AiRankPlan $prefix $coordinates $guards)
        (if (not (postings:sources-current $guards)) AiRank:Decline
          (let $eligible (ai-math:rank-prefix-count $prefix $cutoff)
            (if (== $eligible AiRank:Decline) AiRank:Decline
              (let* (($selected
                       (tensor:view $coordinates ($eligible) (1) 0))
                     ($scores (tensor:zip-map f64 ($selected)
                       ai-math:rank-recency ($cutoff $weight))))
                (tensor:from-coordinates
                  ($size) $selected $scores))))))
      ($other AiRank:Decline)))))
(= (ai-math:rank-coordinate-entry $weights $entry)
   (let ($name $score) $entry
     (let $ordinal (ai-math:name-order-get $weights $name)
       (if (== $ordinal NoName) NoRankCoordinate ($ordinal $score)))))
(= (ai-math:rank-coordinate-block $weights $entries)
   (filter-atom
     (map-atom $entries $entry (ai-math:rank-coordinate-entry $weights $entry))
     $entry (not (== $entry NoRankCoordinate))))
(= (ai-math:rank-coordinate-tensor $size $blocks)
   (tensor:from-coo f64 ($size)
     (list:group-sums-number-blocks $blocks) reject))
(= (ai-math:rank-merge-signals $signals)
   (let ($first $rest) (decons-atom $signals)
     (foldl-atom $rest $first $state $signal
       (tensor:merge $state $signal sum))))
(= (ai-math:rank-packed-output $search $scores $indices)
   (case (tensor:inspect $indices)
     (((TensorData index ($count) $entries)
        (map-atom $entries $entry
          (let* (($source (index-atom $entry 1))
                 ($fact (ai-math:search-fact-at $search $source))
                 ((tensor:present $score) (tensor:at $scores $source)))
            ((ai-math:declaration-name $fact) $score))))
      ($other AiRank:Decline))))
(= (ai-math:rank-packed-attempt
      (AiSearch $count $facts $weights $training) $index $goal $limit)
   (let* (($search (AiSearch $count $facts $weights $training))
          ($symbol-columns (ai-math:rank-symbol-columns-attempt $search
            (ai-math:declaration-symbols $goal) $index))
          ($symbol-summary (case $symbol-columns
            (((Postings:Columns $left $right) AiSymbols:Decline)
             ($columns-unavailable (ai-math:symbol-shared-attempt $search
               (ai-math:declaration-symbols $goal) $index)))))
          ($overlap-packed (case $symbol-columns
            (((Postings:Columns $left $right) (ai-math:rank-overlap-columns $search (ai-math:declaration-symbols $goal) $index $symbol-columns))
             ($overlap-columns-unavailable AiSymbols:Decline))))
          ($overlap (if (== (tensor:dtype $overlap-packed) f64) $overlap-packed
            (let $overlap-source-rows (case $symbol-summary
              (((AiSymbols $overlap-states) (ai-math:overlap-rows-from-symbols $search (AiSymbols $overlap-states)))
               ($overlap-declined (ai-math:overlap-rows $search (ai-math:declaration-symbols $goal) $index))))
              (ai-math:rank-coordinate-tensor $count
                (ai-math:overlap-coordinates-from-rows $search (ai-math:declaration-symbols $goal) $overlap-source-rows)))))
          ($background (ai-math:rank-background-tensor
            $count $weights $index 1.0))
          ($neighbors-packed (case $symbol-columns
            (((Postings:Columns $left $right)
               (ai-math:rank-neighbors-columns $search (ai-math:declaration-symbols $goal) $symbol-columns 24))
             ($neighbor-columns-unavailable AiSymbols:Decline))))
          ($neighbors (case $neighbors-packed
            ((AiSymbols:Decline (case $symbol-summary
               (((AiSymbols $neighbor-states) (ai-math:neighbors-from-symbols $search
                  (ai-math:declaration-symbols $goal) (AiSymbols $neighbor-states)))
                ($neighbor-declined (ai-math:neighbors-prefix $search (ai-math:declaration-symbols $goal) $index)))))
             ($neighbor-values $neighbor-values))))
          ($votes (ai-math:knn-from-neighbors $neighbors 24))
          ($top (ai-math:maximum-score $votes))
          ($knn-rows (if (> $top 0.0)
            (map-atom $votes $entry
              (let ($name $vote) $entry
                ($name (/ (* 1.5 $vote) $top)))) ()))
          ($knn (ai-math:rank-coordinate-tensor $count
            ((ai-math:rank-coordinate-block $weights $knn-rows))))
          ($bayes-tensor (ai-math:rank-bayes-tensor $search $index $goal))
          ($nb (case (tensor:dtype $bayes-tensor)
            ((f64 $bayes-tensor)
             ($declined
               (let $nb-rows (ai-math:bayes-bonuses
                 (ai-math:sort-scores
                   (ai-math:naive-bayes-prefix $search $goal $index 10.0 -4.0 1.0))
                 3.0 8.0 0)
                 (ai-math:rank-coordinate-tensor $count
                   ((ai-math:rank-coordinate-block $weights $nb-rows))))))))
          ($scores (ai-math:rank-merge-signals
            ($overlap $background $knn $nb)))
          ($indices (tensor:top-k $scores $limit)))
     (case $indices
       (((Tensor:Fault $reason) AiRank:Decline)
        ($answer
          (case (ai-math:rank-packed-output $search $scores $answer)
            ((AiRank:Decline AiRank:Decline)
             ($rows (AiRank:Packed $rows)))))))))
(= (ai-math:rank-packed-default $search $index $goal $limit)
   (case (ai-math:rank-packed-attempt $search $index $goal $limit)
     (((AiRank:Packed $rows) $rows)
      ($other $other))))
(= (ai-math:rank $search $index) (ai-math:rank-with $search $index 32 ()))
(= (ai-math:rank $search $index $limit) (ai-math:rank-with $search $index $limit ()))
(= (ai-math:rank-with (AiSearch $count $facts $weights $training) $index $limit $options)
   (let $search (AiSearch $count $facts $weights $training)
     (case (ai-math:search-goal $search $index)
       (((Error $reason $where) (Error $reason $where))
        ($goal
          (if (== $options ())
            (case (ai-math:rank-packed-attempt $search $index $goal $limit)
              (((AiRank:Packed $rows) $rows)
               ($other (ai-math:rank-for $search $index $goal $limit $options))))
            (ai-math:rank-for $search $index $goal $limit $options)))))))

; An intermediate statement has its own features, while its source frontier
; remains explicit. Its original proof and later facts never train the query.
(= (ai-math:rank-for (AiSearch $count $facts $weights $training) $index $goal $limit $options)
   (let $search (AiSearch $count $facts $weights $training)
     (if (or (< $index 0) (> $index $count))
       (Error (AiMathGoalIndex $index) ai-math:rank-for)
       (let* (($earlier (ai-math:search-before $search $index))
                ($name-weight (ai-math:option $options name-weight 0.0))
                ($recency-weight (ai-math:option $options recency-weight 1.0))
                ($overlap (ai-math:overlap-contribution-blocks $search
                            (ai-math:declaration-symbols $goal) $index))
                ($background (map-atom $earlier $fact
                   (ai-math:fact-background-contributions
                     $search $goal $index $fact $name-weight $recency-weight)))
                ($votes (ai-math:knn-prefix $search
                          (ai-math:declaration-symbols $goal) $index 24))
                ($top (ai-math:maximum-score $votes))
                ($knn (if (> $top 0.0)
                        (map-atom $votes $entry
                          (let ($name $vote) $entry
                            ($name (/ (* (ai-math:option $options knn-weight 1.5) $vote) $top)))) ()))
                ($nb-weight (ai-math:option $options nb-weight 3.0))
                ($nb (if (== $nb-weight 0.0) ()
                       (ai-math:bayes-bonuses
                         (ai-math:sort-scores (ai-math:naive-bayes-prefix $search $goal $index
                           (ai-math:option $options nb-sigma 10.0)
                           (ai-math:option $options nb-penalty -4.0)
                           (ai-math:option $options nb-self-weight 1.0)))
                         $nb-weight (ai-math:option $options nb-decay 8.0) 0)))
                ($blocks (union-atom $overlap
                           (union-atom $background ($knn $nb))))
                ($scores (list:group-sums-number-blocks $blocks)))
           (list:take $limit
             (ai-math:sort-scores-with-order $weights $index $scores))))))

(= (ai-math:diverse-slices $search $index)
   (ai-math:diverse-slices $search $index 24 4))
(= (ai-math:diverse-slices (AiSearch $size $facts $weights $training) $index $count $nearest)
   (let $search (AiSearch $size $facts $weights $training)
     (case (ai-math:search-goal $search $index)
       (((Error $reason $where) (Error $reason $where))
        ($goal
         (let* (($earlier (ai-math:search-before $search $index))
                ($allowed (map-atom (filter-atom $earlier $decl
                             (ai-math:contains (THM AXIOM)
                               (ai-math:declaration-kind $decl)))
                            $decl (ai-math:declaration-name $decl)))
                ($bayes (list:take $count (ai-math:sort-scores
                          (filter-atom
                            (ai-math:naive-bayes-prefix
                              $search $goal $index 10.0 -4.0 1.0)
                            $entry
                            (ai-math:contains $allowed (car-atom $entry))))))
                ($knn (foldl-atom
                        (list:take $nearest (ai-math:neighbors-prefix $search
                          (ai-math:declaration-symbols $goal) $index)) () $found $entry
                        (let $decl (car-atom $entry)
                          (foldl-atom (cons-atom (ai-math:declaration-name $decl)
                                        (sort-atom (ai-math:declaration-dependencies $decl)))
                            $found $out $name
                            (if (and (ai-math:contains $allowed $name)
                                     (not (ai-math:contains $out $name)))
                              (union-atom $out ($name)) $out)))))
                ($symbol (list:take $count (ai-math:sort-scores
                           (map-atom
                             (filter-atom
                               (ai-math:overlap-rows $search
                                 (ai-math:declaration-symbols $goal) $index)
                               $row
                               (let (AiOverlapScore $ordinal $fact $score) $row
                                 (ai-math:contains (THM AXIOM)
                                   (ai-math:declaration-kind $fact))))
                             $row
                             (let (AiOverlapScore $ordinal $fact $score) $row
                               ((ai-math:declaration-name $fact) $score)))))))
           (DiverseSlices (nb (ai-math:entry-names $bayes)) (knn (list:take (* 2 $count) $knn))
             (sym (ai-math:entry-names
                    (filter-atom $symbol $entry (> (index-atom $entry 1) 0.0)))))))))))

(= (ai-math:recall-samples $search $decls $cutoffs)
   (let* (($theorems (filter-atom $decls $decl
                      (and (== (ai-math:declaration-kind $decl) THM)
                           (> (size-atom (ai-math:declaration-dependencies $decl)) 0))))
          ($maximum (foldl-atom $cutoffs 0 $best $k (if (> $k $best) $k $best))))
     (map-atom $theorems $decl
       (let* (($truth (ai-math:declaration-dependencies $decl))
              ($ranked (ai-math:entry-names
                         (ai-math:rank $search (ai-math:declaration-index $decl) $maximum))))
         (map-atom $cutoffs $k
           (let $got (size-atom (intersection-atom (list:take $k $ranked) $truth))
             (AiRecall $k (/ $got (size-atom $truth))
               (if (== $got (size-atom $truth)) 1 0))))))))
(= (ai-math:recall-at $samples $index $cutoff)
   (let* (($values (map-atom $samples $row (index-atom $row $index)))
          ($sum (foldl-atom $values 0.0 $total $entry (+ $total (index-atom $entry 2))))
          ($complete (foldl-atom $values 0 $total $entry (+ $total (index-atom $entry 3))))
          ($count (size-atom $samples)))
     (RecallAt $cutoff
       (Mean (if (== $count 0) NoTheorems (/ $sum $count)))
       (Complete $complete (if (== $count 0) NoTheorems (/ $complete $count))))))
(= (ai-math:evaluate-recall $decls) (ai-math:evaluate-recall $decls (8 16 32 64)))
(= (ai-math:evaluate-recall $decls $cutoffs)
   (ai-math:search-recall (ai-math:search $decls) $cutoffs))
(= (ai-math:search-recall $search $cutoffs)
   (let $samples (ai-math:recall-samples $search (ai-math:search-facts $search) $cutoffs)
     (RecallSummary (size-atom $samples) (ai-math:recall-columns $samples $cutoffs 0))))
(= (ai-math:recall-columns $samples $cutoffs $index)
   (if (== $cutoffs ()) ()
     (let ($k $rest) (decons-atom $cutoffs)
       (let $column (ai-math:recall-at $samples $index $k)
         (cons-atom $column (ai-math:recall-columns $samples $rest (+ $index 1)))))))
