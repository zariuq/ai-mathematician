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
     (filter-atom (str:split "_" $name) $part (not (== $part ""))))))

(= (ai-math:index-document $space $ordinal $decl)
   (let* (($name (ai-math:declaration-name $decl))
          ($kind (ai-math:declaration-kind $decl))
          ($statement-symbols
            (sort-atom (unique-atom (ai-math:declaration-symbols $decl))))
          ($overlap-symbols
            (sort-atom (unique-atom
              (cons-atom $name $statement-symbols))))
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
              ($documents (new-space))
              ($indexed (foldl-atom $facts 0 $ordinal $decl
                          (let $stored
                            (ai-math:index-document $documents $ordinal $decl)
                            (+ $ordinal 1))))
              ($keys (unique-atom
                       (collapse (match $documents (AiDocument $kind $key $index)
                                                   (AiFeature $kind $key)))))
              ($weights $documents)
              ($prepared (map-atom $keys $feature
                           (ai-math:prepare-weight $weights $documents
                             $size $feature)))
              ($totals (foldl-atom $facts 0 $ordinal $fact
                         (let $stored
                           (ai-math:prepare-fact-totals $weights $ordinal $fact)
                           (+ $ordinal 1))))
              ($catalog (new-space))
              ($stored (foldl-atom $facts 0 $ordinal $fact
                         (let $entry
                           (add-atom $catalog (AiSearchItem $ordinal $fact))
                           (+ $ordinal 1))))
              ($training (ai-math:training $facts)))
         (AiSearch $size $catalog $weights $training))))))
(= (ai-math:prepare-weight $weights $documents $size (AiFeature $kind $key))
   (let* (($count (size-atom
                   (collapse (match $documents (AiDocument $kind $key $index) $index))))
          ($log (ai-math:ln (/ (+ $size 1.0) (+ $count 1.0))))
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
(= (ai-math:sum-weights $search $kind $items $default)
   (foldl-atom (sort-atom (unique-atom $items)) 0.0 $sum $key
     (+ $sum (ai-math:weight $search $kind $key $default))))

; Group additive evidence through a space's existing key index. Ordinals
; retain floating-addition and tie order; they do not constrain result bags.
(= (ai-math:group-sums $entries)
   (let* (($space (new-space))
          ($indexed (ai-math:store-contributions $space $entries 0))
          ($keys (unique-atom (map-atom $entries $entry (car-atom $entry)))))
     (map-atom $keys $key
       ($key (ai-math:contribution-score $space $key)))))
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
(= (ai-math:sort-scores $entries)
   (let (AiSort $count $rows)
     (foldl-atom $entries (AiSort 0 ()) $state $entry
       (let (AiSort $index $rows) $state
         (let $key (AiSortKey (- 0.0 (index-atom $entry 1)) $index)
           (AiSort (+ $index 1) (cons-atom ($key $entry) $rows)))))
     (unkey-atom (sort-atom $rows))))
(= (ai-math:name-order-get $order $name)
   (let $ordinals
     (sort-atom
       (collapse (match $order (AiNameOrder $name $ordinal) $ordinal)))
     (if (== $ordinals ()) NoName (car-atom $ordinals))))
(= (ai-math:sort-scores-with-order $order $cutoff $scores)
   (unkey-atom (sort-atom
     (map-atom
       (filter-atom $scores $entry
         (let $ordinal (ai-math:name-order-get $order (car-atom $entry))
           (and (not (== $ordinal NoName)) (< $ordinal $cutoff))))
       $entry
       (let* ((($name $score) $entry)
              ($ordinal (ai-math:name-order-get $order $name)))
         ((AiSortKey (- 0.0 $score) $ordinal) $entry))))))
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
     (ai-math:group-sums
       (foldl-atom (sort-atom (unique-atom $goal-symbols)) () $out $symbol
         (union-atom $out
           (map-atom
             (filter-atom
               (collapse (match $weights
                 (AiOverlapSymbol $symbol $ordinal) $ordinal))
               $ordinal (< $ordinal $cutoff))
             $ordinal
             ($ordinal (ai-math:weight $search Symbol $symbol 1.0))))))))
(= (ai-math:statement-shared (AiSearch $count $facts $weights $training)
      $goal-symbols $cutoff)
   (let $search (AiSearch $count $facts $weights $training)
     (ai-math:group-sums
       (foldl-atom (sort-atom (unique-atom $goal-symbols)) () $out $symbol
         (union-atom $out
           (map-atom
             (filter-atom
               (collapse (match $weights
                 (AiStatementSymbol $symbol $ordinal) $ordinal))
               $ordinal (< $ordinal $cutoff))
             $ordinal
             ($ordinal (ai-math:weight $search Symbol $symbol 1.0))))))))
(= (ai-math:overlap-rows (AiSearch $count $facts $weights $training)
      $goal-symbols $cutoff)
   (let $search (AiSearch $count $facts $weights $training)
     (map-atom (ai-math:overlap-shared $search $goal-symbols $cutoff) $entry
       (let ($ordinal $shared) $entry
         (let* (($fact (ai-math:search-fact-at $search $ordinal))
                ($total (ai-math:get $weights (OverlapTotal $ordinal) 0.0)))
           (AiOverlapScore $ordinal $fact
             (if (== $total 0.0) 0.0 (/ $shared $total))))))))
(= (ai-math:overlap-contributions $search $goal-symbols $cutoff)
   (foldl-atom (ai-math:overlap-rows $search $goal-symbols $cutoff) () $out $row
     (let (AiOverlapScore $ordinal $fact $score) $row
       (let* (($name (ai-math:declaration-name $fact))
              ($shared (if (> $score 0.0) (($name $score)) ()))
              ($definition
                (if (and (== (ai-math:declaration-kind $fact) DEF)
                         (ai-math:contains $goal-symbols $name))
                  (($name 2.0)) ())))
         (union-atom $out (union-atom $definition $shared))))))
(= (ai-math:neighbors-prefix (AiSearch $count $facts $weights $training)
      $goal-symbols $cutoff)
   (let* (($search (AiSearch $count $facts $weights $training))
          ($goal-total (ai-math:sum-weights $search Symbol $goal-symbols 1.0)))
     (ai-math:sort-scores
       (filter-atom
         (map-atom (ai-math:statement-shared $search $goal-symbols $cutoff) $entry
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
   (ai-math:group-sums
     (foldl-atom (list:take $count $neighbors)
       () $out $entry
       (let ($decl $similarity) $entry
         (union-atom $out
           (cons-atom ((ai-math:declaration-name $decl) $similarity)
             (map-atom (sort-atom (ai-math:declaration-dependencies $decl)) $name
               ($name $similarity))))))))

; Preparation records evidence once. A premise owns a local ledger, so a
; query does not scan other premises' feature rows. Keys remain strings.
; Source ordinals delimit training; event ordinals retain addition/tie order.
; Self/citation events stay distinct, allowing any query's self-weight without
; rebuilding or regrouping floating additions.
(= (ai-math:training $facts)
   (let* (($training (new-space))
          ($indexed (foldl-atom $facts (AiTrainingPosition 0 0) $position $fact
                      (let (AiTrainingPosition $source $ordinal) $position
                        (AiTrainingPosition (+ $source 1)
                          (ai-math:train-declaration $training $source $ordinal $fact))))))
     $training))
(= (ai-math:training-ledger $training $name $source $ordinal)
   (case (collapse (match $training (AiTrainingCandidate $name $first $event $ledger) $ledger))
     ((() (let* (($ledger (new-space))
                 ($stored (add-atom $training
                            (AiTrainingCandidate $name $source $ordinal $ledger))))
            $ledger))
      (($ledger) $ledger))))
(= (ai-math:train-event $training $source $ordinal $name $kind $features)
   (let* (($ledger (ai-math:training-ledger $training $name $source $ordinal))
          ($use (add-atom $ledger (AiTrainingUse $ordinal $source $kind)))
          ($indexed (map-atom $features $feature
                      (let $local
                        (add-atom $ledger
                          (AiTrainingFeature $feature $ordinal $source $kind))
                        (add-atom $training
                          (AiTrainingPosting $feature $name $ordinal $source $kind))))))
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
(= (ai-math:training-entries $ledger $key)
   (case $key
     ((Uses (collapse (match $ledger (AiTrainingUse $event $source $kind) ($event $source $kind))))
      ((Feature $feature) (collapse (match $ledger
        (AiTrainingFeature $feature $ordinal $origin $role) ($ordinal $origin $role)))))))
(= (ai-math:training-evidence-count $ledger $key $cutoff $policy)
   (case $policy
    ((AiTraining:Unit
     (let* (($sources (case $key
               ((Uses (collapse (match $ledger (AiTrainingUse $event $source $kind) $source)))
                ((Feature $feature) (collapse (match $ledger
                  (AiTrainingFeature $feature $ordinal $origin $role) $origin))))))
            ($count (size-atom (filter-atom $sources $position (ai-math:training-before $position $cutoff)))))
       (if (<= $count 9007199254740992)
         (if (== $count 0) 0 (+ 0.0 $count))
         (ai-math:training-sum (ai-math:training-entries $ledger $key) $cutoff 1.0))))
     ((AiTraining:Weighted $self-weight)
       (ai-math:training-sum (ai-math:training-entries $ledger $key) $cutoff $self-weight)))))
(= (ai-math:bayes-from-training $search $training $goal $cutoff $sigma $penalty $self-weight)
   (let* (($candidates (sort-atom (filter-atom
                        (collapse (match $training
                          (AiTrainingCandidate $name $first $ordinal $ledger)
                          ($ordinal $first $name $ledger)))
                        $entry (ai-math:training-before (index-atom $entry 1) $cutoff))))
          ($policy (if (== (str:number->string $self-weight) "1.0")
                     AiTraining:Unit (AiTraining:Weighted $self-weight)))
          ($features (map-atom (sort-atom (ai-math:declaration-features $goal)) $feature
                       ($feature (ai-math:weight $search Feature $feature 1.0)))))
     (if (== $policy AiTraining:Unit)
       (ai-math:bayes-unit-sparse
         $training $candidates $features $cutoff $sigma $penalty)
       (map-atom $candidates $candidate
         (let* ((($ordinal $first $name $ledger) $candidate)
                ($total (ai-math:training-evidence-count $ledger Uses $cutoff $policy)))
           ($name
             (foldl-atom $features (ai-math:ln $total) $score $entry
               (let ($feature $weight) $entry
                 (let $seen (ai-math:training-evidence-count $ledger (Feature $feature) $cutoff $policy)
                   (+ $score (* $weight (if (== $seen 0.0) $penalty
                                           (ai-math:ln (/ (* $sigma $seen) $total))))))))))))))

; The dense candidate/feature fold is the reference route for unit evidence.
; It also remains the fallback above binary64's exact-integer range.
(= (ai-math:bayes-unit $candidates $features $cutoff $sigma $penalty)
   (map-atom $candidates $candidate
     (let* ((($ordinal $first $name $ledger) $candidate)
            ($sources (collapse (match $ledger (AiTrainingUse $event $source $kind) $source)))
            ($count (size-atom (if (== $cutoff All) $sources
                                 (filter-atom $sources $position (< $position $cutoff)))))
            ($total (if (<= $count 9007199254740992) (+ 0.0 $count)
                      (ai-math:training-sum (ai-math:training-entries $ledger Uses) $cutoff 1.0))))
       ($name
         (foldl-atom $features (ai-math:ln $total) $score $entry
           (let ($feature $weight) $entry
             (let $origins (collapse (match $ledger
                               (AiTrainingFeature $feature $event $source $kind) $source))
               (if (== $origins ()) (+ $score (* $weight $penalty))
                 (let* (($feature-count (size-atom
                             (if (== $cutoff All) $origins
                               (filter-atom $origins $position (< $position $cutoff)))))
                    ($seen (if (<= $feature-count 9007199254740992) (+ 0.0 $feature-count)
                             (ai-math:training-sum
                               (ai-math:training-entries $ledger (Feature $feature)) $cutoff 1.0))))
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
(= (ai-math:training-unit-total $ledger $cutoff)
   (let $sources
     (collapse (match $ledger (AiTrainingUse $event $source $kind) $source))
     (size-atom
       (if (== $cutoff All) $sources
         (filter-atom $sources $position (< $position $cutoff))))))
(= (ai-math:bayes-unit-summary $candidate $cutoff)
   (let ($ordinal $first $name $ledger) $candidate
     (AiBayesUnitCandidate $ordinal $first $name $ledger
       (ai-math:training-unit-total $ledger $cutoff))))
(= (ai-math:feature-entry-weight ($feature $weight)) $weight)
(= (ai-math:training-posting-counts $training $feature $cutoff)
   (let $names
     (unique-atom
       (map-atom
         (filter-atom
           (collapse (match $training
             (AiTrainingPosting $feature $name $event $source $kind)
             ($name $source)))
           $posting
           (let ($name $source) $posting
             (ai-math:training-before $source $cutoff)))
         $posting (car-atom $posting)))
     (map-atom $names $name
       (let $sources
         (collapse (match $training
           (AiTrainingPosting $feature $name $event $source $kind) $source))
         ($name
           (size-atom
             (if (== $cutoff All) $sources
               (filter-atom $sources $source (< $source $cutoff)))))))))
(= (ai-math:bayes-feature-deltas
      $training $totals $feature $weight $cutoff $sigma $penalty)
   (map-atom
     (ai-math:training-posting-counts $training $feature $cutoff)
     $entry
     (let ($name $seen-count) $entry
       (let* (($seen (+ 0.0 $seen-count))
              ($total (ai-math:get $totals (BayesTotal $name) 0.0)))
         ($name (* $weight
           (- (ai-math:ln (/ (* $sigma $seen) $total)) $penalty)))))))
(= (ai-math:bayes-unit-sparse
      $training $candidates $features $cutoff $sigma $penalty)
   (let* (($summaries (map-atom $candidates $candidate
                         (ai-math:bayes-unit-summary $candidate $cutoff)))
          ($unsafe (filter-atom $summaries $summary
                     (> (index-atom $summary 5) 9007199254740992))))
     (if (not (== $unsafe ()))
       (ai-math:bayes-unit $candidates $features $cutoff $sigma $penalty)
       (let* (($totals (new-space))
              ($stored-totals (map-atom $summaries $summary
                (let (AiBayesUnitCandidate $ordinal $first $name $ledger $count) $summary
                  (let $total (+ 0.0 $count)
                    (add-atom $totals
                      (AiEntry (BayesTotal $name) $total))))))
              ($weight-sum (list:sum-by ai-math:feature-entry-weight $features))
              ($scores (new-space))
              ($base-end (ai-math:store-contributions $scores
                (map-atom $summaries $summary
                  (let (AiBayesUnitCandidate $ordinal $first $name $ledger $count) $summary
                    (let $total (+ 0.0 $count)
                      ($name (+ (ai-math:ln $total)
                                (* $penalty $weight-sum))))))
                0))
              ($delta-end (foldl-atom $features $base-end $next $entry
                (let ($feature $weight) $entry
                  (ai-math:store-contributions $scores
                    (ai-math:bayes-feature-deltas
                      $training $totals $feature $weight $cutoff $sigma $penalty)
                    $next)))))
         (map-atom $summaries $summary
           (let (AiBayesUnitCandidate $ordinal $first $name $ledger $count) $summary
             ($name (ai-math:contribution-score $scores $name))))))))
(= (ai-math:naive-bayes-prefix-unit-reference
      (AiSearch $count $facts $weights $training)
      $goal $index $sigma $penalty)
   (let* (($search (AiSearch $count $facts $weights $training))
          ($candidates (sort-atom (filter-atom
            (collapse (match $training
              (AiTrainingCandidate $name $first $ordinal $ledger)
              ($ordinal $first $name $ledger)))
            $entry (< (index-atom $entry 1) $index))))
          ($features (map-atom
            (sort-atom (ai-math:declaration-features $goal)) $feature
            ($feature (ai-math:weight $search Feature $feature 1.0)))))
     (ai-math:bayes-unit $candidates $features $index $sigma $penalty)))
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
(= (ai-math:rank $search $index) (ai-math:rank-with $search $index 32 ()))
(= (ai-math:rank $search $index $limit) (ai-math:rank-with $search $index $limit ()))
(= (ai-math:rank-with (AiSearch $count $facts $weights $training) $index $limit $options)
   (let $search (AiSearch $count $facts $weights $training)
     (case (ai-math:search-goal $search $index)
       (((Error $reason $where) (Error $reason $where))
        ($goal (ai-math:rank-for $search $index $goal $limit $options))))))

; An intermediate statement has its own features, while its source frontier
; remains explicit. Its original proof and later facts never train the query.
(= (ai-math:rank-for (AiSearch $count $facts $weights $training) $index $goal $limit $options)
   (let $search (AiSearch $count $facts $weights $training)
     (if (or (< $index 0) (> $index $count))
       (Error (AiMathGoalIndex $index) ai-math:rank-for)
       (let* (($earlier (ai-math:search-before $search $index))
                ($base (union-atom
                         (ai-math:overlap-contributions $search
                           (ai-math:declaration-symbols $goal) $index)
                         (foldl-atom $earlier () $out $fact
                           (union-atom $out
                             (ai-math:fact-background-contributions
                               $search $goal $index $fact
                               (ai-math:option $options name-weight 0.0)
                               (ai-math:option $options recency-weight 1.0))))))
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
                ($scores (ai-math:group-sums (union-atom $base (union-atom $knn $nb)))))
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
