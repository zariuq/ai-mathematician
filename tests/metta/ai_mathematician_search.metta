!(import! &self "../../phase1/library.metta")
!(import! &self (library list))
!(import! &self "../../phase1/search.metta")

(= (ai-math:search-example)
   ((Decl 0 AXIOM "base" "hb" (PROP) NoBody ("topic") () ("topic"))
    (Decl 1 THM "old" "ho" (PROP) NoBody ("topic") ("base") ("topic"))
    (Decl 2 THM "goal" "hg" (PROP) NoBody ("topic") ("private-goal-proof") ("topic"))
    (Decl 3 THM "future" "hf" (PROP) NoBody ("topic") ("base" "future-only-proof") ("poison"))))

; Overlap first meets ordinal zero through its name; statements first meet
; ordinal one. Shared traversal must preserve both orders, including ties.
(= (test:symbol-source)
   ((Decl 0 THM "a" "h0" (PROP) NoBody ("b" "b") () ())
    (Decl 1 THM "b" "h1" (PROP) NoBody ("a") () ())
    (Decl 2 THM "a" "h2" (PROP) NoBody ("a" "b") () ())))
; Blocks keep self before sorted dependency occurrences, including repeated
; names and non-associative additions. The reference retains prefix append.
(= (test:knn-from-neighbors-reference $neighbors $count)
   (ai-math:group-sums
     (foldl-atom (list:take $count $neighbors) () $out $entry
       (let ($decl $similarity) $entry
         (union-atom $out
           (cons-atom ((ai-math:declaration-name $decl) $similarity)
             (map-atom (sort-atom (ai-math:declaration-dependencies $decl)) $name
               ($name $similarity))))))))
!(test
   (let $neighbors
      (((AiSearchFact 0 THM "same" () ("z" "a" "a") ()) 1.0e16)
       ((AiSearchFact 1 THM "same" () ("a" "same") ()) 1.0)
       ((AiSearchFact 2 THM "same" () ("a" "z") ()) -1.0e16)
       ((AiSearchFact 3 THM "zero" () ("a") ()) -0.0))
     (map-atom (0 1 2 3 4 9) $count
       (let* (($original (test:knn-from-neighbors-reference $neighbors $count))
              ($blocks (ai-math:knn-from-neighbors $neighbors $count))
              ($shape ((size-atom $original)))
              ($left (tensor:encode (tensor:from-values f64 $shape
                (map-atom $original $entry (index-atom $entry 1)))))
              ($right (tensor:encode (tensor:from-values f64 $shape
                (map-atom $blocks $entry (index-atom $entry 1))))))
         (and (== $original $blocks) (== $left $right)))))
   (true true true true true true))
; Unsupported producers keep their occurrence effects and ordered choices.
(= (ai-math:declaration-name (TestVoteEffect $run $name))
   (let $_ (add-atom &self (TestVoteEvent $run Name $name)) $name))
(= (ai-math:declaration-dependencies (TestVoteEffect $run $name))
   (let $_ (add-atom &self (TestVoteEvent $run Dependencies $name)) ("a" "a")))
!(test
   (let* (($original (test:knn-from-neighbors-reference
            (((TestVoteEffect Original "left") 1.0)
             ((TestVoteEffect Original "right") 0.5)) 2))
          ($blocks (ai-math:knn-from-neighbors
            (((TestVoteEffect Blocks "left") 1.0)
             ((TestVoteEffect Blocks "right") 0.5)) 2))
          ($original-events (collapse (match &self
            (TestVoteEvent Original $kind $name) ($kind $name))))
          ($block-events (collapse (match &self
            (TestVoteEvent Blocks $kind $name) ($kind $name)))))
     ((== $original $blocks) $original-events $block-events))
   (true ((Name "left") (Dependencies "left") (Name "right") (Dependencies "right"))
         ((Name "left") (Dependencies "left") (Name "right") (Dependencies "right"))))
(= (ai-math:declaration-name (TestVoteChoice $name)) $name)
(= (ai-math:declaration-dependencies (TestVoteChoice $name))
   (superpose (("a") ("b"))))
!(test
   (let $neighbors (((TestVoteChoice "left") 1.0) ((TestVoteChoice "right") 0.5))
     (== (collapse (ai-math:knn-from-neighbors $neighbors 2))
         (collapse (test:knn-from-neighbors-reference $neighbors 2))))
   true)
; Compiled ingress and singular insertion expose the same ordered rows.
!(test
   (map-atom
     ((AiSearchFact 9 THM "a_b" ("x" "x" "a_b") () ("f" "f"))
      (AiSearchFact 17 DEF "_name__" () () ())
      (AiSearchFact 33 AXIOM "distinct" ("other") () ("g"))) $fact
     (let* (($separate (new-space)) ($bulk (new-space))
            ($original (ai-math:index-document $separate 4 $fact))
            ($inputs ((AiDocumentInput 4 $fact)))
            ($compiled (ai-math:ingest-documents $bulk $inputs)))
       (= (collapse (get-atoms $separate)) (collapse (get-atoms $bulk)))))
   (true true true))
!(test
   (let $search (ai-math:search (test:symbol-source))
     (map-atom (0 1 2 3) $cutoff
       (map-atom (() ("a") ("b" "a" "a") ("missing")) $symbols
         (== (ai-math:symbol-shared $search $symbols $cutoff)
             ((ai-math:overlap-shared $search $symbols $cutoff)
              (ai-math:statement-shared $search $symbols $cutoff))))))
   ((true true true true) (true true true true)
    (true true true true) (true true true true)))
!(test
   (let $search (ai-math:search (test:symbol-source))
     (case (ai-math:symbol-shared-attempt $search ("a" "b") 2)
       (((AiSymbols $rows)
          (let ($overlap $statement) (ai-math:symbol-shared $search ("a" "b") 2)
            ((map-atom $overlap $row (index-atom $row 0))
             (map-atom $statement $row (index-atom $row 0)))))
        ($other $other))))
   ((0 1) (1 0)))
; Mutation invalidates the snapshot, and duplicates in the new source still
; count on the authored route. Numeric query keys do not adopt string policy.
!(test
   (let* (($search (ai-math:search (test:symbol-source)))
          ((AiSearch $count $facts $weights $training) $search)
          ($added (add-atom $weights (AiOverlapSymbol "a" 0))))
     (and (== (ai-math:symbol-shared-attempt $search ("a") 2) AiSymbols:Decline)
       (== (ai-math:symbol-shared $search ("a") 2)
           ((ai-math:overlap-shared $search ("a") 2)
            (ai-math:statement-shared $search ("a") 2)))))
   true)
!(test (ai-math:symbol-shared-attempt (ai-math:search (test:symbol-source)) (1.0) 2)
   AiSymbols:Decline)

; Bulk preparation uses each fact's original sorted-key schedule. These
; weights distinguish ordered binary64 accumulation from reassociation.
(= (test:total-facts)
   ((AiSearchFact 0 AXIOM "q" ("c" "a" "b" "a") () ())
    (AiSearchFact 1 AXIOM "empty" () () ())
    (AiSearchFact 2 AXIOM "a" ("a" "b") () ())))
(= (test:total-blocks)
   ((("a" "b" "c") 0 0) (("q") 1 0) (("empty") 3 1) (("a" "b") 4 2)))
(= (test:total-weights)
   (let* (($weights (new-space))
          ($saved (add-atoms $weights
            ((AiEntry (Weight Symbol "a") 1.0e16)
             (AiEntry (Weight Symbol "b") 1.0)
             (AiEntry (Weight Symbol "c") -1.0e16)))))
     $weights))
(= (test:observe-totals $weights)
   (sort-atom (collapse (match $weights (AiEntry $key $value) ($key $value)))))
!(test
   (let* (($facts (test:total-facts)) ($packed (test:total-weights))
          ($reference (test:total-weights))
          ($prepared (ai-math:prepare-totals-attempt $packed $facts
            ((AiFeature Symbol "a") (AiFeature Symbol "b") (AiFeature Symbol "c"))
            3 (postings:prepare-blocks (test:total-blocks))))
          ($separate (foldl-atom $facts 0 $ordinal $fact
            (let $stored (ai-math:prepare-fact-totals $reference $ordinal $fact)
              (+ $ordinal 1)))))
     ($prepared (= (test:observe-totals $packed) (test:observe-totals $reference))
       (ai-math:get $packed (StatementTotal 0) Missing)
       (ai-math:get $packed (OverlapTotal 0) Missing)))
   (AiTotals:Prepared true 0.0 1.0))
; Incomplete coverage and closed handles publish no partial totals.
!(test
   (map-atom (Incomplete Closed) $mode
     (let* (($weights (test:total-weights))
            ($before (test:observe-totals $weights))
            ($table (postings:prepare-blocks ((("a") 0 0))))
            ($closed (if (== $mode Closed) (postings:close $table) ()))
            ($result (ai-math:prepare-totals-attempt $weights (test:total-facts)
              ((AiFeature Symbol "a") (AiFeature Symbol "b") (AiFeature Symbol "c"))
              3 $table)))
       ($result (= $before (test:observe-totals $weights)))))
   ((AiTotals:Decline true) (AiTotals:Decline true)))
!(test (ai-math:prepare-totals-attempt (new-space) () () 0 (postings:prepare-blocks ()))
   AiTotals:Prepared)

; Document frequencies retain repeated occurrences and separate feature kinds.
!(test
   (let* (($documents (new-space))
          ($stored (add-atoms $documents
            ((AiDocument Symbol "a" 0) (AiDocument Symbol "a" 0)
             (AiDocument Symbol "b" 0) (AiDocument Feature "a" 1))))
          ($before (_minimal-space-revision $documents))
          ($counts (ai-math:document-frequencies-attempt $documents)))
     ($counts (== $before (_minimal-space-revision $documents))))
   ((List:GroupedSums
      (((AiFeature Symbol "a") 2) ((AiFeature Symbol "b") 1)
       ((AiFeature Feature "a") 1))) true))
; Mixed numeric representations do not borrow a structural grouping policy.
!(test
   (let* (($documents (new-space))
          ($stored (add-atoms $documents
            ((AiDocument Symbol 1 0) (AiDocument Symbol 1.0 1)))))
     (ai-math:document-frequencies-attempt $documents))
   List:GroupSumsFallback)

; Positive: earlier similar statements vote for themselves and cited facts.
!(test
   (let* (($decls (ai-math:search-example)) ($search (ai-math:search $decls)))
     (ai-math:knn $search ("topic") (list:take 2 $decls) 24))
   (("old" 1.0) ("base" 1.0)))

; Positive: the three selectors produce usable premise lists.
!(test
   (ai-math:diverse-slices (ai-math:search (ai-math:search-example)) 2)
   (DiverseSlices (nb ("base" "old")) (knn ("old" "base")) (sym ("base" "old"))))

; Negative: neither the goal's own proof nor later proofs supply premises.
!(test
   (ai-math:entry-names
     (ai-math:rank (ai-math:search (ai-math:search-example)) 2))
   ("base" "old"))

; No earlier declarations means no invented candidates.
!(test (ai-math:rank (ai-math:search (ai-math:search-example)) 0) ())
!(test
   (case (ai-math:rank (ai-math:search (ai-math:search-example)) 99)
     (((Error $reason $where) BadGoal) ($other IncorrectlyAccepted)))
   BadGoal)

; Additive evidence retains repeated uses, not duplicate dictionary values.
!(test (ai-math:group-sums (("p" 1.0) ("q" 1.0) ("p" 2.0)))
       (("p" 3.0) ("q" 1.0)))

; Turning learned/recency bonuses off is an ordinary caller choice.
!(test
   (ai-math:entry-names
     (ai-math:rank-with (ai-math:search (ai-math:search-example)) 2 32
       ((nb-weight 0.0) (knn-weight 0.0) (recency-weight 0.0))))
   ("base" "old"))

; Lookup defaults and empty name tokens are explicit and harmless.
!(test (ai-math:weight (ai-math:search ()) Symbol "unknown" 1.0) 1.0)
!(test (ai-math:name-tokens "_nat__add_") ("add" "nat"))
!(test (ai-math:name-similarity (ai-math:search ()) "_" "__") 0.0)

; Reusing preparation does not consume or train on the query.
!(test
   (let $search (ai-math:search (ai-math:search-example))
     (== (ai-math:rank $search 2) (ai-math:rank $search 2)))
   true)

; The packed default aggregation has the exact authored rank observation.
(= (test:symbol-columns-source)
   ((Decl 0 DEF "named" "hd" (PROP) NoBody ("other") () ())
    (Decl 1 AXIOM "base" "ha" (PROP) NoBody ("shared") () ())
    (Decl 2 THM "a" "hb" (PROP) NoBody ("b") ("base") ())
    (Decl 3 THM "b" "hc" (PROP) NoBody ("a") ("base") ())
    (Decl 4 THM "query" "he" (PROP) NoBody ("a" "b" "named") ("a") ())))
; Numeric projections retain the statement-specific tie order and the
; definition-before-overlap scalar schedule without fetching every fact.
!(test
   (let $search (ai-math:search (test:symbol-columns-source))
     (map-atom (0 1 2 5) $cutoff
       (map-atom (() ("a" "b") ("named" "other") ("shared") ("missing")) $symbols
         (case (ai-math:rank-symbol-columns-attempt $search $symbols $cutoff)
           (((Postings:Columns $labels $values)
              (let $columns (postings:column-result $labels $values)
                (and (== (ai-math:rank-overlap-columns $search $symbols $cutoff $columns)
                         (ai-math:rank-coordinate-tensor 5
                           (ai-math:overlap-coordinate-blocks $search $symbols $cutoff)))
                  (== (ai-math:rank-neighbors-columns $search $symbols $columns 24)
                      (list:take 24 (ai-math:neighbors-prefix $search $symbols $cutoff))))))
            ($other FailedAdmission))))))
   ((true true true true true) (true true true true true)
    (true true true true true) (true true true true true)))
!(test
   (let* (($search (ai-math:search (test:symbol-columns-source)))
          ($columns (ai-math:rank-symbol-columns-attempt $search ("a" "b") 5)))
     (map-atom (0 1 24) $limit
       (== (ai-math:rank-neighbors-columns $search ("a" "b") $columns $limit)
           (list:take $limit (ai-math:neighbors-prefix $search ("a" "b") 5)))))
   (true true true))
!(test
   (map-atom (Catalog Weights) $owner
     (let* (($search (ai-math:search (test:symbol-columns-source)))
            ((AiSearch $count $facts $weights $training) $search)
            ($changed (if (== $owner Catalog)
              (add-atom $facts (AiSearchItem 10 (AiSearchFact 10 DEF "later" () () ())))
              (add-atom $weights (AiOverlapSymbol "a" 0)))))
       (ai-math:rank-symbol-columns-attempt $search ("a" "b") 4)))
   (AiSymbols:Decline AiSymbols:Decline))
!(test
   (let $search (ai-math:search (test:symbol-source))
     (ai-math:rank-symbol-columns-attempt $search ("a" "b") 2))
   AiSymbols:Decline)
!(test
   (let* (($decls (ai-math:search-example))
          ($search (ai-math:search $decls)))
     (map-atom (0 1 2 3) $index
       (let $goal (ai-math:search-goal $search $index)
         (== (ai-math:rank-packed-default $search $index $goal 32)
             (ai-math:rank-for $search $index $goal 32 ())))))
   (true true true true))

(= (test:bayes-closed-example)
   ((Decl 0 AXIOM "first" "h0" (PROP) NoBody () () ("f"))
    (Decl 1 THM "second" "h1" (PROP) NoBody () ("later" "first") ("f"))
    (Decl 2 THM "later" "h2" (PROP) NoBody () ("first") ("g"))
    (Decl 3 THM "query" "h3" (PROP) NoBody () ("second") ("f"))))
(= (test:bayes-row-signal (AiSearch $count $facts $weights $training) $index $goal)
   (let* (($search (AiSearch $count $facts $weights $training))
          ($rows (ai-math:bayes-bonuses
            (ai-math:sort-scores
              (ai-math:naive-bayes-prefix $search $goal $index 10.0 -4.0 1.0))
            3.0 8.0 0)))
     (ai-math:rank-coordinate-tensor $count
       ((ai-math:rank-coordinate-block $weights $rows)))))
; Premise introduction order is not catalog order. Admission is checked
; explicitly, then tensor equality compares support and scalar bits.
!(test
   (let $search (ai-math:search (test:bayes-closed-example))
     (map-atom (0 1 2 3) $index
       (let* (($goal (ai-math:search-goal $search $index))
              ($scores (ai-math:rank-bayes-tensor $search $index $goal)))
         (case (tensor:dtype $scores)
           ((f64
              (== $scores (test:bayes-row-signal $search $index $goal)))
            ($other FailedAdmission))))))
   (true true true true))
; Independent row materialization preserves sparse gaps and input-position
; ties before an arbitrary injective renaming into catalog coordinates.
(= (test:bayes-score-row-reference $size $scores $mapping)
   (let* (((TensorData f64 $shape $entries) (tensor:inspect $scores))
          ($ranked (ai-math:bayes-bonuses (ai-math:sort-scores $entries) 3.0 8.0 0))
          ($rows (map-atom $ranked $entry
            (let ($ordinal $bonus) $entry ((index-atom $mapping $ordinal) $bonus)))))
     (tensor:from-coo f64 ($size) (list:group-sums-number-blocks ($rows)) reject)))
!(test
   (let* (($mapping (6 0 4 2 1))
          ($renaming (tensor:from-values index (5) $mapping))
          ($positions (tensor:from-values i64 (5) (0 1 2 3 4))))
     (map-atom (() ((0 -0.0) (2 1.0) (4 1.0))
                  ((1 0.0) (3 -0.0)) ((0 -4.0) (1 -4.0) (4 -8.0))) $entries
       (let* (($scores (tensor:from-coo f64 (5) $entries reject))
              ($result (ai-math:rank-bayes-from-scores 7 $scores $renaming $positions)))
         (case (tensor:dtype $result)
           ((f64
              (== $result (test:bayes-score-row-reference 7 $scores $mapping)))
            ($other FailedAdmission))))))
   (true true true true))
; Unknown names and noninjective catalog identities cannot use the renaming.
!(test
   (let* (($unknown (ai-math:search-example))
          ($closed (test:bayes-closed-example))
          ($duplicate (cons-atom (car-atom $closed) $closed)))
     (map-atom ($unknown $duplicate) $decls
       (let* (($search (ai-math:search $decls))
              ($goal (ai-math:search-goal $search 2)))
         (ai-math:rank-bayes-tensor $search 2 $goal))))
   (AiRank:Decline AiRank:Decline))
!(test
   (let* (($search (ai-math:search (test:bayes-closed-example)))
          ((AiSearch $count $facts $weights $training) $search)
          ($aliased (add-atom $weights (AiNameOrder "later" 0))))
     (ai-math:prepare-bayes-rank-plan $weights $training))
   NoBayesRankPlan)
!(test
   (map-atom (Weights Training) $owner
     (let* (($search (ai-math:search (test:bayes-closed-example)))
            ((AiSearch $count $facts $weights (AiTraining $training $revision $prefixes)) $search)
            ($goal (ai-math:search-goal $search 2))
            ($before (case (tensor:dtype (ai-math:rank-bayes-tensor $search 2 $goal))
              ((f64 Admitted) ($other FailedAdmission))))
            ($changed (if (== $owner Weights)
              (add-atom $weights (AiNameOrder "alias" 0))
              (add-atom $training (AiTrainingFeature 0 "f" 100 0 Citation)))))
       ($before (ai-math:rank-bayes-tensor $search 2 $goal))))
   ((Admitted AiRank:Decline) (Admitted AiRank:Decline)))
; A changed fact catalog invalidates the packed coordinate plan. The public
; default then runs the current authored rank rather than reusing stale rows.
!(test
   (let* (($search (ai-math:search (ai-math:search-example)))
          ((AiSearch $count $facts $weights $training) $search)
          ($changed (add-atom $facts
            (AiSearchItem 99 (AiSearchFact 99 DEF "later" () () ()))))
          ($goal (ai-math:search-goal $search 2))
          ($declined (case (ai-math:rank-packed-attempt $search 2 $goal 32)
            ((AiRank:Decline true) ($other false)))))
     (and $declined
       (== (ai-math:rank $search 2)
           (ai-math:rank-for $search 2 $goal 32 ()))))
   true)
!(test
   (let* (($search (ai-math:search (ai-math:search-example)))
          ((AiSearch $count $facts $weights $training) $search)
          ($changed (add-atom $weights (AiNameOrder "later-alias" 0)))
          ($goal (ai-math:search-goal $search 2))
          ($declined (case (ai-math:rank-packed-attempt $search 2 $goal 32)
            ((AiRank:Decline true) ($other false)))))
     (and $declined
       (== (ai-math:rank $search 2)
           (ai-math:rank-for $search 2 $goal 32 ()))))
   true)

!(test
   (ai-math:evaluate-recall () (8))
   (RecallSummary 0 ((RecallAt 8 (Mean NoTheorems) (Complete 0 NoTheorems)))))

; Prepared prefixes equal independent subset preparation, including non-unit
; self weights and reverse query order. Queries leave evidence unchanged;
; the derived prefix cache may acquire newly requested feature columns.
!(test
   (let* (($decls (ai-math:search-example)) ($search (ai-math:search $decls)))
     (map-atom (3 2 0 1 2) $index
       (let $goal (index-atom $decls $index)
         (== (ai-math:naive-bayes-prefix $search $goal $index 3.0 -2.5 0.1)
             (ai-math:naive-bayes $search $goal (list:take $index $decls) 3.0 -2.5 0.1)))))
   (true true true true true))

; Negative: later evidence for an existing premise cannot affect a prefix's
; counts, even if that premise has already been introduced.
!(test
   (let* (($decls (ai-math:search-example)) ($search (ai-math:search $decls))
          ($goal (index-atom $decls 2)))
     (ai-math:entry-names (ai-math:naive-bayes-prefix $search $goal 2 10.0 -4.0 1.0)))
   ("base" "old"))

; Strings never become executable symbols. Repeated examples count as
; separate evidence, and first introduction decides equal-score order.
(= (ai-math:repeated-training-example)
   ((Decl 0 AXIOM "Empty" "ha" (PROP) NoBody () () ("Empty"))
    (Decl 1 THM "same" "hb" (PROP) NoBody () ("Empty") ("Empty"))
    (Decl 2 THM "same" "hc" (PROP) NoBody () ("Empty") ("Empty"))
    (Decl 3 THM "query" "hd" (PROP) NoBody () ("future-secret") ("Empty"))))
; Bulk preparation retains the complete source sequence, not just counts.
!(test
   (map-atom
     (()
      ((AiSearchFact 7 DEF "unused" () ("ignored") ()))
      ((AiSearchFact 9 AXIOM "base" () () ("f" "f"))
       (AiSearchFact 17 THM "same" () ("future" "base" "base") ("f"))
       (AiSearchFact 22 DEF "skip" () ("ignored") ())
       (AiSearchFact 33 THM "same" () ("base" "future") ("g")))
      ((AiSearchFact 4 AXIOM 1 () () ("f"))
       (AiSearchFact 8 THM 1.0 () (1 1.0) ("g")))) $facts
     (let* (((AiTraining $bulk $br $bp) (ai-math:training $facts))
            ((AiTraining $single $sr $sp) (ai-math:training-reference $facts)))
       (== (collapse (get-atoms $bulk)) (collapse (get-atoms $single)))))
   (true true true true))
!(test
   (let* (($decls (ai-math:repeated-training-example))
          ($search (ai-math:search $decls))
          ($goal (ai-math:search-goal $search 3))
          ($declined (case (ai-math:rank-packed-attempt $search 3 $goal 32)
            ((AiRank:Decline true) ($other false)))))
     (and $declined
       (and (== (ai-math:rank $search 3)
                (ai-math:rank-for $search 3 $goal 32 ()))
            (== (ai-math:rank $search 3 0) ()))))
   true)
!(test
   (let* (($decls (ai-math:repeated-training-example)) ($search (ai-math:search $decls)))
     (ai-math:entry-names
       (ai-math:sort-scores (ai-math:naive-bayes-prefix $search
         (index-atom $decls 3) 3 10.0 -4.0 1.0))))
   ("Empty" "same"))
!(test
   (let* (($decls (ai-math:repeated-training-example)) ($search (ai-math:search $decls)))
     (== (ai-math:naive-bayes-prefix $search (index-atom $decls 3) 3 10.0 -4.0 0.5)
         (ai-math:naive-bayes $search (index-atom $decls 3) (list:take 3 $decls) 10.0 -4.0 0.5)))
   true)

; Base events live once in the tagged source relation. Explicit use, feature,
; or posting overlays mutate that same revision and invalidate its snapshot.
!(test
   (let* (($search (ai-math:search (ai-math:search-example)))
          ((AiSearch $n $facts $weights (AiTraining $source $rev $prefixes)) $search)
          ($base (match $source (AiTrainingPremise "base" $premise) $premise)))
     (and (> (size-atom (collapse (match $source
                   (AiTrainingPostingBlock $features $name $premise $event $origin $role)
                   $event))) 0)
       (and (== (collapse (match $source
                    (AiTrainingPosting $feature $name $premise $event $origin $role)
                    $event)) ())
         (and (== (collapse (match $source
                    (AiTrainingFeature $premise $feature $event $origin $role)
                    $event)) ())
           (== (collapse (match $source
                    (AiTrainingUse $premise $event $origin $role)
                    $event)) ())))))
   true)
!(test
   (let* (($search (ai-math:search (ai-math:search-example)))
          ((AiSearch $n $facts $weights (AiTraining $source $rev $prefixes)) $search))
     (== (ai-math:training-posting-counts-prepared $source $prefixes "topic" 2)
         (ai-math:training-posting-counts $source "topic" 2)))
   true)
!(test
   (let* (($search (ai-math:search (ai-math:search-example)))
          ((AiSearch $n $facts $weights (AiTraining $source $rev $prefixes)) $search)
          ($old (ai-math:training-posting-counts-prepared $source $prefixes "topic" 2))
          ($added (add-atom $source (AiTrainingPosting "topic" "base" 0 100 1 Citation)))
          ($current (if (== $rev (_minimal-space-revision $source)) $prefixes NoPrefix)))
     (and (not (== $current $prefixes))
       (== (ai-math:training-posting-counts-prepared $source $current "topic" 2)
           (ai-math:training-posting-counts $source "topic" 2))))
   true)
!(test
   (let* (($search (ai-math:search (ai-math:search-example)))
          ((AiSearch $n $facts $weights (AiTraining $source $rev $prefixes)) $search)
          ($candidate (match $source (AiTrainingCandidate "base" $first $event $premise)
                              ($event $first "base" $premise)))
          (($event $first $name $premise) $candidate)
          ($added (add-atom $source
                    (AiTrainingUse $premise 100 1 Citation)))
          ($current (if (== $rev (_minimal-space-revision $source))
                      $prefixes NoPrefix)))
     (and (== $current NoPrefix)
       (== (ai-math:bayes-unit-summary $source $candidate 2 $current)
           (ai-math:bayes-unit-summary $source $candidate 2 NoPrefix))))
   true)

; Packed snapshots must reject every source change, including feature-only
; changes for premises beyond the currently requested prefix.
; The ordinary dense replay then observes the actual current evidence.
(= (test:packed-snapshot-mutation $name $event)
   (let* (($search (ai-math:search (ai-math:search-example)))
          ((AiSearch $n $facts $weights (AiTraining $source $revision $prefixes)) $search)
          ($candidates (sort-atom (filter-atom
            (collapse (match $source
              (AiTrainingCandidate $candidate $first $ordinal $premise)
              ($ordinal $first $candidate $premise)))
            $entry (< (index-atom $entry 1) 2))))
          ($before (ai-math:bayes-unit-packed $source
                      (("topic" 1.0)) 2 10.0 -4.0 $prefixes))
          ($premise (match $source (AiTrainingPremise $name $id) $id))
          ($changed (case $event
            (((TestTrainingFeature $feature $ordinal $origin $role)
               (add-atom $source
                 (AiTrainingFeature $premise $feature $ordinal $origin $role)))
             ((TestTrainingUse $ordinal $origin $role)
               (add-atom $source
                 (AiTrainingUse $premise $ordinal $origin $role)))))))
     (SnapshotMutation
       (case $before (((AiBayes:Packed $rows) Packed) ($other FailedAdmission)))
       (ai-math:bayes-unit-packed $source (("topic" 1.0)) 2 10.0 -4.0 $prefixes)
       (== (ai-math:bayes-unit-sparse $source (("topic" 1.0)) 2 10.0 -4.0 $prefixes)
           (ai-math:bayes-unit $source $candidates (("topic" 1.0)) 2 10.0 -4.0)))))
!(test (test:packed-snapshot-mutation "base" (TestTrainingFeature "topic" 100 1 Citation))
       (SnapshotMutation Packed AiBayes:Stale true))
!(test (test:packed-snapshot-mutation "future" (TestTrainingFeature "topic" 100 3 Self))
       (SnapshotMutation Packed AiBayes:Stale true))
!(test (test:packed-snapshot-mutation "base" (TestTrainingUse 100 1 Citation))
       (SnapshotMutation Packed AiBayes:Stale true))

; A non-prefix subset is deliberately different from the corpus prefix.
!(test
   (let* (($decls (ai-math:search-example)) ($search (ai-math:search $decls)))
     (ai-math:entry-names (ai-math:naive-bayes $search (index-atom $decls 2)
       ((index-atom $decls 1)) 10.0 -4.0 1.0)))
   ("old" "base"))

; Stored declaration ordinals, not caller-supplied indices, define prefixes.
!(test
   (let* (($decls
            ((Decl 20 AXIOM "first" "hf" (PROP) NoBody () () ("f"))
             (Decl 10 THM "second" "hs" (PROP) NoBody () ("first") ("f"))
             (Decl 99 THM "goal" "hg" (PROP) NoBody () ("not-earlier") ("f"))))
          ($search (ai-math:search $decls)))
     (ai-math:entry-names (ai-math:naive-bayes-prefix $search
       (ai-math:search-goal $search 2) 2 10.0 -4.0 1.0)))
   ("first" "second"))

; Independent append-accumulator reference for the ordered block observer.
; Empty rows, definition-before-overlap order and repeated names are retained.
(= (test:overlap-append-reference $search $goal-symbols $cutoff)
   (foldl-atom (ai-math:overlap-rows $search $goal-symbols $cutoff) () $out $row
     (let (AiOverlapScore $ordinal $fact $score) $row
       (let* (($name (ai-math:declaration-name $fact))
              ($shared (if (> $score 0.0) (($name $score)) ()))
              ($definition
                (if (and (== (ai-math:declaration-kind $fact) DEF)
                         (ai-math:contains $goal-symbols $name))
                  (($name 2.0)) ())))
         (union-atom $out (union-atom $definition $shared))))))
!(test
   (let* (($decls
            ((Decl 0 DEF "topic" "hd" (PROP) NoBody ("x") () ())
             (Decl 1 AXIOM "Empty" "ha" (PROP) NoBody ("topic") () ())
             (Decl 2 THM "Empty" "ht" (PROP) NoBody ("x") () ())))
          ($search (ai-math:search $decls)))
     (map-atom (0 1 2 3) $cutoff
       (map-atom (() ("topic") ("topic" "x") ("unknown")) $symbols
         (== (ai-math:overlap-contributions $search $symbols $cutoff)
             (test:overlap-append-reference $search $symbols $cutoff)))))
   ((true true true true) (true true true true)
    (true true true true) (true true true true)))
!(test
   (let $search (ai-math:search (ai-math:repeated-training-example))
     (== (ai-math:overlap-contributions $search ("Empty" "same") 3)
         (test:overlap-append-reference $search ("Empty" "same") 3)))
   true)

; Eligibility and tie decoration share a live lookup. Ineligible payloads
; must not be interpreted as scores, and a later call sees changed metadata.
!(test
   (let* (($order (new-space))
          ($first (add-atom $order (AiNameOrder "later" 2)))
          ($second (add-atom $order (AiNameOrder "earlier" 1)))
          ($older (add-atom $order (AiNameOrder "earlier" 0))))
     (ai-math:sort-scores-with-order $order 2
       (("later" unrecognized-score) ("unknown" unrecognized-score)
        ("earlier" 1.0) ("earlier" 2.0))))
   (("earlier" 2.0) ("earlier" 1.0)))
!(test
   (let* (($order (new-space))
          ($first (add-atom $order (AiNameOrder "a" 0)))
          ($second (add-atom $order (AiNameOrder "b" 1)))
          ($before (ai-math:sort-scores-with-order $order 2 (("b" 1.0) ("a" 1.0))))
          ($changed (add-atom $order (AiNameOrder "b" -1)))
          ($after (ai-math:sort-scores-with-order $order 2 (("b" 1.0) ("a" 1.0)))))
     (BeforeAfter $before $after))
   (BeforeAfter (("a" 1.0) ("b" 1.0)) (("b" 1.0) ("a" 1.0))))
