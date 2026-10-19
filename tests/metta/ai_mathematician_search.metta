!(import! &self "../../phase1/library.metta")
!(import! &self (library list))
!(import! &self "../../phase1/search.metta")

(= (ai-math:search-example)
   ((Decl 0 AXIOM "base" "hb" (PROP) NoBody ("topic") () ("topic"))
    (Decl 1 THM "old" "ho" (PROP) NoBody ("topic") ("base") ("topic"))
    (Decl 2 THM "goal" "hg" (PROP) NoBody ("topic") ("private-goal-proof") ("topic"))
    (Decl 3 THM "future" "hf" (PROP) NoBody ("topic") ("base" "future-only-proof") ("poison"))))

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

!(test
   (ai-math:evaluate-recall () (8))
   (RecallSummary 0 ((RecallAt 8 (Mean NoTheorems) (Complete 0 NoTheorems)))))

; Prepared prefixes equal independent subset preparation, including non-unit
; self weights and reverse query order. Querying does not mutate training.
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
