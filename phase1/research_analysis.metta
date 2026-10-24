; Diagnostics inspect source proofs or solver advice, not proof certificates.
(= (ai-math:research-term-size $term)
   (if (== (get-metatype $term) Expression)
     (+ 1 (foldl-atom $term 0 $n $child (+ $n (ai-math:research-term-size $child)))) 1))
(= (ai-math:research-subterms $term)
   (if (== (get-metatype $term) Expression)
     (if (== $term ()) ()
       (cons-atom $term (ai-math:research-concat
         (map-atom $term $child (ai-math:research-subterms $child))))) ()))
(= (ai-math:research-witnesses $term)
   (if (== (get-metatype $term) Expression)
     (if (== $term ()) ()
       (union-atom (if (and (== (car-atom $term) PTMAP) (>= (size-atom $term) 3))
                     ((index-atom $term 2)) ())
         (ai-math:research-concat (map-atom $term $child (ai-math:research-witnesses $child))))) ()))
(= (ai-math:research-counts $keys)
   (let* (($counts (new-space))
          ($seen (foldl-atom $keys () $names $key
            (let $put (ai-math:put $counts $key (+ 1 (ai-math:get $counts $key 0)))
              (if (ai-math:contains $names $key) $names (cons-atom $key $names))))))
     (map-atom (sort-atom $seen) $key ($key (ai-math:get $counts $key 0)))))
(= (ai-math:witness-classify $declaration)
   (let* (($statement (index-atom $declaration 5))
          ($body (index-atom $declaration 6))
          ($args (ai-math:research-witnesses $body))
          ($subterms (ai-math:research-subterms $statement))
          ($classes (map-atom $args $term
            (let $tag (if (== (get-metatype $term) Expression) (car-atom $term) $term)
              (if (and (ai-math:contains (DB TPVAR TMH PRIM HYP KNOWN PROP SET) $tag)
                       (if (== (get-metatype $term) Expression) (<= (size-atom $term) 2) true)) atomic
                (if (ai-math:contains $subterms $term) in-goal synthesized)))))
          ($largest (foldl-atom $args 0 $n $arg
            (let $size (ai-math:research-term-size $arg) (if (> $size $n) $size $n)))))
     (AiWitness:Analysis (ai-math:research-counts $classes) $largest
       (if (== $body NoBody) 0 (ai-math:research-term-size $body)))))
(= (ai-math:proof-first-order-rules)
   (file introduced negated_conjecture rectify flattening ennf_transformation nnf_transformation
    cnf_transformation skolemisation resolution subsumption_resolution forward_subsumption_resolution
    backward_subsumption_resolution superposition forward_demodulation backward_demodulation demodulation
    equality_resolution equality_factoring factoring trivial_inequality_removal duplicate_literal_removal
    avatar_definition avatar_component_clause avatar_split_clause avatar_contradiction_clause avatar_sat_refutation
    sat_conversion rat definition_unfolding definition_folding evaluation unused_predicate_definition_removal pure_predicate_removal))
(= (ai-math:proof-profile (AiATP:ProofDAG $steps))
   (let* (($rules (map-atom $steps $step (ai-math:proof-name (index-atom $step 5))))
          ($counts (ai-math:research-counts $rules))
          ($hol (sort-atom (unique-atom (filter-atom $rules $rule
                  (not (ai-math:contains (ai-math:proof-first-order-rules) $rule)))))))
     (AiProofProfile (size-atom $steps) $counts $hol)))
(= (ai-math:proof-profile-report $report)
   (let* (($summary (ai-math:atp-summary $report))
          ($dag (case $report
            (((AiATP:Report $s $p $d $r $o $e $payloads) (ai-math:proof-report-dag $payloads))
             ($other (AiATP:ProofRequest no-report $other))))))
     (AiResearch:RuleProfile $summary
       (case $dag
         (((AiATP:ProofDAG $steps) (ai-math:proof-profile $dag))
          ($other (case $report
            (((AiATP:Report $s $p $d $r $o $envelope $payloads)
              (ai-math:proof-lexical-profile $envelope $other))
             ($missing $other)))))))))
; Some producer formulas are outside the strict reader's language. Count
; their printed rule annotations for diagnostics, retaining the parse refusal.
; This fallback is not a parsed DAG and cannot authorize reconstruction.
(= (ai-math:proof-record-lines $body)
   (let (AiRuleScan $current $records)
     (foldl-atom (str:split "\n" $body) (AiRuleScan () ()) $state $line
       (let (AiRuleScan $current $records) $state
         (if (str:starts-with $line "%") $state
           (if (or (str:starts-with $line "thf(") (or (str:starts-with $line "tff(")
                 (or (str:starts-with $line "fof(") (str:starts-with $line "cnf("))))
             (AiRuleScan ($line) (if (== $current ()) $records
               (cons-atom (str:join "\n" (list:reverse $current)) $records)))
             (if (== $current ()) $state (AiRuleScan (cons-atom $line $current) $records))))))
     (list:reverse (if (== $current ()) $records
       (cons-atom (str:join "\n" (list:reverse $current)) $records)))))
(= (ai-math:proof-lexical-rule $record $inference $file $introduced)
   (let $text (str:trim $record)
     (if (str:ends-with $text ").")
       (let $inner (str:byte-slice $text 0 (- (str:byte-length $text) 2))
         (case (re:find $inference $inner)
           (((re:match $a $b $captures)
             ((str:string->symbol (str:trim (re:group-text (re:match $a $b $captures) $inner 1)))))
            ($other (case (re:find $file $inner)
              (((re:match $a $b $captures) (file))
               ($missing (case (re:find $introduced $inner)
                 (((re:match $a $b $captures) (introduced)) ($absent ())))))))))) ())))
(= (ai-math:proof-lexical-profile $envelope $refusal)
   (let* (($inference (re:prepare (re:pattern "(?s)inference\\(\\s*([^,\\[]+?)\\s*,\\s*\\[[^\\]]*\\]\\s*,\\s*\\[([^\\]]*)\\]\\s*\\)\\s*$")))
          ($file (re:prepare (re:pattern "(?s)file\\(\\s*'[^']*'\\s*,\\s*'?([^'\\),]+)'?\\s*\\)\\s*$")))
          ($introduced (re:prepare (re:pattern "introduced\\(\\s*(\\w+)\\s*,")))
          ($blocks (filter-atom (tptp:szs-data $envelope) $block
            (ai-math:contains ("Proof" "Refutation" "CNFRefutation") (index-atom $block 1))))
          ($rules (ai-math:research-concat (map-atom $blocks $block
            (ai-math:research-concat (map-atom (ai-math:proof-record-lines (index-atom $block 2)) $record
              (ai-math:proof-lexical-rule $record $inference $file $introduced))))))
          ($summary (AiProofProfile (size-atom $rules) (ai-math:research-counts $rules)
            (sort-atom (unique-atom (filter-atom $rules $rule
              (not (ai-math:contains (ai-math:proof-first-order-rules) $rule))))))))
     (AiResearch:LexicalRuleProfile $summary $refusal)))
(= (ai-math:oracle-premise-advice (AiProver $search $thf $itp $vampire $policy) $declaration $options)
   (let* (($name (ai-math:declaration-name $declaration))
          ($premises (sort-atom (ai-math:declaration-dependencies $declaration)))
          ($index (ai-math:declaration-index $declaration))
          ($problem (ai-math:thf-problem $thf $index $premises (ai-math:option $options definition-depth 3)))
          ($report (ai-math:vampire $thf $problem $vampire (ai-math:option $options seconds 30))))
     (AiOracle:Premises $name $premises (ai-math:atp-summary $report) $report)))
(= (ai-math:recall-report $rows $cutoffs)
   (let $samples (map-atom $rows $row
          (let ($ranked $truth) $row
            (map-atom $cutoffs $k
              (let $hits (size-atom (intersection-atom (list:take $k $ranked) $truth))
                (AiRecall $k (if (== $truth ()) 1.0 (/ $hits (size-atom $truth)))
                  (if (== $hits (size-atom $truth)) 1 0))))))
     (RecallSummary (size-atom $rows) (ai-math:recall-columns $samples $cutoffs 0))))
