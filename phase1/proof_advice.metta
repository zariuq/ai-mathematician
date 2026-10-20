; Structural TSTP advice through the shared, strict TPTP reader. A source
; DAG describes the solver's claims; it does not certify an inference.
; Import the normal ATP/search/prover APIs before calling these functions.

(= (ai-math:proof-name $name)
   (if (== (get-type $name) String) (str:string->symbol $name) $name))
(= (ai-math:proof-parents $parents)
   (if (list:is-list $parents)
     (let $items (list:to-expression $parents)
       (if (foldl-atom $items true $ok $parent
             (and $ok (or (== (get-metatype $parent) Symbol)
                       (or (== (get-type $parent) String) (== (get-type $parent) Number)))))
         (AiATP:Parents (map-atom $items $parent (ai-math:proof-name $parent)))
         (AiATP:ProofRequest parent-annotation $parents)))
     (AiATP:ProofRequest parent-list $parents)))
(= (ai-math:proof-source $source)
   (case $source
     (((TPTP:RecordSource (file $path $name))
       (AiATP:ProofSource file () (AiATP:Input (ai-math:proof-name $name))))
      ((TPTP:RecordSource (inference $rule $information $parents))
       (case (ai-math:proof-parents $parents)
         (((AiATP:Parents $names) (AiATP:ProofSource $rule $names AiATP:Derived))
          ($other $other))))
      ((TPTP:RecordSource (introduced $rule $information))
       (AiATP:ProofSource introduced () (AiATP:Introduced $rule)))
      ((TPTP:RecordSource (introduced $rule $information $details))
       (AiATP:ProofSource introduced () (AiATP:Introduced $rule)))
      ((TPTP:NoSource) (AiATP:ProofSource unspecified () AiATP:Unspecified))
      ($other (AiATP:ProofRequest source $other)))))
(= (ai-math:proof-step $record)
   (case ((tptp:record-name $record) (tptp:record-role $record)
          (tptp:record-formula $record) (ai-math:proof-source (tptp:record-source $record)))
     ((((TPTP:RecordName $id) (TPTP:RecordRole $role)
        (TPTP:RecordFormula $formula) (AiATP:ProofSource $rule $parents $origin))
       (AiATP:ProofStep (ai-math:proof-name $id) (tptp:record-family $record)
         $role $formula $rule $parents $origin))
      ($other (AiATP:ProofRequest record $record)))))
(= (ai-math:proof-add $seen $state $record)
   (case $state
     (((AiATP:ProofDAG $steps)
       (case (ai-math:proof-step $record)
         (((AiATP:ProofStep $id $family $role $formula $rule $parents $origin)
           (if (not (== (ai-math:get $seen $id AiMissing) AiMissing))
             (AiATP:ProofRequest duplicate-step $id)
             (let $stored (ai-math:put $seen $id (AiATP:ProofNode $parents))
               (AiATP:ProofDAG (cons-atom
                 (AiATP:ProofStep $id $family $role $formula $rule $parents $origin) $steps)))))
          ($other $other))))
      ($other $other))))
; Source order is presentation, not a dependency restriction. Index the whole
; graph, then use an explicit DFS worklist to check edges and acyclicity.
; Duplicate edges remain in the original steps; visitation is only a cache.
(= (ai-math:proof-walk $nodes $colors $work)
   (if (== $work ()) AiATP:ProofGraphOK
     (let ($entry $rest) (decons-atom $work)
       (case $entry
         (((AiATP:Leave $id)
           (let $stored (ai-math:put $colors $id AiATP:Black)
             (ai-math:proof-walk $nodes $colors $rest)))
          ((AiATP:Enter $id)
           (ai-math:proof-enter $nodes $colors $id $rest)))))))
(= (ai-math:proof-enter $nodes $colors $id $rest)
   (case (ai-math:get $colors $id AiATP:White)
     ((AiATP:Black (ai-math:proof-walk $nodes $colors $rest))
      (AiATP:Gray (AiATP:ProofRequest dependency-cycle $id))
      (AiATP:White
       (let (AiATP:ProofNode $parents) (ai-math:get $nodes $id AiMissing)
         (ai-math:proof-visit $nodes $colors $id $parents $rest))))))
(= (ai-math:proof-visit $nodes $colors $id $parents $rest)
   (let $missing (filter-atom $parents $parent
                    (== (ai-math:get $nodes $parent AiMissing) AiMissing))
     (if (not (== $missing ()))
       (AiATP:ProofRequest missing-predecessors ($id $missing))
       (let $stored (ai-math:put $colors $id AiATP:Gray)
         (ai-math:proof-walk $nodes $colors
           (union-atom (map-atom $parents $parent (AiATP:Enter $parent))
             (cons-atom (AiATP:Leave $id) $rest)))))))
(= (ai-math:proof-dag $records)
   (if (list:is-list $records)
     (let* (($seen (new-space))
            ($result (foldl-atom $records (AiATP:ProofDAG ()) $state $record
                       (ai-math:proof-add $seen $state $record))))
       (case $result
         (((AiATP:ProofDAG $steps)
           (let* (($ordered (list:reverse $steps)) ($colors (new-space))
                  ($checked (ai-math:proof-walk $seen $colors
                              (map-atom $ordered $step (AiATP:Enter (index-atom $step 1))))))
             (if (== $checked AiATP:ProofGraphOK) (AiATP:ProofDAG $ordered) $checked)))
          ($other $other))))
     (AiATP:ProofRequest records $records)))

; Display records retain formulas and dependency edges, but not producer file
; paths or arbitrary useful-info annotations. The unmodified parsed records
; remain in the report. Do not silently splice or renumber inference edges.
(= (ai-math:proof-display-record
      (AiATP:ProofStep $id $family $role $formula $rule $parents $origin))
   (case $origin
     (((AiATP:Input $name) ($family $id $role $formula (file "problem" $name)))
      (AiATP:Derived ($family $id $role $formula
        (inference $rule (list:from-expression ()) (list:from-expression $parents))))
      ((AiATP:Introduced $name) ($family $id $role $formula))
      (AiATP:Unspecified ($family $id $role $formula)))))
(= (ai-math:proof-lines (AiTHF $count $index (AiTHF:Formats $reader $printer))
      (AiATP:ProofDAG $steps))
   (map-atom $steps $step
     (tptp:print-records-with $printer ((ai-math:proof-display-record $step)))))
(= (ai-math:proof-take-lines $lines $limit)
   (let (AiATP:TextSize $size $kept $finished)
     (foldl-atom $lines (AiATP:TextSize 0 () false) $state $line
       (let (AiATP:TextSize $size $kept $finished) $state
         (if $finished $state
           (let $next (+ $size (str:codepoint-count $line))
             (if (> $next $limit) (AiATP:TextSize $size $kept true)
               (AiATP:TextSize $next (cons-atom $line $kept) false))))))
     (list:reverse $kept)))
(= (ai-math:proof-display $context $dag $limit)
   (let $lines (ai-math:proof-lines $context $dag)
     (if (not (foldl-atom $lines true $ok $line (and $ok (== (get-type $line) String))))
       (AiATP:ProofRequest printing $lines)
       (let $size (foldl-atom $lines 0 $total $line (+ $total (str:codepoint-count $line)))
         (if (or (== $limit 0) (<= $size $limit)) (str:join "" $lines)
           (let* (($head (ai-math:proof-take-lines $lines (/ $limit 3)))
                  ($head-size (foldl-atom $head 0 $total $line (+ $total (str:codepoint-count $line))))
                  ($tail (list:reverse (ai-math:proof-take-lines (list:reverse $lines) (- $limit $head-size)))))
             (str:join "" (union-atom $head
               (cons-atom "% ... middle records omitted for display ...\n" $tail)))))))))
(= (ai-math:proof-report-dag $payloads)
   (if (== $payloads ()) (AiATP:ProofRequest absent-proof ())
     (let $records (ai-math:vampire-payload-records (car-atom $payloads))
       (if (or (== $records ()) (not (list:is-list $records)))
         (ai-math:proof-report-dag (cdr-atom $payloads))
         (ai-math:proof-dag $records)))))
(= (ai-math:proof-symbols $term)
   (if (== (get-metatype $term) Symbol) ($term)
     (if (list:is-list $term)
       (foldl-atom $term () $out $child (union-atom $out (ai-math:proof-symbols $child))) ())))
(= (ai-math:proof-display-name $context $target-index $id)
   (let* (($text (str:symbol->string $id))
          ($definition (str:ends-with $text "_def"))
          ($base (if $definition (str:byte-slice $text 0 (- (str:byte-length $text) 4)) $text)))
     (if (str:starts-with $base "c_")
       (let $ordinal (str:string->number (str:byte-slice $base 2 (str:byte-length $base)))
         (if (ai-math:itp-natural $ordinal)
           (if (== (ai-math:thf-id $ordinal) (str:string->symbol $base))
             (ai-math:proof-display-ordinal $context $target-index $text $ordinal $definition) ()) ())) ())))
(= (ai-math:proof-display-ordinal $context $target-index $text $ordinal $definition)
   (case (ai-math:thf-lookup $context Ordinal $ordinal)
     (((AiTHF:Fact $i $kind $name $stmt $body)
       (if (and (< $i $target-index) (or (not $definition) (== $kind DEF)))
         ((str:join "" ($text " = " $name (if $definition "_def" "")))) ()))
      ($other ()))))
(= (ai-math:proof-legend $context $target-index (AiATP:ProofDAG $steps))
   (let $symbols (sort-atom (unique-atom (foldl-atom $steps () $out $step
                    (let (AiATP:ProofStep $id $family $role $formula $rule $parents $origin) $step
                      (union-atom $out (union-atom (ai-math:proof-symbols $formula)
                        (case $origin (((AiATP:Input $name) ($name)) ($other ())))))))))
     (foldl-atom $symbols () $out $symbol
       (union-atom $out (ai-math:proof-display-name $context $target-index $symbol)))))
(= (ai-math:proof-guidance $context $goal-index $dag $limit)
   (let* (($legend (map-atom (ai-math:proof-legend $context $goal-index $dag) $line
                    (str:concat $line "\n")))
          ($shown (if (== $limit 0) $legend (ai-math:proof-take-lines $legend (/ $limit 3))))
          ($legend-size (foldl-atom $shown 0 $total $line (+ $total (str:codepoint-count $line))))
          ($body (ai-math:proof-display $context $dag
                   (if (== $limit 0) 0 (- $limit $legend-size)))))
     (if (== (get-type $body) String)
       (str:join "\n" ("Untrusted Vampire refutation advice, not a checked Lean proof."
         "Vampire assumes the negated goal and derives false. Inference parent IDs describe the solver's argument."
         "Only earlier library facts may be used. Reconstruct a direct Lean proof; the independent checker remains authoritative."
         "Identifiers (a _def suffix denotes a definition):"
         (str:join "" $shown)
         (if (== $shown $legend) "" "% ... additional identifier mappings omitted ...")
         "TPTP inference records:" $body)) $body)))
(= (ai-math:proof-advice-slices $context $name $index $ranked $slices $vampire $seconds $depth $limit $trace)
   (if (== $slices ()) (AiATP:ProofUnavailable (list:reverse $trace))
     (let* (($k (car-atom $slices))
            ($problem (ai-math:thf-problem $context $index (list:take $k $ranked) $depth)))
       (case $problem
         (((AiTHF:Problem $records $ids $skipped $unexpanded)
           (let* (($report (ai-math:vampire $context $problem $vampire $seconds))
                  ($summary (ai-math:atp-summary $report)))
             (case $summary
               (((AiATP:Advice "Theorem" $premises $definitions)
                 (let $dag (ai-math:proof-report-dag (index-atom $report 7))
                   (case $dag
                     (((AiATP:ProofDAG $steps)
                       (let $text (ai-math:proof-guidance $context $index $dag $limit)
                         (if (== (get-type $text) String)
                           (AiATP:ProofAdvice $name $k $text $premises $definitions
                             (AiATP:ProofEvidence $problem $report $dag))
                           $text)))
                      ($request (ai-math:proof-advice-slices $context $name $index $ranked
                        (cdr-atom $slices) $vampire $seconds $depth $limit
                        (cons-atom (AiATP:ProofSlice $k $request) $trace)))))))
                ($other (ai-math:proof-advice-slices $context $name $index $ranked
                  (cdr-atom $slices) $vampire $seconds $depth $limit
                  (cons-atom (AiATP:ProofSlice $k $summary) $trace)))))))
          ($request (AiATP:ProofUnavailable
            (list:reverse (cons-atom (AiATP:ProofSlice $k $request) $trace)))))))))
(= (ai-math:proof-advice $context $name $limit)
   (if (and (== (get-type $name) String) (ai-math:itp-natural $limit))
     (ai-math:proof-advice-ready $context $name $limit)
     (AiATP:ProofRequest display-policy ($name $limit))))
(= (ai-math:proof-advice-ready (AiProver $search $thf $itp $vampire $options) $name $limit)
   (case (ai-math:thf-lookup $thf Name $name)
     (((AiTHF:Binding $id (AiTHF:Fact $i THM $n $stmt $body))
       (let* (($slices (ai-math:option $options slices (16 32 64 128 256 512)))
              ($largest (foldl-atom $slices 0 $maximum $k (if (> $k $maximum) $k $maximum)))
              ($ranked (ai-math:entry-names (ai-math:rank-with $search $i $largest
                         (ai-math:option $options search-options ())))))
         (ai-math:proof-advice-slices $thf $name $i $ranked $slices $vampire
           (ai-math:option $options vampire-seconds 30)
           (ai-math:option $options definition-depth All) $limit ())))
      ($other (AiATP:ProofRequest theorem $name)))))
