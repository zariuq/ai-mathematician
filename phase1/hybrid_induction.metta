; Closed induction-case claims can use the full reconstruction cascade and
; recursively another source-derived split. All assembled scripts are checked.
(= (ai-math:hybrid-goal $context $synth $aliases $goal $statement $depth $hints $options)
   (let $direct (if (ai-math:option $options direct false) (ai-math:derived-prove $goal $hints $options) AiDerived:NoProof)
     (case $direct
       (((AiDerived:Proved $label $script $checked) (AiHybrid:Proved $script $checked (($direct))))
        ($other (if (ai-math:derived-can-continue $other)
          (let* (((AiProver $s $thf $itp $v $p) $context)
                 ($parent (index-atom $goal 2))
                 ($index (index-atom (ai-math:get (index-atom $itp 1) $parent AiMissing) 1))
                 ($splits (ai-math:induction-splits $thf $index $statement))
                 ($ordered (ai-math:hybrid-order-splits $context $aliases $parent $statement $splits $options)))
            (ai-math:hybrid-splits $context $synth $aliases $goal $depth $hints
              (list:take (ai-math:option $options splits 3) $ordered) $options ()))
          (ai-math:hybrid-failure $other)))))))
(= (ai-math:hybrid-failure $answer)
   (case (ai-math:derived-failure $answer)
     (((AiDerived:Unfinished $trace) (AiHybrid:Unfinished $trace))
      ($other (AiHybrid:Fault $other)))))
(= (ai-math:hybrid-case-claims $synth $cases)
   (map-atom (collapse (ai-math:positions 0 (size-atom $cases))) $i
     (let* (((AiInd:Syntax $term) (index-atom $cases $i))
            ($type (ai-math:lean-term (index-atom $synth 2) (AiLean:Scope () () ()) Tm $term)))
       (case $type
         (((AiLean:Text $text) (AiClaim (str:concat "hc" (str:number->string $i)) $text))
          ($other $other))))))
(= (ai-math:hybrid-splits $context $synth $aliases $goal $depth $hints $splits $options $trace)
   (if (== $splits ()) (AiHybrid:NotProved $trace)
     (let* (((AiHybrid:Split $split $bridge-advice) (car-atom $splits))
            ((AiInd:Split $name $count $x $guard $cases) $split)
            ($claims (ai-math:hybrid-case-claims $synth $cases))
            ($source-claims (map-atom (collapse (ai-math:positions 0 (size-atom $cases))) $i
              ((str:concat "hc" (str:number->string $i)) (index-atom (index-atom $cases $i) 1))))
            ($scripts (map-atom $claims $claim
              (str:concat "first | exact " (str:concat (ai-math:lean-name (index-atom $claim 1))
                (str:concat " | (apply " (str:concat (ai-math:lean-name (index-atom $claim 1)) " <;> assumption)"))))))
            ($closing (ai-math:induction-script $split (map-atom (collapse (ai-math:positions 0 (size-atom $scripts))) $i
              (AiInd:Winner $i "hybrid-case" (index-atom $scripts $i)))))
            ($policy (union-atom
              ((claim-handler (AiPlan:Handler &self ai-math:hybrid-claim)) (hybrid-synth $synth)
               (hybrid-aliases $aliases) (hybrid-depth $depth) (source-claims $source-claims) (final-script $closing)) $options))
            ($advised-hints (case $bridge-advice
              (((AiATP:Advice "Theorem" $premises $defs)
                (let (AiProver:Hints $sets $definitions $gd $status $atp-trace) $hints
                  (AiProver:Hints (cons-atom $premises $sets) (sort-atom (unique-atom (union-atom $defs $definitions)))
                    $gd $status $atp-trace))) ($other $hints))))
            ($result (ai-math:plan-prove $context $goal (AiProofPlan "" $claims) $advised-hints $policy)))
       (case $result
         (((AiPlan:Proved $script $checked $steps)
           (AiHybrid:Proved $script $checked (union-atom $trace ((AiHybrid:Plan $split $bridge-advice $steps)))))
          ((AiPlan:NotProved $steps $why)
            (ai-math:hybrid-splits $context $synth $aliases $goal $depth $hints (cdr-atom $splits) $options
              (union-atom $trace ((AiHybrid:Plan $split $bridge-advice $result)))))
          ($other (ai-math:hybrid-failure $other)))))))
(= (ai-math:hybrid-claim $context $goal $claim $parent-hints $options $failed)
   (let* (($name (index-atom $claim 1))
          ($source (filter-atom (ai-math:option $options source-claims ()) $row (== (car-atom $row) $name))))
     (if (== (size-atom $source) 1)
       (let* (($term (index-atom (car-atom $source) 1))
              ($aliases (ai-math:option $options hybrid-aliases NoAliases))
              ($synth (ai-math:option $options hybrid-synth NoSynth))
              ($depth (ai-math:option $options hybrid-depth 0))
              ($hints (ai-math:research-source-hints $context $aliases (index-atom $goal 2) $term $options))
              ($direct (ai-math:derived-prove $goal $hints $options)))
         (case $direct
           (((AiDerived:Proved $label $script $checked) (AiDerived:Proved $label $script $checked))
            ($other (if (and (ai-math:derived-can-continue $other) (> $depth 0))
              (case (ai-math:hybrid-goal $context $synth $aliases $goal $term (- $depth 1) $hints
                      (ai-math:research-option $options direct false))
                (((AiHybrid:Proved $script $checked $trace) (AiDerived:Proved "nested-induction" $script $checked))
                 ((AiHybrid:NotProved $trace) $failed)
                 ((AiHybrid:Unfinished $trace) (AiDerived:Unfinished $trace))
                 ($stop (AiDerived:Fault ($stop))))) (ai-math:derived-failure $other)))))) $failed)))
(= (ai-math:hybrid-order-splits $context $aliases $parent $statement $splits $options)
   (let* (($tagged (map-atom $splits $split (AiHybrid:Split $split
             (ai-math:hybrid-bridge $context $aliases $parent $statement $split
               (ai-math:option $options smt-slices (8 16 32 64)) $options))))
          ($proved (filter-atom $tagged $entry
            (case (index-atom $entry 2) (((AiATP:Advice "Theorem" $p $d) true) ($other false)))))
          ($other (filter-atom $tagged $entry (not (ai-math:contains $proved $entry)))))
     (union-atom $proved $other)))
(= (ai-math:hybrid-bridge $context $aliases $parent $statement $split $slices $options)
   (if (or (== $slices ()) (not (== (index-atom $split 1) "nat_ind"))) AiHybrid:NoBridge
     (let* (((AiProver $search $thf $itp $vampire $policy) $context)
            ($index (index-atom (ai-math:get (index-atom $itp 1) $parent AiMissing) 1))
            ($query (AiSearchFact $index THM $parent (ai-math:collect $statement $aliases false) () (ai-math:features $statement $aliases)))
            ($limit (foldl-atom $slices 0 $size $k (if (> $k $size) $k $size)))
            ($ranked (ai-math:entry-names (ai-math:rank-for $search $index $query $limit ())))
            ($problem (ai-math:smt-problem $thf (AiTHF:Fact $index THM $parent $statement NoBody)
              (list:take (car-atom $slices) $ranked)
              ((bridge (index-atom $split 3)) (guard (index-atom $split 4)) (motive true)
               (definition-depth (ai-math:option $options definition-depth 3)))))
            ($answer (case $problem
              (((AiSMT:Problem $commands $ids $skipped $unexpanded)
                (ai-math:smt-summary (ai-math:smt-vampire $thf $problem $vampire
                  (ai-math:option $options seconds 30) ("-ind" "struct" "-updr" "off" "-nm" "0"))))
               ($other $other)))))
       (case $answer
         (((AiATP:Advice "Theorem" $p $d) $answer)
          ($other (ai-math:hybrid-bridge $context $aliases $parent $statement $split (cdr-atom $slices) $options)))))))
(= (ai-math:hybrid-prove $context $declarations $target $hints $options)
   (case (ai-math:research-profile $context $options)
     (((AiProver $search $thf $itp $vampire $policy)
       (let* (($selected (AiProver $search $thf $itp $vampire $policy))
              ($index (index-atom (ai-math:get (index-atom $itp 1) $target AiMissing) 1))
              ((AiTHF:Fact $i THM $name $statement $body) (ai-math:thf-lookup $thf Ordinal $index))
              ($result (ai-math:hybrid-goal $selected (ai-math:prop-synth $declarations 10)
                (ai-math:research-source-aliases $selected) (AiDerivedGoal $itp $target "skip" 0) $statement
                (ai-math:option $options depth 1) $hints $options)))
         (case $result
           (((AiHybrid:Proved $script $checked $trace)
             (AiHybrid:Result $target $script (ai-math:itp-check-with $itp $target $script
               (ai-math:option $options budget (AiITP:Budget 120000 200000 8000))) $trace))
            ($other (AiHybrid:Result $target "" $other ()))))))
      ($other (AiHybrid:Fault $other)))))
