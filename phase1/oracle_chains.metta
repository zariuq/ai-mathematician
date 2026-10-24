; Oracle analysis deliberately reads the original proof's stepping stones.
; Its observations do not count as unaided discovery. A chain counts as a
; proof only after checking its assembled script at the original statement.
(= (ai-math:oracle-close-proposition $proposition $binders)
   (foldl-atom (list:reverse $binders) $proposition $closed $binder
     (let ($kind $type) $binder (if (== $kind tm) (ALL $type $closed) (IMP $type $closed)))))
(= (ai-math:oracle-haves $node $binders)
   (case $node
     (((PPFAP (PLAM $proposition $continuation) $justification)
       (cons-atom (ai-math:oracle-close-proposition $proposition $binders)
         (union-atom (ai-math:oracle-haves $justification $binders)
           (ai-math:oracle-haves $continuation (union-atom $binders ((pf $proposition)))))))
      ((TLAM $type $body) (ai-math:oracle-haves $body (union-atom $binders ((tm $type)))))
      ((PLAM $type $body) (ai-math:oracle-haves $body (union-atom $binders ((pf $type)))))
      ($other (if (== (get-metatype $other) Expression)
        (if (== $other ()) () (ai-math:research-concat
          (map-atom (cdr-atom $other) $child (ai-math:oracle-haves $child $binders)))) ())))))
(= (ai-math:oracle-hops $declaration)
   (case $declaration
     (((Decl $i THM $name $hash $statement $body $ss $ds $fs)
       (AiOracle:Hops $name (ai-math:oracle-haves $body ())))
      ($other (AiOracle:Fault not-a-theorem)))))
(= (ai-math:oracle-plan $synth (AiOracle:Hops $parent $propositions))
   (AiProofPlan "" (ai-math:research-concat
     (map-atom (collapse (ai-math:positions 0 (size-atom $propositions))) $i
       (case (ai-math:lean-term (index-atom $synth 2) (AiLean:Scope () () ()) Tm (index-atom $propositions $i))
         (((AiLean:Text $type) ((AiClaim (str:concat "step" (str:number->string $i)) $type)))
          ($unsupported ())))))))
(= (ai-math:chain-prove $context $synth $declaration $hints $options)
   (let* (($hops (ai-math:oracle-hops $declaration))
          ($plan (ai-math:oracle-plan $synth $hops))
          ($source-claims (map-atom (collapse (ai-math:positions 0 (size-atom (index-atom $hops 2)))) $i
            ((str:concat "step" (str:number->string $i)) (index-atom (index-atom $hops 2) $i))))
          ($policy (union-atom ((claim-handler (AiPlan:Handler &self ai-math:oracle-claim))
            (source-claims $source-claims) (source-aliases (ai-math:research-source-aliases $context))) $options))
          ($result (ai-math:decompose-plan $context (ai-math:declaration-name $declaration)
            $plan $hints (ai-math:research-option $policy skip-failed true))))
     (AiOracle:Chain $hops $result)))
(= (ai-math:oracle-claim $context $goal $claim $hints $options $failed)
   (case (filter-atom (ai-math:option $options source-claims ()) $row (== (car-atom $row) (index-atom $claim 1)))
     ((($source)
       (ai-math:derived-prove $goal
         (ai-math:research-source-hints $context (ai-math:option $options source-aliases NoAliases)
           (index-atom $goal 2) (index-atom $source 1) $options) $options))
      ($other $failed))))
(= (ai-math:oracle-probe $context $synth $declaration $hints $options)
   (let* (((AiProver $search $thf $itp $vampire $policy) $context)
          ($parent (ai-math:declaration-name $declaration))
          ($hops (ai-math:oracle-hops $declaration))
          ($aliases (ai-math:research-source-aliases $context))
          ($sources (map-atom (collapse (ai-math:positions 0 (size-atom (index-atom $hops 2)))) $i
             ((str:concat "step" (str:number->string $i)) (index-atom (index-atom $hops 2) $i))))
          ($plan (ai-math:oracle-plan $synth $hops)))
     (AiOracle:Observations $parent
       (map-atom (index-atom $plan 2) $claim
         (let* (($prefix (ai-math:plan-relative-prefix (AiProofPlan "" ($claim)) () ($claim)))
                ($goal (AiDerivedGoal $itp $parent $prefix 0)))
           (let ($source) (filter-atom $sources $row (== (car-atom $row) (index-atom $claim 1)))
             ($claim (ai-math:derived-prove $goal
               (ai-math:research-source-hints $context $aliases $parent (index-atom $source 1) $options)
               $options))))))))
