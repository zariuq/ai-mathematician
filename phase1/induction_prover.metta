; Untrusted induction advice and independently checked reconstruction.
; Entry points additionally import induction.metta, itp and the ATP/controller.

(= (ai-math:ind-case-advice $thf $term $ranked $slices $vampire $seconds $depth $trace)
   (if (== $slices ()) (AiInd:NoCaseAdvice $trace)
     (let ($size $rest) (decons-atom $slices)
       (case (ai-math:thf-statement-problem $thf $term (list:take $size $ranked) $depth)
         (((AiTHF:Problem $records $ids $skipped $unexpanded)
           (let* (($summary (ai-math:atp-summary
                            (ai-math:vampire $thf (AiTHF:Problem $records $ids $skipped $unexpanded) $vampire $seconds)))
                  ($next (union-atom $trace ((AiInd:Slice $size $summary $skipped $unexpanded)))))
             (case $summary
               (((AiATP:Advice "Theorem" $premises $definitions) (AiInd:CaseAdvice $premises $next))
                ($other (ai-math:ind-case-advice $thf $term $ranked $rest $vampire $seconds $depth $next))))))
          ($request (AiInd:NoCaseAdvice (union-atom $trace ((AiInd:TranslationRequest $request))))))))))
(= (ai-math:ind-cases-advice $thf $cases $ranked $slices $vampire $seconds $depth $ordinal)
   (if (== $cases ()) (AiInd:CasesAdvice () ())
     (let ($head $rest) (decons-atom $cases)
       (case $head
         (((AiInd:Syntax $term)
           (case (ai-math:ind-case-advice $thf $term $ranked $slices $vampire $seconds $depth ())
             (((AiInd:CaseAdvice $premises $trace)
               (case (ai-math:ind-cases-advice $thf $rest $ranked $slices $vampire $seconds $depth (+ $ordinal 1))
                 (((AiInd:CasesAdvice $sets $traces)
                   (AiInd:CasesAdvice (cons-atom $premises $sets) (cons-atom (AiInd:CaseTrace $ordinal $trace) $traces)))
                  ((AiInd:NoCaseAdvice $traces)
                   (AiInd:NoCaseAdvice (cons-atom (AiInd:CaseTrace $ordinal $trace) $traces))))))
              ((AiInd:NoCaseAdvice $trace) (AiInd:NoCaseAdvice ((AiInd:CaseTrace $ordinal $trace)))))))
          ($request (AiInd:NoCaseAdvice ((AiInd:TranslationRequest $request)))))))))
(= (ai-math:ind-select-plan $thf $splits $ranked $slices $vampire $seconds $depth $trace)
   (if (== $splits ()) (AiInd:NoPlan $trace)
     (let* ((($split $rest) (decons-atom $splits))
            ((AiInd:Split $name $count $x $guard $cases) $split))
       (case (ai-math:ind-cases-advice $thf $cases $ranked $slices $vampire $seconds $depth 0)
         (((AiInd:CasesAdvice $premises $details)
           (AiInd:Plan $split $premises (union-atom $trace ((AiInd:SplitAdvice $split $details)))))
          ((AiInd:NoCaseAdvice $details)
           (ai-math:ind-select-plan $thf $rest $ranked $slices $vampire $seconds
             $depth (union-atom $trace ((AiInd:SplitAdvice $split $details))))))))))

; Solver advice is optional. An unresolved or absent refutation does not
; prevent checking an independently proposed proof of the actual cases.
; The evidence records that these candidates have no solver-selected facts.
(= (ai-math:ind-local-plan $split $trace)
   (let (AiInd:Split $name $count $x $guard $cases) $split
     (AiInd:Plan $split (map-atom $cases $case ())
       (union-atom $trace ((AiInd:WithoutSolverAdvice $name))))))
(= (ai-math:ind-case-candidates $sets $definitions $ordinal)
   (if (== $sets ()) ()
     (let ($premises $rest) (decons-atom $sets)
       (union-atom
         (map-atom (ai-math:candidate-tactics $premises $definitions $definitions) $candidate
           (let (AiITP:Candidate $label $tactic) $candidate (AiITP:CaseCandidate $ordinal $label $tactic)))
         (ai-math:ind-case-candidates $rest $definitions (+ $ordinal 1))))))
(= (ai-math:ind-case-results $candidates $answers)
   (if (== $candidates ()) ()
     (let* ((($candidate $more) (decons-atom $candidates))
            ((AiITP:CaseCandidate $case $label $tactic) $candidate)
            (($answer $rest) (decons-atom $answers))
            ((AiITP:CaseAttempt $c $l $result) $answer))
       (cons-atom (AiInd:Attempt $case $label $tactic $result) (ai-math:ind-case-results $more $rest)))))
(= (ai-math:ind-case-winner $attempts $ordinal $count)
   (if (== $attempts ()) AiInd:NoWinner
     (let ($head $rest) (decons-atom $attempts)
       (case $head
         (((AiInd:Attempt $case $label $tactic (AiITP:CaseAccepted $target $same $total $used $axioms))
           (if (and (== $case $ordinal) (and (== $same $ordinal) (== $total $count)))
             (AiInd:Winner $ordinal $label $tactic) (ai-math:ind-case-winner $rest $ordinal $count)))
          ($other (ai-math:ind-case-winner $rest $ordinal $count)))))))
(= (ai-math:ind-case-winners $attempts $ordinal $count)
   (if (== $ordinal $count) (AiInd:Winners ())
     (case (ai-math:ind-case-winner $attempts $ordinal $count)
       ((AiInd:NoWinner (AiInd:MissingCase $ordinal))
        ($winner (case (ai-math:ind-case-winners $attempts (+ $ordinal 1) $count)
          (((AiInd:Winners $rest) (AiInd:Winners (cons-atom $winner $rest))) ($other $other))))))))
(= (ai-math:induction-script $split $winners)
   (str:join "\n" (cons-atom (ai-math:induction-prefix $split)
     (map-atom $winners $winner
       (let (AiInd:Winner $ordinal $label $tactic) $winner
         (str:concat "·\n  " (str:join "\n  " (str:split "\n" $tactic))))))))
(= (ai-math:ind-reconstruct $itp $target $plan $goal-defs $options)
   (let* (((AiInd:Plan $split $sets $trace) $plan)
          ((AiInd:Split $principle $count $x $guard $cases) $split)
          ($candidates (ai-math:ind-case-candidates $sets $goal-defs 0))
          ($policy (ai-math:option $options induction-policy
                     (AiProver:LeanPolicy (AiITP:Budget 600000 200000 8000) (AiITP:Budget 120000 200000 8000) 600000))))
     (let (AiProver:LeanPolicy $batch $single $retry) $policy
       (case (ai-math:itp-case-batch-resilient $itp $target (ai-math:induction-prefix $split) $candidates $batch $single $retry)
         (((AiITP:CaseBatch $name $answers)
           (let $attempts (ai-math:ind-case-results $candidates $answers)
             (case (ai-math:ind-case-winners $attempts 0 (size-atom $cases))
               (((AiInd:Winners $winners)
                 (let $script (ai-math:induction-script $split $winners)
                   (AiInd:Reconstruction $split $trace $attempts $script
                     (ai-math:itp-check-with $itp $target $script
                       (ai-math:option $options induction-final (AiITP:Budget 300000 200000 8000))))))
                ($missing (AiInd:MissingProof $split $trace $attempts $missing))))))
          ($other (AiInd:CheckFailure $split $trace $other)))))))
(= (ai-math:ind-local-plans $itp $target $splits $goal-defs $options $trace $attempts)
   (if (== $splits ()) (AiInd:NoReconstruction $trace $attempts)
     (let ($split $rest) (decons-atom $splits)
       (let $result (ai-math:ind-reconstruct $itp $target
                      (ai-math:ind-local-plan $split $trace) $goal-defs $options)
         (case $result
           (((AiInd:Reconstruction $s $t $a $script (AiITP:Accepted $n $u $ax)) $result)
            ((AiInd:MissingProof $s $t $a $missing)
             (ai-math:ind-local-plans $itp $target $rest $goal-defs $options $trace
               (union-atom $attempts ($result))))
            ($other $other)))))))
(= (ai-math:induction-prove (AiProver $search $thf $itp $vampire $options) $target)
   (case (ai-math:thf-lookup $thf Name $target)
     (((AiTHF:Binding $id (AiTHF:Fact $index THM $name $statement $body))
       (let* (($slices (ai-math:option $options induction-slices (16 32 64)))
              ($limit (foldl-atom $slices 0 $maximum $size (if (> $size $maximum) $size $maximum)))
              ($ranked (ai-math:entry-names (ai-math:rank-with $search $index $limit
                         (ai-math:option $options search-options ()))))
              ($splits (ai-math:induction-splits $thf $index $statement)))
         (case (ai-math:ind-select-plan $thf $splits $ranked $slices $vampire
                 (ai-math:option $options induction-seconds 5) (ai-math:option $options definition-depth All) ())
           (((AiInd:Plan $split $sets $trace)
             (ai-math:ind-reconstruct $itp $target (AiInd:Plan $split $sets $trace)
               (ai-math:prover-goal-defs $thf (ai-math:search-goal $search $index)) $options))
            ((AiInd:NoPlan $trace)
             (if (ai-math:option $options induction-without-advice true)
               (ai-math:ind-local-plans $itp $target $splits
                 (ai-math:prover-goal-defs $thf (ai-math:search-goal $search $index)) $options $trace ())
               (AiInd:NoReconstruction $trace ())))
            ($other $other)))))
      ($other (AiInd:UnknownGoal $target $other)))))

(= (ai-math:induction-after $context $target $direct)
   (case ($context $direct)
     ((((AiProver $search $thf $itp $vampire $options)
        (AiProver:Result $name $index (AiProver:Hints $sets $defs $goal-defs $status $trace) $attempts $outcome))
       (if (and (ai-math:option $options induction true)
                (and (not (str:starts-with $status "Theorem"))
                  (case $outcome
                    (((AiProver:Proved $s $i $l $t $u $a) false)
                     ((AiProver:Faulted $faults) false) ($other true)))))
         (let* (($evidence (ai-math:induction-prove $context $target))
                ($extra (case $evidence
                  (((AiInd:Reconstruction $split $advice $cases $script $result)
                    ((AiProver:Attempt induction 0 (str:concat "induction:" (index-atom $split 1)) $script $result)))
                   ((AiInd:MissingProof $split $advice $cases $missing)
                    (map-atom $cases $attempt
                      (let (AiInd:Attempt $ordinal $label $tactic $result) $attempt
                        (AiProver:Attempt induction-case $ordinal $label $tactic $result))))
                   ((AiInd:NoReconstruction $advice $plans)
                    (foldl-atom $plans () $out $plan
                      (let (AiInd:MissingProof $split $plan-trace $cases $missing) $plan
                        (union-atom $out (map-atom $cases $attempt
                          (let (AiInd:Attempt $ordinal $label $tactic $result) $attempt
                            (AiProver:Attempt induction-case $ordinal $label $tactic $result)))))))
                   ((AiInd:CheckFailure $split $advice $result) ((AiProver:StageFault induction $result)))
                   ($other ()))))
                ($all (union-atom $attempts (union-atom ((AiProver:InductionEvidence $evidence)) $extra)))
                ($winner (ai-math:prover-winner $extra)))
           (AiProver:Result $name $index (AiProver:Hints $sets $defs $goal-defs $status $trace) $all
             (if (== $winner AiProver:NoWinner)
               (case $outcome
                 (((AiProver:NotProved (AiProver:Coverage $stages))
                   (ai-math:prover-outcome $all (union-atom $stages (induction))))
                  ($other $other))) $winner)))
         $direct))
      ($other $direct))))
