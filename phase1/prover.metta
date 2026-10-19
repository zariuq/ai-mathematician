; Search -> Vampire advice -> isolated Lean attempts, on PeTTa 1.0.6.
; Import library, list, lib_tptp, search, atp, proc, json, system and itp.
; Contexts retain prepared spaces, never the corpus's original proof terms.
; Only AiITP:Accepted can produce AiProver:Proved.

(= (ai-math:prover $declarations $corpus $root $lean $vampire)
   (ai-math:prover-with $declarations $corpus $root $lean $vampire ()))
(= (ai-math:prover-profile-options $profile)
   (case $profile
     ((PythonV4
       ((slices (16 32 64 128 256 512))
        (vampire-seconds 30)
        (definition-depth 3)
        (induction true)
        (induction-without-advice false)
        (use-duper Auto)
        (induction-slices (16 32 64))
        (induction-seconds 5)
        (base (AiProver:LeanPolicy
          (AiITP:Budget 120000 200000 8000) (AiITP:Budget 60000 200000 8000) 480000))
        (followup (AiProver:LeanPolicy
          (AiITP:Budget 300000 200000 8000) (AiITP:Budget 90000 200000 8000) 600000))
        (apply (AiProver:LeanPolicy
          (AiITP:Budget 300000 200000 8000) (AiITP:Budget 60000 200000 8000) 600000))
        (duper (AiProver:LeanPolicy
          (AiITP:Budget 300000 1000000 8000) (AiITP:Budget 300000 1000000 8000) 900000))
        (induction-policy (AiProver:LeanPolicy
          (AiITP:Budget 600000 200000 8000) (AiITP:Budget 120000 200000 8000) 600000))
        (induction-final (AiITP:Budget 300000 200000 8000))))
      (CettaFull ())
      ($other (AiProver:InvalidProfile $other)))))
(= (ai-math:prover-with-profile $declarations $corpus $root $lean $vampire $profile)
   (case (ai-math:prover-profile-options $profile)
     (((AiProver:InvalidProfile $unknown) (AiProver:Fault "" invalid-profile $unknown))
      ($options (ai-math:prover-with $declarations $corpus $root $lean $vampire $options)))))
(= (ai-math:prover-with $declarations $corpus $root $lean $vampire $options)
   (if (ai-math:prover-options-valid $options)
     (ai-math:prover-prepare $declarations $corpus $root $lean $vampire $options)
     (AiProver:Fault "" invalid-options $options)))
(= (ai-math:prover-prepare $declarations $corpus $root $lean $vampire $options)
   (case $declarations
     (((Error $reason $where) $declarations)
      ($items
       (case (ai-math:itp $items $root $lean)
         (((AiITP $index $application $executable $profile)
           (case (ai-math:thf $items $corpus)
             (((AiTHF $count $catalog $formats)
               (AiProver (ai-math:search $items) (AiTHF $count $catalog $formats)
                 (AiITP $index $application $executable $profile) $vampire $options))
              ($other $other))))
          ($other $other)))))))

(= (ai-math:prover-policy-valid $policy)
   (case $policy
     (((AiProver:LeanPolicy $batch $single $retry)
       (and (ai-math:itp-budget-valid $batch)
         (and (ai-math:itp-budget-valid $single) (ai-math:itp-natural $retry))))
      ($other false))))
(= (ai-math:prover-options-valid $options)
   (if (== (get-metatype $options) Expression)
     (foldl-atom $options true $ok $entry
       (and $ok (case $entry
         ((($key $value)
           (case $key
             ((slices (if (== (get-metatype $value) Expression)
                         (foldl-atom $value true $valid $k (and $valid (ai-math:itp-natural $k))) false))
              (vampire-seconds (ai-math:itp-natural $value))
              (induction-seconds (ai-math:itp-natural $value))
              (definition-depth (or (== $value All) (ai-math:itp-natural $value)))
              (trace-directory (and (== (get-type $value) String) (> (str:byte-length $value) 0)))
              (induction (or (== $value true) (== $value false)))
              (induction-without-advice (or (== $value true) (== $value false)))
              (use-duper (or (== $value Auto) (or (== $value true) (== $value false))))
              (induction-policy (ai-math:prover-policy-valid $value))
              (induction-final (ai-math:itp-budget-valid $value))
              (induction-slices (if (== (get-metatype $value) Expression)
                                  (foldl-atom $value true $valid $k (and $valid (ai-math:itp-natural $k))) false))
              (lean-stages (if (== (get-metatype $value) Expression)
                              (foldl-atom $value true $valid $stage
                                (and $valid (ai-math:contains (base followup apply duper) $stage))) false))
              (search-options (if (== (get-metatype $value) Expression)
                                (foldl-atom $value true $valid $option
                                  (and $valid (case $option
                                    ((($name $number) (== (get-type $number) Number)) ($other false))))) false))
              ($stage (if (ai-math:contains (base followup apply duper) $stage)
                        (ai-math:prover-policy-valid $value) false)))))
          ($other false)))))
     false))

(= (ai-math:prover-dupers $sets $definitions $ordinal)
   (if (== $sets ()) ()
     (let ($premises $rest) (decons-atom $sets)
       (union-atom (ai-math:prover-suffix (ai-math:duper-tactics $premises $definitions) $ordinal)
         (ai-math:prover-dupers $rest $definitions (+ $ordinal 1))))))
(= (ai-math:prover-stages-at $root $options)
   (ai-math:option $options lean-stages
     (let $duper (ai-math:option $options use-duper Auto)
       (if (or (== $duper true)
               (and (== $duper Auto) (ai-math:itp-duper-prepared $root)))
         (base followup apply duper) (base followup apply)))))
(= (ai-math:prover-stages (AiITP $catalog $root $lean $profile) $options)
   (ai-math:prover-stages-at $root $options))

; Successful solver evidence is optional and content-addressed.  It remains
; untrusted input to later reconstruction; these functions only preserve the
; exact generated problem and solver observation without inflating every
; ordinary controller result.
(= (ai-math:trace-object-path $directory Problem $digest)
   (str:join "" ($directory "/" $digest ".problem.p")))
(= (ai-math:trace-object-path $directory Solver $digest)
   (str:join "" ($directory "/" $digest ".solver.szs")))
(= (ai-math:trace-verify-object $kind $digest $text $path)
   (let $observed (fs:read-text $path)
     (if (and (== (get-type $observed) String) (== $observed $text))
       (AiATP:TraceObject $kind $digest (str:byte-length $text))
       (AiATP:TraceFault $kind $digest (AiATP:ContentMismatch $path $observed)))))
(= (ai-math:trace-write-object $directory $kind $text)
   (let* (($digest (str:sha256 $text))
          ($path (ai-math:trace-object-path $directory $kind $digest)))
     (let $exists (fs:exists $path)
       (case $exists
         ((true (ai-math:trace-verify-object $kind $digest $text $path))
          (false
           (let $written (fs:write $path $text)
             (if (== $written ())
               (ai-math:trace-verify-object $kind $digest $text $path)
               (AiATP:TraceFault $kind $digest (AiATP:WriteFailure $path $written)))))
          ($existence-fault
           (AiATP:TraceFault $kind $digest
             (AiATP:ExistenceFailure $path $existence-fault))))))))
(= (ai-math:trace-archive $context $problem $goal $slice $summary $report $directory)
   (case $report
     (((AiATP:Report $status $names $definitions $references
         (proc:result $termination $completion $stdout $stderr $capture) $envelope $payloads)
       (ai-math:trace-archive-report $context $problem $goal $slice $summary
         $stdout $payloads $directory))
      ($other (AiATP:TraceFailure $summary (AiATP:MissingReport $other))))))
(= (ai-math:trace-archive-report $context $problem $goal $slice $summary $stdout $payloads $directory)
   (case (ai-math:thf-text $context $problem)
     (((Error $reason $where)
       (AiATP:TraceFailure $summary (AiATP:ProblemPrintFailure $reason $where)))
      ($problem-text
       (ai-math:trace-archive-text $goal $slice $summary $problem-text $stdout $payloads $directory)))))
(= (ai-math:trace-archive-text $goal $slice $summary $problem-text $stdout $payloads $directory)
   (let* (($problem-object (ai-math:trace-write-object $directory Problem $problem-text))
          ($solver-object (ai-math:trace-write-object $directory Solver $stdout)))
     (ai-math:trace-archive-objects
       $goal $slice $summary $payloads $problem-object $solver-object)))
(= (ai-math:trace-archive-objects $goal $slice $summary $payloads $problem-object $solver-object)
   (case $problem-object
     (((AiATP:TraceObject $pk $ph $pb)
       (case $solver-object
         (((AiATP:TraceObject $sk $sh $sb)
           (AiATP:ArchivedAdvice $summary
             (AiATP:TraceRef "ai-math.tstp.v1" $goal $slice
               (AiATP:TraceObject $pk $ph $pb)
               (AiATP:TraceObject $sk $sh $sb)
               (str:sha256 (repr $payloads)))))
          ($solver-fault (AiATP:TraceFailure $summary $solver-fault)))))
      ($problem-fault (AiATP:TraceFailure $summary $problem-fault)))))
(= (ai-math:prover-retain-advice $context $problem $goal $slice $summary $report $options)
   (case $summary
     (((AiATP:Advice "Theorem" $premises $definitions)
       (let $directory (ai-math:option $options trace-directory AiATP:NoTrace)
         (if (== $directory AiATP:NoTrace) $summary
           (ai-math:trace-archive $context $problem $goal $slice $summary $report $directory))))
      ($other $other))))
(= (ai-math:prover-advice $summary)
   (case $summary
     (((AiATP:ArchivedAdvice $advice $reference) $advice)
      ((AiATP:TraceFailure $advice $fault) $advice)
      ($other $other))))


; Every slice is attempted: a different sufficient set may reconstruct better.
; Solver output contributes hints, not a proof-acceptance judgment.
(= (ai-math:prover-hints (AiProver $search $thf $itp $vampire $options) $name)
   (if (ai-math:prover-options-valid $options)
     (ai-math:prover-collect-hints (AiProver $search $thf $itp $vampire $options) $name)
     (AiProver:Fault $name invalid-options $options)))
(= (ai-math:prover-collect-hints (AiProver $search $thf $itp $vampire $options) $name)
   (case (ai-math:thf-lookup $thf Name $name)
     (((AiTHF:Binding $id (AiTHF:Fact $i THM $n $stmt $body))
       (let* (($slices (ai-math:option $options slices (16 32 64 128 256 512)))
              ($limit (foldl-atom $slices 0 $maximum $k (if (> $k $maximum) $k $maximum)))
              ($ranked (ai-math:entry-names (ai-math:rank-with $search $i $limit
                         (ai-math:option $options search-options ()))))
              ($facts (filter-atom $ranked $premise
                (case (ai-math:thf-lookup $thf Name $premise)
                  (((AiTHF:Binding $pid (AiTHF:Fact $pi $kind $pn $ps $pb))
                    (ai-math:contains (THM AXIOM) $kind)) ($other false)))))
              ($goal-defs (ai-math:prover-goal-defs $thf (ai-math:search-goal $search $i)))
              ($sweep (ai-math:prover-slices $thf $name $i $ranked $slices $vampire
                        (ai-math:option $options vampire-seconds 30)
                        (ai-math:option $options definition-depth All) $options)))
         (ai-math:prover-summarize-hints $facts $goal-defs $sweep)))
      ($other (AiProver:Fault $name unknown-theorem $other)))))
(= (ai-math:prover-slices $thf $goal $index $ranked $slices $vampire $seconds $depth $options)
   (if (== $slices ()) ()
     (let ($k $rest) (decons-atom $slices)
       (case (ai-math:thf-problem $thf $index (list:take $k $ranked) $depth)
         (((AiTHF:Problem $records $ids $skipped $unexpanded)
           (let* (($problem (AiTHF:Problem $records $ids $skipped $unexpanded))
                  ($report (ai-math:vampire $thf $problem $vampire $seconds))
                  ($summary (ai-math:atp-summary $report))
                  ($retained (ai-math:prover-retain-advice
                               $thf $problem $goal $k $summary $report $options)))
             (cons-atom (AiProver:Slice $k $retained $skipped $unexpanded)
               (ai-math:prover-slices $thf $goal $index $ranked $rest
                 $vampire $seconds $depth $options))))
          ($request ((AiProver:Slice $k (AiProver:TranslationRequest $request) () ()))))))))
(= (ai-math:prover-summarize-hints $facts $goal-defs $trace)
   (let* (($found (filter-atom $trace $slice
                   (case (ai-math:prover-advice (index-atom $slice 2))
                     (((AiATP:Advice "Theorem" $p $d) true) ($other false)))))
          ($sets (unique-atom (map-atom $found $slice
                   (let (AiATP:Advice $status $premises $definitions)
                     (ai-math:prover-advice (index-atom $slice 2)) $premises))))
          ($definitions (sort-atom (unique-atom (foldl-atom $found $goal-defs $out $slice
                            (let (AiATP:Advice $status $premises $defs)
                              (ai-math:prover-advice (index-atom $slice 2))
                              (union-atom $out $defs))))))
          ($fallback (list:take 8 $facts)))
     (AiProver:Hints
       (if (== $found ()) ($fallback)
         (if (and (foldl-atom $sets true $small $set (and $small (< (size-atom $set) 2)))
                  (not (ai-math:contains $sets $fallback)))
           (union-atom $sets ($fallback)) $sets))
       $definitions $goal-defs
       (if (== $found ())
         (foldl-atom $trace "skipped" $last $slice
           (case (ai-math:prover-advice (index-atom $slice 2))
             (((AiATP:Advice $status $p $d) $status)
              ((AiProver:TranslationRequest $request) "unsupported")
              ($other "unavailable"))))
         (str:concat "Theorem@" (str:join ","
           (map-atom $found $slice (str:number->string (index-atom $slice 1))))))
       $trace)))

(= (ai-math:prover-suffix $candidates $number)
   (map-atom $candidates $candidate
     (let (AiITP:Candidate $label $tactic) $candidate
       (AiITP:Candidate (str:join "" ($label "#" (str:number->string $number))) $tactic))))

; Advice is optional, but a failed bridge is not completed search coverage.
; Keep it in the same attempt ledger as Lean faults; a later checked proof
; may still win, while failed reconstruction retains the original cause.
(= (ai-math:prover-solver-failure $goal $k $status $observation $envelope)
   (case $observation
     (((proc:result $termination $completion $stdout $stderr $capture)
       (if (or (ai-math:contains (proc:timed-out proc:cancelled) $completion)
               (== ($termination $completion) ((proc:exited 0) proc:normal)))
         (AiITP:Unfinished $goal vampire-process ($k $status $observation $envelope))
         (AiITP:Fault $goal vampire-process ($k $status $observation $envelope))))
      ($other (AiITP:Fault $goal vampire-process ($k $status $observation $envelope))))))
(= (ai-math:prover-bridge-attempts $goal $trace)
   (foldl-atom $trace () $out $slice
     (let (AiProver:Slice $k $raw $skipped $unexpanded) $slice
       (let $advice (ai-math:prover-advice $raw)
         (union-atom $out
           (case $advice
             (((AiATP:Advice $status $premises $definitions)
               (if (ai-math:contains ("Timeout" "ResourceOut" "MemoryOut") $status)
                 ((AiProver:StageFault atp (AiITP:Unfinished $goal vampire-resource ($k $status)))) ()))
              ((Error $operation $reason)
               ((AiProver:StageFault atp (AiITP:Fault $goal thf-print ($k $operation $reason)))))
              ((AiATP:PayloadInterpretationNeeded $payloads)
               ((AiProver:StageFault atp (AiITP:Unfinished $goal vampire-payload ($k $payloads)))))
              ((AiProver:TranslationRequest $request)
               ((AiProver:StageFault atp (AiITP:Unfinished $goal source-interpretation ($k $request)))))
              ((AiATP:IncompleteCapture $status)
               ((AiProver:StageFault atp (AiITP:Unfinished $goal incomplete-solver-capture ($k $status)))))
              ((AiATP:UnfinishedOrFaulted $status $observation $envelope)
               ((AiProver:StageFault atp
                  (ai-math:prover-solver-failure $goal $k $status $observation $envelope))))
              ($other ((AiProver:StageFault atp (AiITP:Fault $goal vampire-bridge ($k $other))))))))))))
(= (ai-math:prover-secondary-base $sets $defs $goal-defs $number)
   (if (== $sets ()) ()
     (let ($premises $rest) (decons-atom $sets)
       (union-atom
         (ai-math:prover-suffix
           (filter-atom (ai-math:candidate-tactics $premises $defs $goal-defs) $candidate
             (let (AiITP:Candidate $label $script) $candidate
               (or (str:starts-with $label "prem-")
                 (or (str:starts-with $label "solve_by_elim") (str:starts-with $label "goal-unfold"))))) $number)
         (ai-math:prover-secondary-base $rest $defs $goal-defs (+ $number 1))))))
(= (ai-math:prover-followups $sets $defs $goal-defs $number)
   (if (== $sets ()) ()
     (let ($premises $rest) (decons-atom $sets)
       (union-atom (ai-math:prover-suffix (ai-math:followup-tactics $premises $defs $goal-defs) $number)
         (ai-math:prover-followups $rest $defs $goal-defs (+ $number 1))))))
(= (ai-math:prover-applies $sets $defs $number)
   (if (== $sets ()) ()
     (let ($premises $rest) (decons-atom $sets)
       (union-atom (ai-math:prover-suffix (ai-math:apply-tactics $premises $defs) $number)
         (ai-math:prover-applies $rest $defs (+ $number 1))))))
(= (ai-math:prover-stage-candidates $stage (AiProver:Hints $sets $defs $goal-defs $status $trace) $extras)
   (let $advised (str:starts-with $status "Theorem")
     (case $stage
       ((base (union-atom
                (let $candidates (ai-math:candidate-tactics (car-atom $sets) $defs $goal-defs)
                  (if $advised $candidates
                    (filter-atom $candidates $candidate
                      (ai-math:contains ("intro-grind" "unfold-grind" "solve_by_elim" "goal-unfold-sbe" "ext-grind")
                        (index-atom $candidate 1))))) $extras))
        (followup (union-atom
                    (ai-math:prover-secondary-base (cdr-atom $sets) $defs $goal-defs 2)
                    (if $advised (ai-math:prover-followups $sets $defs $goal-defs 1) ())))
        (apply (if $advised (ai-math:prover-applies $sets $defs 1) ()))
        (duper (if $advised (ai-math:prover-dupers (list:take 2 $sets) $defs 1) ()))
        ($other (AiProver:InvalidStage $stage))))))

; These are the original application's explicitly named resource policies,
; not language or library ceilings. A caller can supply zero/unbounded budgets.
(= (ai-math:prover-policy $options $stage)
   (ai-math:option $options $stage
     (case $stage
       ((base (AiProver:LeanPolicy (AiITP:Budget 120000 200000 8000) (AiITP:Budget 60000 200000 8000) 480000))
        (followup (AiProver:LeanPolicy (AiITP:Budget 300000 200000 8000) (AiITP:Budget 90000 200000 8000) 600000))
        (apply (AiProver:LeanPolicy (AiITP:Budget 300000 200000 8000) (AiITP:Budget 60000 200000 8000) 600000))
        (duper (AiProver:LeanPolicy (AiITP:Budget 300000 1000000 8000) (AiITP:Budget 300000 1000000 8000) 900000))))))

(= (ai-math:prover-attempts $stage $candidates $attempts $ordinal)
   (if (== $candidates ()) ()
     (let* ((($candidate $more) (decons-atom $candidates))
            ((AiITP:Candidate $label $script) $candidate)
            (($attempt $rest) (decons-atom $attempts))
            ((AiITP:Attempt $same-label $result) $attempt))
       (cons-atom (AiProver:Attempt $stage $ordinal $label $script $result)
         (ai-math:prover-attempts $stage $more $rest (+ $ordinal 1))))))
(= (ai-math:prove $context $name) (ai-math:prove-with $context $name ()))
(= (ai-math:prove-with $context $name $extras)
   (case $context
     (((AiProver $search $thf $itp $vampire $options)
       (if (ai-math:itp-candidates-valid $extras)
         (case (ai-math:prover-hints $context $name)
           (((AiProver:Hints $sets $defs $goal-defs $status $trace)
             (let (AiTHF:Binding $id (AiTHF:Fact $index THM $n $s $b))
               (ai-math:thf-lookup $thf Name $name)
               (let* (($stages (ai-math:prover-stages $itp $options))
                      ($direct (ai-math:prover-run $itp $name $index
                        (AiProver:Hints $sets $defs $goal-defs $status $trace)
                        $stages $stages $options $extras (ai-math:prover-bridge-attempts $name $trace))))
                 (ai-math:induction-after $context $name $direct))))
            ($other $other)))
         (AiProver:Fault $name invalid-candidates $extras)))
      ($other $other))))
(= (ai-math:prover-run $itp $name $index $hints $pending $stages $options $extras $attempts)
   (if (== $pending ())
     (AiProver:Result $name $index $hints $attempts (ai-math:prover-outcome $attempts $stages))
     (let* ((($stage $rest) (decons-atom $pending))
            ($candidates (ai-math:prover-stage-candidates $stage $hints $extras)))
       (case $candidates
         (((AiProver:InvalidStage $invalid) (AiProver:Fault $name invalid-stage $invalid))
          ($rows
           (if (== $rows ())
             (ai-math:prover-run $itp $name $index $hints $rest $stages $options $extras $attempts)
             (case (ai-math:prover-policy $options $stage)
               (((AiProver:LeanPolicy $batch $single $retry)
                 (let* (($result (ai-math:prover-run-attempts $itp $name $stage $rows $batch $single $retry))
                        ($new (case $result
                          (((AiITP:Batch $n $out) (ai-math:prover-attempts $stage $rows $out 0))
                           ($fault ((AiProver:StageFault $stage $fault))))))
                        ($winner (ai-math:prover-winner $new))
                        ($all (union-atom $attempts $new)))
                   (if (== $winner AiProver:NoWinner)
                     (ai-math:prover-run $itp $name $index $hints $rest $stages $options $extras $all)
                     (AiProver:Result $name $index $hints $all $winner))))
                ($other (AiProver:Fault $name invalid-policy $other)))))))))))

; Duper candidates run separately so a slow variant cannot consume another
; variant's budget. The common acceptance and retry path stays unchanged.
(= (ai-math:prover-run-attempts $itp $name $stage $rows $batch $single $retry)
   (if (== $stage duper)
     (case (ai-math:itp-select-profile $itp duper)
       (((AiITP $catalog $root $lean duper)
         (let $started (system:monotonic-ns)
           (AiITP:Batch $name
             (ai-math:itp-retry (AiITP $catalog $root $lean duper) $name $rows $single $retry $started false))))
        ($other $other)))
     (ai-math:itp-batch-resilient $itp $name $rows $batch $single $retry)))
