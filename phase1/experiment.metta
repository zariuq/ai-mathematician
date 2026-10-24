; Sequential discovery and resumable JSONL observations, on PeTTa 1.0.6.
; Import after prover.metta. One caller owns a log; use the process API's
; external lock wrapper when multiple operating-system processes may race.
; Saved claims never produce acceptance without rechecking their tactics.

; The run lock or a worker's private destination serializes each publisher.
; Interrupted preparation only touches the sibling pending file. Rename
; publishes an entire snapshot, without promising power-failure durability.
(= (ai-math:run-publish-file $path $text)
   (let $pending (str:concat $path ".pending")
     (case (fs:write $pending $text)
       ((() (fs:rename $pending $path))
        ($fault $fault)))))

(= (ai-math:run-source-files)
   ("phase1/library.metta" "phase1/search.metta" "phase1/atp.metta" "phase1/vampire_output.metta"
    "phase1/itp.metta" "phase1/proof_strategy.metta" "phase1/induction.metta" "phase1/smt_bridge.metta"
    "formats/SMTLibExport.module"
    "phase1/induction_prover.metta" "phase1/prover.metta" "phase1/experiment.metta"
    "phase1/experiment_workers.metta" "phase1/experiment_worker_main.metta"
    "phase1/workers_main.metta" "phase1/workers_driver.metta" "lean-toolchain"
    "tools/duper-env/lakefile.toml" "tools/duper-env/lake-manifest.json"
    "tools/duper-env/lean-toolchain"))
(= (ai-math:run-checker-files)
   (let $native (== (system:getenv-or-default "CETTA_ITP_RUNTIME" "interpreted") "native")
     (union-atom
       (if $native (".cetta/lean-native/itp-guard" ".cetta/lean-native/itp-worker") ())
       (map-atom ("MegLib" "Bridge" "CettaProofTactics" "CettaITP" "CettaProposalView" "CettaITPGuard") $module
         (str:join "" ((if $native ".cetta/lean-native/lib/" "lib/") $module ".olean"))))))
(= (ai-math:run-descriptor $root $corpus $options $toolchain)
   (let* (($corpus-text (fs:read-text $corpus))
          ($sources (map-atom (ai-math:run-source-files) $path
            (let $text (fs:read-text (str:join "" ($root "/" $path)))
              (if (== (get-type $text) String) ($path (str:sha256 $text))
                (AiRun:Fault source-read ($path $text))))))
          ($failed (filter-atom $sources $source
            (case $source (((AiRun:Fault $why $detail) true) ($other false))))))
     (if (== (get-type $corpus-text) String)
       (if (== $failed ())
         (case (ai-math:itp-complete-process-text
                 (proc:run (union-atom ("sha256sum" "--") (ai-math:run-checker-files)) ((cwd $root))))
           (((AiITP:ProcessText $artifacts)
             (let* (($artifact-rows (map-atom
                       (filter-atom (str:split "\n" $artifacts) $line (not (== $line ""))) $line
                       (let ($hash $file) (str:split "  " $line) ($file $hash))))
                    ($descriptor (AiRun:Descriptor "ai-math.run.v1" "petta@1.0.6"
                       (str:sha256 $corpus-text) (union-atom $sources $artifact-rows) $options $toolchain)))
               (AiRun:Identity (str:sha256 (repr $descriptor)) $descriptor)))
            ($other (AiRun:Fault checker-artifacts $other))))
         (car-atom $failed))
       (AiRun:Fault corpus-read $corpus-text))))
(= (ai-math:run-header (AiRun:Identity $key $descriptor))
   (JsonObject ((JsonPair "schema" "ai-math.run.v1")
     (JsonPair "run" $key) (JsonPair "descriptor" (repr $descriptor)))))
(= (ai-math:run-outcome $outcome)
   (case $outcome
     (((AiProver:Proved $s $o $l $t $u $a) "proved")
      ((AiProver:NotProved $coverage) "not-proved")
      ((AiProver:Unfinished $evidence) "unfinished")
      ($other "fault"))))
(= (ai-math:run-trace-field $slice)
   (case $slice
     (((AiProver:Slice $k (AiATP:SMTAdvice $advice) $skipped $unexpanded)
       (ai-math:run-trace-field (AiProver:Slice $k $advice $skipped $unexpanded)))
      ((AiProver:Slice $k
         (AiATP:ArchivedAdvice $advice
           (AiATP:TraceRef $schema $goal $same-k
             (AiATP:TraceObject $problem-kind $problem-digest $problem-bytes)
             (AiATP:TraceObject Solver $solver-digest $solver-bytes) $parsed-digest))
         $skipped $unexpanded)
       (AiRun:TraceReference
         (JsonObject
           ((JsonPair "schema" $schema)
            (JsonPair "goal" $goal)
            (JsonPair "slice" $same-k)
            (JsonPair "problem_sha256" $problem-digest)
            (JsonPair "problem_bytes" $problem-bytes)
            (JsonPair "solver_sha256" $solver-digest)
            (JsonPair "solver_bytes" $solver-bytes)
            (JsonPair "parsed_sha256" $parsed-digest)))))
      ((AiProver:Slice $k (AiATP:TraceFailure $advice $fault) $skipped $unexpanded)
       (AiRun:TraceFault
         (JsonObject
           ((JsonPair "slice" $k)
            (JsonPair "detail" (repr $fault))))))
      ($other AiRun:NoTrace))))
(= (ai-math:run-trace-fields $trace)
   (let (AiRun:TraceFields $references $faults)
     (foldl-atom $trace (AiRun:TraceFields () ()) $state $slice
       (let (AiRun:TraceFields $refs $bad) $state
         (case (ai-math:run-trace-field $slice)
           (((AiRun:TraceReference $value) (AiRun:TraceFields (cons-atom $value $refs) $bad))
            ((AiRun:TraceFault $value) (AiRun:TraceFields $refs (cons-atom $value $bad)))
            ($other $state)))))
     (AiRun:TraceFields (list:reverse $references) (list:reverse $faults))))
(= (ai-math:run-result $key $nanoseconds $result)
   (case $result
     (((AiProver:Result $name $index (AiProver:Hints $sets $defs $gdefs $status $trace) $attempts $outcome)
       (let $claim (case $outcome
              (((AiProver:Proved $s $o $l $t $u $a) ($l $t $u $a (if (== $s duper) "duper" "core")))
               ($other (AiRun:NoClaim AiRun:NoClaim () () "core"))))
         (let ($label $tactic $used $axioms $proof-profile) $claim
           (let (AiRun:TraceFields $trace-references $trace-faults)
             (ai-math:run-trace-fields $trace)
           (JsonObject
             ((JsonPair "schema" "ai-math.result.v1")
              (JsonPair "run" $key) (JsonPair "goal" $name)
              (JsonPair "index" $index)
              (JsonPair "outcome" (ai-math:run-outcome $outcome))
              (JsonPair "proved_by" (if (== $label AiRun:NoClaim) JsonNull $label))
              (JsonPair "tactic" (if (== $tactic AiRun:NoClaim) JsonNull $tactic))
              (JsonPair "proof_profile" (if (== $tactic AiRun:NoClaim) JsonNull $proof-profile))
              (JsonPair "used" (JsonArray (map-atom $used $item $item)))
              (JsonPair "axioms" (JsonArray (map-atom $axioms $item $item)))
              (JsonPair "vampire" $status)
              (JsonPair "premises" (JsonArray (map-atom (car-atom $sets) $item $item)))
              (JsonPair "premise_sets" (JsonArray (map-atom $sets $set
                (JsonArray (map-atom $set $item $item)))))
              (JsonPair "defs" (JsonArray (map-atom $defs $item $item)))
              (JsonPair "goal_defs" (JsonArray (map-atom $gdefs $item $item)))
              (JsonPair "solver_traces" (JsonArray $trace-references))
              (JsonPair "solver_trace_faults" (JsonArray $trace-faults))
              (JsonPair "nanoseconds" $nanoseconds)
              (JsonPair "evidence" (repr $result))))))))
      ($other (AiRun:Fault invalid-controller-result $other)))))
(= (ai-math:run-unique-object $row)
   (case $row
     (((JsonObject $pairs)
       (let $keys (ai-math:itp-json-keys $pairs)
         (and (== (size-atom $keys) (size-atom (unique-atom $keys)))
           (foldl-atom $keys true $ok $key (and $ok (== (get-type $key) String))))))
      ($other false))))
(= (ai-math:run-goal-valid (AiProver $search $thf (AiITP $catalog $root $lean $profile) $vampire $options) $row)
   (case ((json:get $row "goal") (json:get $row "index"))
     ((($name $ordinal)
       (if (and (== (get-type $name) String)
                (ai-math:itp-natural $ordinal))
         (case (ai-math:get $catalog $name AiMissing)
           (((AiITP:Declaration $i THM) (== $ordinal $i)) ($other false)))
         false))
      ($other false))))
(= (ai-math:run-record-valid $context $key $row)
   (and (ai-math:run-unique-object $row)
     (and (== (json:get $row "schema") "ai-math.result.v1")
       (and (== (json:get $row "run") $key)
         (and (ai-math:run-goal-valid $context $row)
           (let $outcome (json:get $row "outcome")
             (if (== $outcome "proved")
               (let* (($tactic (json:get $row "tactic"))
                      ($label (json:get $row "proved_by"))
                      ($profile (json:get $row "proof_profile")))
                 (and (== (get-type $tactic) String)
                   (and (== (get-type $label) String)
                     (and (== (get-type $profile) String)
                          (ai-math:contains ("core" "duper") $profile)))))
               (and (== (get-type $outcome) String)
                    (ai-math:contains ("not-proved" "unfinished" "fault") $outcome)))))))))
(= (ai-math:run-scan-line $context $key $store $state $line)
   (case $state
     (((AiRun:Scanned $header $issues)
       (if (== (str:trim $line) "") $state
         (let $row (json:parse $line)
           (if (and (ai-math:run-unique-object $row)
                    (== (json:get $row "schema") "ai-math.run.v1"))
             (if (and (not $header) (== (json:get $row "run") $key))
               (AiRun:Scanned true $issues) (AiRun:Fault incompatible-run $row))
             (if (and $header (ai-math:run-record-valid $context $key $row))
               (let $stored (ai-math:put $store (json:get $row "goal")
                              (AiRun:Saved $row)) $state)
               (AiRun:Scanned $header (cons-atom (AiRun:IgnoredLine (str:sha256 $line)) $issues)))))))
      ($other $state))))
(= (ai-math:run-option-identity $option)
   (case $option
     (((trace-directory $path) (trace-policy SuccessfulSolverEvidenceV1))
      ($other $other))))
(= (ai-math:run-options-identity $options)
   (map-atom $options $option (ai-math:run-option-identity $option)))
(= (ai-math:run-effective-options $root $options)
   (AiRun:EffectiveOptions (ai-math:run-options-identity $options)
     (ai-math:prover-stages-at $root $options)))
(= (ai-math:run-open-prepared $context $corpus $path $toolchain $mode)
   (let (AiProver $search $thf (AiITP $catalog $root $lean $profile) $vampire $options) $context
     (ai-math:run-open-identity $context $path $mode
       (ai-math:run-descriptor $root $corpus (ai-math:run-effective-options $root $options) $toolchain))))
(= (ai-math:run-open-identity $context $path $mode $identity)
     (case $identity
       (((AiRun:Identity $key $descriptor)
         (let $store (new-space)
           (case $mode
             ((Fresh (if (fs:exists $path) (AiRun:Request existing-log $path)
               (let $written (fs:write $path (str:concat (json:stringify
                        (ai-math:run-header (AiRun:Identity $key $descriptor))) "\n"))
                 (if (== $written ()) (AiRun $context $path $key $store ()) (AiRun:Fault log-write $written)))))
              (Resume
               (case (fs:read-lines $path)
                 (((Error $why $where) (AiRun:Fault log-read ($why $where)))
                  ($lines
                   (case (foldl-atom $lines (AiRun:Scanned false ()) $state $line
                           (ai-math:run-scan-line $context $key $store $state $line))
                     (((AiRun:Scanned true $issues) (AiRun $context $path $key $store (list:reverse $issues)))
                      ((AiRun:Scanned false $issues) (AiRun:Fault missing-run-header $issues))
                      ($other $other)))))))
              ($other (AiRun:Request log-mode $mode))))))
        ($other $other))))
(= (ai-math:run-open $context $corpus $path $toolchain $mode)
   (case $context
     (((AiProver $search $thf $itp $vampire $options)
       (ai-math:run-open-prepared $context $corpus $path $toolchain $mode))
      ($other $other))))
(= (ai-math:run-reusable (AiProver $search $thf $itp $vampire $options) $row $budget)
   (case (json:get $row "outcome")
     (("not-proved" AiRun:Completed)
      ("proved"
       (case (json:get $row "proof_profile")
         (($profile
           (if (ai-math:contains ("core" "duper") $profile)
             (case (ai-math:itp-check-with
                     (ai-math:itp-select-profile $itp (str:string->symbol $profile))
                     (json:get $row "goal")
                     (json:get $row "tactic") $budget)
               (((AiITP:Accepted $n $used $axioms) (AiRun:Rechecked $used $axioms))
                ($checked-other (AiRun:Retry $checked-other))))
             (AiRun:Retry invalid-proof-profile)))
          ($missing-profile (AiRun:Retry missing-proof-profile)))))
      ($other (AiRun:Retry $other)))))
(= (ai-math:run-rechecked-row (JsonObject $fields) $used $axioms)
   (JsonObject (union-atom
     (filter-atom $fields $field (not (ai-math:contains ("used" "axioms" "resume_check") (index-atom $field 1))))
     ((JsonPair "used" (JsonArray (map-atom $used $name $name)))
      (JsonPair "axioms" (JsonArray (map-atom $axioms $name $name)))
      (JsonPair "resume_check" "kernel-and-source-order")))))
(= (ai-math:run-publish (AiRun $context $path $key $store $issues) $target $row)
     (case $row
       (((JsonObject $fields)
         (if (and (== (json:get $row "goal") $target)
                  (ai-math:run-record-valid $context $key $row))
           (let $written (fs:append-text $path (str:join "" ("\n" (json:stringify $row) "\n")))
             (if (== $written ())
               (let $stored (ai-math:put $store $target $row) (AiRun:Recorded $target $row))
               (AiRun:Fault log-append ($target $written))))
           (AiRun:Fault invalid-result-row $target)))
        ($other $other))))
(= (ai-math:run-fresh $owner $target)
   (let* (($context (index-atom $owner 1)) ($key (index-atom $owner 3))
          ($start (system:monotonic-ns)) ($result (ai-math:prove $context $target))
          ($elapsed (- (system:monotonic-ns) $start)))
     (ai-math:run-publish $owner $target (ai-math:run-result $key $elapsed $result))))
(= (ai-math:run-resume $owner $target $resume-budget)
   (case $owner
     (((AiRun $context $path $key $store $issues)
       (let* (($entry (ai-math:get $store $target AiRun:Missing))
              ($old (case $entry (((AiRun:Saved $saved-record) $saved-record) ($other $other)))))
         (if (== $old AiRun:Missing) AiRun:NeedsWork
           (case (ai-math:run-reusable $context $old $resume-budget)
             ((AiRun:Completed
               (let $stored (ai-math:put $store $target $old) (AiRun:Reused $target completed $old)))
              ((AiRun:Rechecked $used $axioms)
               (let* (($refreshed (ai-math:run-rechecked-row $old $used $axioms))
                      ($stored (ai-math:put $store $target $refreshed))) (AiRun:Reused $target rechecked $refreshed)))
              ($other AiRun:NeedsWork))))))
      ($other $other))))
(= (ai-math:run-one $owner $target $resume-budget)
   (case (ai-math:run-resume $owner $target $resume-budget)
     ((AiRun:NeedsWork (ai-math:run-fresh $owner $target)) ($other $other))))
(= (ai-math:run-targets $context $stride)
   (ai-math:run-targets-shard $context $stride 0))
(= (ai-math:run-targets-shard
      (AiProver (AiSearch $count $facts $weights $training) $thf $itp $vampire $options)
      $stride $shard)
   (if (and (ai-math:itp-natural $stride) (> $stride 0))
     (if (and (ai-math:itp-natural $shard) (< $shard $stride))
       (let $targets (sort-atom (collapse (match $facts
                        (AiSearchItem $i (AiSearchFact $i THM $name $syms $deps $features)) ($i $name))))
         (let (AiRun:Targets $position $selected)
           (foldl-atom $targets (AiRun:Targets 0 ()) $state $entry
             (let (AiRun:Targets $ordinal $out) $state
               (AiRun:Targets (+ $ordinal 1)
                 (if (== (% $ordinal $stride) $shard)
                   (cons-atom (index-atom $entry 1) $out) $out))))
           (list:reverse $selected)))
       (AiRun:Request shard ($shard $stride)))
     (AiRun:Request stride $stride)))
(= (ai-math:run-summary $owner)
   (case $owner
     (((AiRun $context $path $key $store $issues)
       (let $rows (collapse (match $store (AiEntry $name (JsonObject $fields)) (JsonObject $fields)))
         (AiRun:Summary $key (size-atom $rows)
           (map-atom ("proved" "not-proved" "unfinished" "fault") $kind
             ($kind (size-atom (filter-atom $rows $row (== (json:get $row "outcome") $kind))))) $issues)))
      ($other $other))))
(= (ai-math:run-step $owner $budget $state $target)
   (if (== $state AiRun:Running)
     (let $result (ai-math:run-one $owner $target $budget)
       (let $printed (println! $result)
         (case $result
           (((AiRun:Recorded $n $row) AiRun:Running)
            ((AiRun:Reused $n $kind $row) AiRun:Running) ($other $other))))) $state))
(= (ai-math:run $owner $targets $resume-budget)
   (case $owner
     (((AiRun $context $path $key $store $issues)
       (let $completed (foldl-atom $targets AiRun:Running $state $target
                         (ai-math:run-step $owner $resume-budget $state $target))
         (if (== $completed AiRun:Running) (ai-math:run-summary $owner) $completed)))
      ($other $other))))

; Worker stdout is a small completion protocol. Full evidence stays in its
; owned journal and a fresh snapshot; it is not copied through a pipe.
(= (ai-math:run-quiet $owner $targets $resume-budget)
   (case $owner
     (((AiRun $context $path $key $store $issues)
       (let $completed (foldl-atom $targets AiRun:Running $state $target
           (if (== $state AiRun:Running)
             (case (ai-math:run-one $owner $target $resume-budget)
               (((AiRun:Recorded $n $row) AiRun:Running)
                ((AiRun:Reused $n $kind $row) AiRun:Running) ($other $other))) $state))
         (if (== $completed AiRun:Running) (ai-math:run-summary $owner) $completed)))
      ($other $other))))
