; Lean proof attempts and source-order acceptance for PeTTa 1.0.6.
; Import library.metta, proc, json, system and this file at the entry point.
; No proposed statement or tactic is interpolated into a Lean command.

(= (ai-math:itp $declarations $application-root $lean)
   (let* (($root (fs:canonical-path $application-root))
          ($index (new-space))
          ($indexed (map-atom $declarations $declaration
            (let (Decl $i $kind $name $hash $s $b $ss $ds $fs) $declaration
              (ai-math:put $index $name (AiITP:Declaration $i $kind)))))
          ($library (str:concat $root "/lib")))
     (if (and (fs:exists (str:concat $library "/CettaITP.olean"))
              (and (fs:exists (str:concat $library "/CettaITPGuard.olean"))
                (and (fs:exists (str:concat $library "/CettaProofTactics.olean"))
                (and (fs:exists (str:concat $library "/Bridge.olean"))
                     (fs:exists (str:concat $library "/MegLib.olean"))))))
       (let $runtime (ai-math:itp-execution $root $lean)
         (case $runtime
           ((AiITP:Interpreted
             (let $stored (ai-math:put $index (AiITPRuntime $root $lean) $runtime)
               (AiITP $index $root $lean core)))
            ((AiITP:Native $guard $worker $prefix $prepared-library)
             (let $stored (ai-math:put $index (AiITPRuntime $root $lean) $runtime)
               (AiITP $index $root $lean core)))
            ($other $other))))
       (AiITP:PreparationNeeded $root))))

(= (ai-math:itp-execution $root $lean)
   (case (system:getenv-or-default "CETTA_ITP_RUNTIME" "interpreted")
     (("interpreted" AiITP:Interpreted)
      ("native" (ai-math:itp-native-execution $root $lean))
      ($other (AiITP:InterpretationRequest runtime $other)))))
(= (ai-math:itp-runtime (AiITP $index $root $lean $profile))
   (ai-math:get $index (AiITPRuntime $root $lean) AiITP:Interpreted))
(= (ai-math:itp-complete-process-text $observation)
   (case $observation
     (((proc:result (proc:exited 0) proc:normal $out $err
         (proc:capture $out-seen $out-kept $err-seen $err-kept proc:eof proc:eof
           (proc:input $input-size $input-sent)))
       (if (and (== $out-seen $out-kept)
                (and (== $err-seen $err-kept) (== $input-size $input-sent)))
         (AiITP:ProcessText $out) (AiITP:Fault "" preparation-capture $observation)))
      ($other (AiITP:Fault "" preparation-process $observation)))))
; Make owns native build dependencies. Runtime uses the compiled bundle and
; checks its compiler installation, not mutable Lean source fingerprints.
(= (ai-math:itp-native-execution $root $lean)
   (let $directory (str:concat $root "/.cetta/lean-native")
     (if (foldl-atom ("itp-guard" "itp-worker" "sysroot.txt"
                     "lib/MegLib.olean" "lib/Bridge.olean" "lib/CettaProofTactics.olean"
                     "lib/CettaITP.olean" "lib/CettaProposalView.olean" "lib/CettaITPGuard.olean") true $ok $file
           (and $ok (fs:exists (str:join "/" ($directory $file)))))
       (case (ai-math:itp-complete-process-text
               (proc:run ($lean "--print-prefix") ((cwd $root))))
         (((AiITP:ProcessText $prefix)
           (if (== (str:trim $prefix) (str:trim (fs:read-text (str:concat $directory "/sysroot.txt"))))
             (AiITP:Native (str:concat $directory "/itp-guard")
               (str:concat $directory "/itp-worker") (str:trim $prefix)
               (str:concat $directory "/lib"))
             (AiITP:PreparationNeeded $root native-toolchain)))
          ($other $other)))
       (AiITP:PreparationNeeded $root native))))

(= (ai-math:itp-profile-name (AiITP $index $root $lean $profile)) (str:symbol->string $profile))
(= (ai-math:itp-library (AiITP $index $root $lean $profile))
   (case (ai-math:itp-runtime (AiITP $index $root $lean $profile))
     (((AiITP:Native $guard $worker $prefix $library) $library)
      ($other (str:concat $root "/lib")))))
(= (ai-math:itp-lean-path (AiITP $index $root $lean $profile))
   (str:join ":" (cons-atom (ai-math:itp-library (AiITP $index $root $lean $profile))
     (if (== $profile duper)
       (map-atom ("Duper" "auto" "batteries") $package
         (str:join "" ($root "/tools/duper-env/.lake/packages/" $package "/.lake/build/lib/lean"))) ()))))
(= (ai-math:itp-duper-prepared $root)
   (fs:exists (str:concat $root "/tools/duper-env/.lake/packages/Duper/.lake/build/lib/lean/Duper.olean")))
(= (ai-math:itp-select-profile (AiITP $index $root $lean $previous) $profile)
   (case $profile
     ((core (AiITP $index $root $lean core))
      (duper (if (ai-math:itp-duper-prepared $root)
               (AiITP $index $root $lean duper) (AiITP:PreparationNeeded $root duper)))
      ($other (AiITP:InterpretationRequest profile $other)))))

(= (ai-math:itp-bridges)
   ("b_True" "b_False" "b_not" "b_and" "b_or" "b_iff" "b_eq" "b_neq" "b_ex"))

; These are the permitted core axioms, not a whitelist of name prefixes.
; Megalodon parameters/axioms additionally have to precede the target.
(= (ai-math:itp-core-axioms) ("propext" "Classical.choice" "Quot.sound"))

; Resource counts have a natural-number wire representation. Validate before
; launching a process, including its wall timeout, rather than relying on a
; backend to coerce a malformed count or silently remove a limit.
(= (ai-math:itp-natural $value)
   (ai-math:natural $value))
(= (ai-math:itp-budget-valid $budget)
   (case $budget
     (((AiITP:Budget $wall $heartbeats $recursion)
       (and (ai-math:itp-natural $wall)
         (and (ai-math:itp-natural $heartbeats) (ai-math:itp-natural $recursion))))
      ($other false))))

(= (ai-math:itp-name-order (AiITP $index $root $lean $profile) $target-index $name)
   (if (str:starts-with $name "Megalodon.")
     (let $short (str:byte-slice $name 10 (str:byte-length $name))
       (if (or (== $short "set") (ai-math:contains (ai-math:itp-bridges) $short))
         true
         (let $base (car-atom (str:split "." $short))
           (case (ai-math:get $index $short (ai-math:get $index $base AiMissing))
             (((AiITP:Declaration $i $kind) (< $i $target-index))
              ($other false))))))
     true))

(= (ai-math:itp-axiom (AiITP $index $root $lean $profile) $target-index $name)
   (if (ai-math:contains (ai-math:itp-core-axioms) $name) true
     (if (== $name "Megalodon.set") true
       (if (str:starts-with $name "Megalodon.")
         (let $short (str:byte-slice $name 10 (str:byte-length $name))
           (case (ai-math:get $index $short AiMissing)
             (((AiITP:Declaration $i $kind)
               (and (< $i $target-index) (ai-math:contains (PARAM PRIM AXIOM) $kind)))
              ($other false))))
         false))))

(= (ai-math:itp-check $context $target $tactic)
   (ai-math:itp-check-with $context $target $tactic (AiITP:Budget 0 0 0)))

; The budget is (wall milliseconds, Lean heartbeats, recursion depth).
; Zero is unbounded. Exhaustion is unfinished, never an invalid proof.
(= (ai-math:itp-check-with $context $target $tactic $budget)
   (if (ai-math:itp-budget-valid $budget)
     (ai-math:itp-request $context $target "check" $tactic $budget)
     (AiITP:Fault $target invalid-budget $budget)))

(= (ai-math:itp-check-program-with $context $target $helpers $tactic $budget)
   (if (and (== (get-type $helpers) String) (== (get-type $tactic) String))
     (if (ai-math:itp-budget-valid $budget)
       (ai-math:itp-request $context $target "check" $tactic $budget $helpers)
       (AiITP:Fault $target invalid-budget $budget))
     (AiITP:Fault $target invalid-proof-program ($helpers $tactic))))

(= (ai-math:itp-statement $context $target)
   (ai-math:itp-request $context $target "statement" "" (AiITP:Budget 0 0 0)))

; Load all requested theorem signatures with one Lean import, into an ordinary
; indexed space. These are display types for advice, never trusted inputs to
; proof checking. Each proof still checks against the actual imported type.
(= (ai-math:itp-theorems (AiITP $index $root $lean $profile))
   (map-atom (sort-atom
      (collapse (match $index (AiEntry $name (AiITP:Declaration $i THM)) ($i $name))))
     $entry (index-atom $entry 1)))

(= (ai-math:itp-load-statements $context)
   (case $context
     (((AiITP $index $root $lean $profile) (ai-math:itp-statement-catalog $context))
      ($other $other))))

(= (ai-math:itp-statement-catalog $context)
   (ai-math:itp-send $context "" 0 "statements"
     (json:stringify (JsonObject
       ((JsonPair "schema" "ai-math.itp.v1")
        (JsonPair "target" "")
        (JsonPair "operation" "statements")
        (JsonPair "profile" (ai-math:itp-profile-name $context))
        (JsonPair "heartbeats" 0)
        (JsonPair "recursion" 0)
        (JsonPair "targets" (JsonArray
          (map-atom (ai-math:itp-theorems $context) $name $name)))))) 0))

(= (ai-math:itp-signature (AiITP:Statements $space) $name)
   (ai-math:get $space $name (AiITP:MissingStatement $name)))

(= (ai-math:itp-send $context $target $index $operation $input $milliseconds)
   (case $context
     (((AiITP $catalog $root $lean $profile)
       (ai-math:itp-observation $context $target $index $operation
         (proc:run (ai-math:itp-command $context)
           ((lifetime owner) (cwd $root) (stdin $input) (timeout-ms $milliseconds)))))
      ($other $other))))
(= (ai-math:itp-command (AiITP $catalog $root $lean $profile))
   (let $context (AiITP $catalog $root $lean $profile)
     (case (ai-math:itp-runtime $context)
       (((AiITP:Native $guard $worker $prefix $library)
         ("env" (str:concat "LEAN_PATH=" (ai-math:itp-lean-path $context))
          (str:concat "LEAN_SYSROOT=" $prefix) $guard "--worker" $worker))
        ($other
         ("env" (str:concat "LEAN_PATH=" (ai-math:itp-lean-path $context))
          $lean "--run" (str:concat $root "/phase1/itp_guard.lean")
          $lean (str:concat $root "/phase1/itp_driver.lean")))))))

(= (ai-math:itp-request $context $target $operation $tactic $budget)
   (ai-math:itp-request $context $target $operation $tactic $budget ""))
(= (ai-math:itp-request $context $target $operation $tactic $budget $helpers)
   (case $context
     (((AiITP $index $root $lean $profile)
       (case (ai-math:get $index $target AiMissing)
         (((AiITP:Declaration $i THM)
           (case $budget
             (((AiITP:Budget $milliseconds $heartbeats $recursion)
               (let $input (json:stringify
                 (JsonObject
                   (union-atom ((JsonPair "schema" "ai-math.itp.v1")
                    (JsonPair "target" $target)
                    (JsonPair "operation" $operation)
                    (JsonPair "profile" (ai-math:itp-profile-name $context))
                    (JsonPair "tactic" $tactic)
                    (JsonPair "heartbeats" $heartbeats)
                    (JsonPair "recursion" $recursion))
                    (if (== $helpers "") () ((JsonPair "prelude" $helpers))))))
                 (ai-math:itp-send $context $target $i $operation $input $milliseconds)))
              ($other (AiITP:Fault $target invalid-budget $budget)))))
          ($other (AiITP:Rejected $target unknown-theorem $other)))))
      ($other $other))))

(= (ai-math:itp-observation $context $target $index $operation $observation)
   (case $observation
     (((proc:result (proc:exited 0) proc:normal $stdout $stderr
         (proc:capture $out-seen $out-kept $err-seen $err-kept proc:eof proc:eof
           (proc:input $input-size $input-sent)))
       (if (and (== $out-seen $out-kept)
                (and (== $err-seen $err-kept) (== $input-size $input-sent)))
         (ai-math:itp-decode $context $target $index $operation (json:parse $stdout))
         (AiITP:Unfinished $target incomplete-capture $observation)))
      ((proc:result $termination proc:timed-out $out $err $capture)
       (AiITP:Unfinished $target deadline $observation))
      ((proc:result $termination proc:cancelled $out $err $capture)
       (AiITP:Unfinished $target cancelled $observation))
      ($other (AiITP:Fault $target process $observation)))))

(= (ai-math:itp-json-keys $pairs)
   (map-atom $pairs $pair
     (case $pair (((JsonPair $key $value) $key) ($other AiITP:InvalidKey)))))

(= (ai-math:itp-decode $context $target $index $operation $reply)
   (case $reply
     (((JsonObject $pairs)
       (let $keys (ai-math:itp-json-keys $pairs)
         (if (and (== (size-atom $keys) (size-atom (unique-atom $keys)))
                  (foldl-atom $keys true $ok $key (and $ok (== (get-type $key) String))))
           (ai-math:itp-response $context $target $index $operation $reply)
           (AiITP:Fault $target duplicate-or-invalid-json-key $reply))))
      ($other (AiITP:Fault $target protocol $reply)))))

(= (ai-math:itp-response $context $target $index $operation $reply)
   (if (and (== (json:get $reply "schema") "ai-math.itp.v1")
            (== (json:get $reply "target") $target))
     (case (json:get $reply "kind")
       (("checked"
         (if (== $operation "check")
           (ai-math:itp-checked $context $target $index
             (json:get $reply "used") (json:get $reply "axioms"))
           (AiITP:Fault $target wrong-operation $reply)))
        ("statement"
         (if (== $operation "statement")
           (case (json:get $reply "statement")
             (($text (if (== (get-type $text) String)
                       (AiITP:Statement $target $text)
                       (AiITP:Fault $target invalid-statement $reply)))
              ($other (AiITP:Fault $target missing-statement $reply))))
           (AiITP:Fault $target wrong-operation $reply)))
        ("statements"
         (if (== $operation "statements")
           (ai-math:itp-statements-ready $context (json:get $reply "statements"))
           (AiITP:Fault $target wrong-operation $reply)))
        ("batch"
         (case $operation
           (((AiITP:BatchRequest $candidates)
             (ai-math:itp-batch-ready $context $target $index $candidates
               (json:get $reply "attempts")))
            ($other (AiITP:Fault $target wrong-operation $reply)))))
        ("case-checked"
         (case $operation
           (((AiITP:CaseRequest $case)
             (if (== (json:get $reply "case") $case)
               (case (json:get $reply "caseCount")
                 (($count
                     (if (and (ai-math:itp-natural $count) (> $count $case))
                       (case (ai-math:itp-checked $context $target $index
                               (json:get $reply "used") (json:get $reply "axioms"))
                         (((AiITP:Accepted $n $used $axioms) (AiITP:CaseAccepted $target $case $count $used $axioms))
                          ($other $other)))
                       (AiITP:Fault $target invalid-case-count $reply)))
                  ($other (AiITP:Fault $target missing-case-count $reply))))
               (AiITP:Fault $target case-identity $reply)))
            ($other (AiITP:Fault $target wrong-operation $reply)))))
        ("case-batch"
         (case $operation
           (((AiITP:CaseBatchRequest $candidates)
             (ai-math:itp-case-batch-ready $context $target $index $candidates
               (json:get $reply "attempts")))
            ($other (AiITP:Fault $target wrong-operation $reply)))))
        ("context"
         (case $operation
           (((AiITP:ContextRequest $premises $definitions)
             (ai-math:itp-context-ready $target $premises $definitions $reply))
            ($other (AiITP:Fault $target wrong-operation $reply)))))
        ("rejected"
         (AiITP:Rejected $target (json:get $reply "reason") $reply))
        ("unfinished"
         (AiITP:Unfinished $target (json:get $reply "reason") $reply))
        ($other (AiITP:Fault $target runner $reply))))
     (AiITP:Fault $target response-identity $reply)))

(= (ai-math:itp-statements-ready $context $value)
   (case $value
     (((JsonArray $rows)
       (let $decoded (map-atom $rows $row
          (case $row
            (((JsonArray ($name $text))
              (AiITP:Signature $name $text))
             ($other AiITP:InvalidSignature))))
         (if (foldl-atom $decoded true $ok $row
               (and $ok (case $row
                 (((AiITP:Signature $name $text)
                   (and (== (get-type $name) String) (== (get-type $text) String)))
                  ($other false)))))
           (let $names (map-atom $decoded $row (index-atom $row 1))
             (if (== (sort-atom $names) (sort-atom (ai-math:itp-theorems $context)))
               (let $space (new-space)
                 (let $stored (map-atom $decoded $row
                   (let (AiITP:Signature $name $text) $row (ai-math:put $space $name $text)))
                   (AiITP:Statements $space)))
               (AiITP:Fault "" statement-domain $value)))
           (AiITP:Fault "" invalid-statement $value))))
      ($other (AiITP:Fault "" missing-statements $value)))))

(= (ai-math:itp-string-array $values)
   (foldl-atom $values true $ok $value
     (and $ok (== (get-type $value) String))))

(= (ai-math:itp-checked $context $target $index $used $axioms)
   (case ($used $axioms)
     ((((JsonArray $dependencies) (JsonArray $assumptions))
       (if (and (ai-math:itp-string-array $dependencies) (ai-math:itp-string-array $assumptions))
         (let* (($names (map-atom $dependencies $name $name))
                ($axiom-names (map-atom $assumptions $name $name))
                ($forbidden (filter-atom $names $name
                  (not (ai-math:itp-name-order $context $index $name))))
                ($untrusted (filter-atom $axiom-names $name
                  (not (ai-math:itp-axiom $context $index $name)))))
           (if (== $forbidden ())
             (if (== $untrusted ())
               (AiITP:Accepted $target $names $axiom-names)
               (AiITP:Rejected $target untrusted-axioms $untrusted))
             (AiITP:Rejected $target source-order $forbidden)))
         (AiITP:Fault $target invalid-dependency-array ($used $axioms))))
      ($other (AiITP:Fault $target missing-dependencies ($used $axioms))))))

; A batch is an ordered sequence of candidate occurrences. Equal labels do
; not identify occurrences. Importing once does not share proof environments.
(= (ai-math:itp-candidates-valid $candidates)
   (if (== (get-metatype $candidates) Expression)
     (foldl-atom $candidates true $ok $candidate
       (and $ok (case $candidate
         (((AiITP:Candidate $label $tactic)
           (and (== (get-type $label) String) (== (get-type $tactic) String)))
          ($other false)))))
     false))
(= (ai-math:itp-batch $context $target $candidates)
   (ai-math:itp-batch-with $context $target $candidates (AiITP:Budget 0 0 0)))
(= (ai-math:itp-batch-with $context $target $candidates $budget)
   (case $context
     (((AiITP $index $root $lean $profile)
       (case (ai-math:get $index $target AiMissing)
         (((AiITP:Declaration $i THM)
           (if (ai-math:itp-candidates-valid $candidates)
             (if (ai-math:itp-budget-valid $budget) (case $budget
               (((AiITP:Budget $milliseconds $heartbeats $recursion)
                 (let $input (json:stringify (JsonObject
                   ((JsonPair "schema" "ai-math.itp.v1")
                    (JsonPair "target" $target)
                    (JsonPair "operation" "batch")
                    (JsonPair "profile" (ai-math:itp-profile-name $context))
                    (JsonPair "heartbeats" $heartbeats)
                    (JsonPair "recursion" $recursion)
                    (JsonPair "candidates" (JsonArray (map-atom $candidates $candidate
                      (let (AiITP:Candidate $label $tactic) $candidate
                        (JsonObject ((JsonPair "label" $label)
                                     (JsonPair "tactic" $tactic))))))))))
                   (ai-math:itp-send $context $target $i
                     (AiITP:BatchRequest $candidates) $input $milliseconds)))
                ($other (AiITP:Fault $target invalid-budget $budget))))
               (AiITP:Fault $target invalid-budget $budget))
             (AiITP:Fault $target invalid-candidates $candidates)))
          ($other (AiITP:Rejected $target unknown-theorem $other)))))
      ($other $other))))
(= (ai-math:itp-batch-ready $context $target $index $candidates $value)
   (case $value
     (((JsonArray $rows)
       (if (== (size-atom $rows) (size-atom $candidates))
         (case (ai-math:itp-batch-rows $context $target $index $candidates $rows 0)
           (((AiITP:Rows $attempts) (AiITP:Batch $target $attempts))
            ($fault $fault)))
         (AiITP:Fault $target batch-domain $value)))
      ($other (AiITP:Fault $target missing-attempts $value)))))
(= (ai-math:itp-batch-rows $context $target $index $candidates $rows $ordinal)
   (if (== $candidates ()) (AiITP:Rows ())
     (let* ((($candidate $more) (decons-atom $candidates))
            ((AiITP:Candidate $label $tactic) $candidate)
            (($row $rest) (decons-atom $rows)))
       (case $row
         (((JsonObject $pairs)
           (let $keys (ai-math:itp-json-keys $pairs)
             (if (and (== (sort-atom $keys) (sort-atom ("index" "label" "result")))
                      (and (== (json:get $row "index")
                               $ordinal)
                           (== (json:get $row "label") $label)))
               (let $result (ai-math:itp-decode $context $target $index "check"
                              (json:get $row "result"))
                 (case (ai-math:itp-batch-rows $context $target $index $more $rest (+ $ordinal 1))
                   (((AiITP:Rows $out) (AiITP:Rows (cons-atom (AiITP:Attempt $label $result) $out)))
                    ($fault $fault))))
               (AiITP:Fault $target batch-row-identity $row))))
          ($other (AiITP:Fault $target invalid-batch-row $row)))))))

; A wall timeout discards the incomplete batch reply, never invents a failed
; proof. Optional isolated retries give later fast proposals their own turn.
; Retry milliseconds bound the retry phase; zero means no bound.
(= (ai-math:itp-batch-resilient $context $target $candidates $batch-budget $single-budget $retry-ms)
   (if (and (ai-math:itp-budget-valid $single-budget) (ai-math:itp-natural $retry-ms))
    (case (ai-math:itp-batch-with $context $target $candidates $batch-budget)
     (((AiITP:Unfinished $name deadline $observation)
       (let $started (system:monotonic-ns)
         (AiITP:Batch $target (ai-math:itp-retry $context $target $candidates
           $single-budget $retry-ms $started false))))
      ($result $result)))
    (AiITP:Fault $target invalid-retry-policy ($single-budget $retry-ms))))
(= (ai-math:itp-retry $context $target $candidates $budget $retry-ms $started $proved)
   (if (== $candidates ()) ()
     (let* ((($candidate $rest) (decons-atom $candidates))
            ((AiITP:Candidate $label $tactic) $candidate))
       (if $proved
         (cons-atom (AiITP:Attempt $label (AiITP:Skipped $target already-proved))
           (ai-math:itp-retry $context $target $rest $budget $retry-ms $started true))
         (let* (($nanoseconds (- (system:monotonic-ns) $started))
                ($elapsed (/ (- $nanoseconds (% $nanoseconds 1000000)) 1000000)))
           (let $result (if (and (> $retry-ms 0) (>= $elapsed $retry-ms))
                           (AiITP:Unfinished $target retry-deadline ())
                           (ai-math:itp-check-with $context $target $tactic
                             (ai-math:itp-retry-budget $budget $retry-ms $elapsed)))
             (cons-atom (AiITP:Attempt $label $result)
               (ai-math:itp-retry $context $target $rest $budget $retry-ms $started
                 (case $result (((AiITP:Accepted $n $u $a) true) ($other false)))))))))))
(= (ai-math:itp-retry-budget (AiITP:Budget $wall $heartbeats $recursion) $retry-ms $elapsed)
   (if (== $retry-ms 0) (AiITP:Budget $wall $heartbeats $recursion)
     (let $remaining (- $retry-ms $elapsed)
       (AiITP:Budget (if (or (== $wall 0) (< $remaining $wall)) $remaining $wall)
         $heartbeats $recursion))))

; A checked case is not a checked target. The Lean runner closes the selected
; subgoal over its local context and kernel-checks that theorem without filling
; any other subgoal. The assembled target must still pass itp-check.
(= (ai-math:itp-case-candidates-valid $candidates)
   (if (== (get-metatype $candidates) Expression)
     (foldl-atom $candidates true $ok $candidate
       (and $ok (case $candidate
         (((AiITP:CaseCandidate $case $label $tactic)
           (and (ai-math:itp-natural $case)
             (and (== (get-type $label) String) (== (get-type $tactic) String))))
          ($other false))))) false))
(= (ai-math:itp-case-batch-with $context $target $prefix $candidates $budget)
   (case $context
     (((AiITP $index $root $lean $profile)
       (if (and (ai-math:itp-budget-valid $budget)
                (and (== (get-type $prefix) String) (ai-math:itp-case-candidates-valid $candidates)))
         (case (ai-math:get $index $target AiMissing)
           (((AiITP:Declaration $i THM)
             (let (AiITP:Budget $milliseconds $heartbeats $recursion) $budget
               (ai-math:itp-send $context $target $i (AiITP:CaseBatchRequest $candidates)
                 (json:stringify (JsonObject
                   ((JsonPair "schema" "ai-math.itp.v1")
                    (JsonPair "target" $target)
                    (JsonPair "operation" "case-batch")
                    (JsonPair "profile" (ai-math:itp-profile-name $context))
                    (JsonPair "prefix" $prefix)
                    (JsonPair "heartbeats" $heartbeats)
                    (JsonPair "recursion" $recursion)
                    (JsonPair "candidates" (JsonArray (map-atom $candidates $candidate
                      (let (AiITP:CaseCandidate $case $label $tactic) $candidate
                        (JsonObject ((JsonPair "case" $case)
                                     (JsonPair "label" $label)
                                     (JsonPair "tactic" $tactic)))))))))) $milliseconds)))
            ($other (AiITP:Rejected $target unknown-theorem $other))))
         (AiITP:Fault $target invalid-case-request ($prefix $candidates $budget))))
      ($other $other))))
(= (ai-math:itp-case-batch-ready $context $target $index $candidates $value)
   (case $value
     (((JsonArray $rows)
       (if (== (size-atom $rows) (size-atom $candidates))
         (case (ai-math:itp-case-rows $context $target $index $candidates $rows 0)
           (((AiITP:Rows $out) (AiITP:CaseBatch $target $out)) ($other $other)))
         (AiITP:Fault $target case-batch-domain $value)))
      ($other (AiITP:Fault $target missing-case-attempts $value)))))
(= (ai-math:itp-case-rows $context $target $index $candidates $rows $ordinal)
   (if (== $candidates ()) (AiITP:Rows ())
     (let* ((($candidate $more) (decons-atom $candidates))
            ((AiITP:CaseCandidate $case $label $tactic) $candidate)
            (($row $rest) (decons-atom $rows)))
       (case $row
         (((JsonObject $pairs)
           (if (and (== (sort-atom (ai-math:itp-json-keys $pairs)) (sort-atom ("index" "label" "result")))
                    (and (== (json:get $row "index") $ordinal)
                         (== (json:get $row "label") $label)))
             (let $result (ai-math:itp-decode $context $target $index (AiITP:CaseRequest $case)
                            (json:get $row "result"))
               (case (ai-math:itp-case-rows $context $target $index $more $rest (+ $ordinal 1))
                 (((AiITP:Rows $out)
                   (AiITP:Rows (cons-atom (AiITP:CaseAttempt $case $label $result) $out)))
                  ($other $other))))
             (AiITP:Fault $target case-batch-row-identity $row)))
          ($other (AiITP:Fault $target invalid-case-batch-row $row)))))))

(= (ai-math:itp-case-batch-resilient $context $target $prefix $candidates $batch $single $retry)
   (if (and (ai-math:itp-budget-valid $single) (ai-math:itp-natural $retry))
     (case (ai-math:itp-case-batch-with $context $target $prefix $candidates $batch)
       (((AiITP:Unfinished $name deadline $detail)
         (let $started (system:monotonic-ns)
           (AiITP:CaseBatch $target
             (ai-math:itp-case-retry $context $target $prefix $candidates $single $retry $started ()))))
        ($other $other)))
     (AiITP:Fault $target invalid-case-retry-policy ($single $retry))))
(= (ai-math:itp-case-retry $context $target $prefix $candidates $budget $retry $started $proved)
   (if (== $candidates ()) ()
     (let* ((($candidate $rest) (decons-atom $candidates))
            ((AiITP:CaseCandidate $case $label $tactic) $candidate)
            ($ns (- (system:monotonic-ns) $started))
            ($elapsed (/ (- $ns (% $ns 1000000)) 1000000))
            ($result
              (if (ai-math:contains $proved $case) (AiITP:Skipped $target case-already-proved)
                (if (and (> $retry 0) (>= $elapsed $retry)) (AiITP:Unfinished $target retry-deadline ())
                  (case (ai-math:itp-case-batch-with $context $target $prefix ($candidate)
                          (ai-math:itp-retry-budget $budget $retry $elapsed))
                    (((AiITP:CaseBatch $n ((AiITP:CaseAttempt $c $l $answer))) $answer)
                     ($other $other))))))
            ($next (case $result
              (((AiITP:CaseAccepted $n $c $count $used $axioms) (unique-atom (union-atom $proved ($case))))
               ($other $proved)))))
       (cons-atom (AiITP:CaseAttempt $case $label $result)
         (ai-math:itp-case-retry $context $target $prefix $rest $budget $retry $started $next)))))

; Prompt context is display data only. Facts expose types; only actual
; earlier definitions expose values. No theorem proof body is requested.
(= (ai-math:itp-context-rows $names $rows)
   (if (== $names ()) (if (== $rows ()) (AiITP:ContextRows ()) AiITP:BadContextRows)
     (if (== $rows ()) AiITP:BadContextRows
       (let* ((($name $more) (decons-atom $names)) (($row $rest) (decons-atom $rows)))
         (case $row
           (((JsonArray ($same $text))
             (if (and (== $name $same)
                      (and (== (get-type $same) String)
                           (== (get-type $text) String)))
               (case (ai-math:itp-context-rows $more $rest)
                 (((AiITP:ContextRows $out) (AiITP:ContextRows (cons-atom (AiITP:ContextText $name $text) $out)))
                  ($other $other))) AiITP:BadContextRows))
            ($other AiITP:BadContextRows)))))))
(= (ai-math:itp-context-ready $target $premises $definitions $reply)
   (case ((json:get $reply "statement") (json:get $reply "facts") (json:get $reply "definitions"))
     ((($statement (JsonArray $facts) (JsonArray $defs))
       (if (== (get-type $statement) String)
         (case ((ai-math:itp-context-rows $premises $facts)
                (ai-math:itp-context-rows $definitions $defs))
           ((((AiITP:ContextRows $fact-texts)
              (AiITP:ContextRows $definition-texts))
             (AiITP:PromptContext
               $target $statement $definition-texts $fact-texts))
            ($other (AiITP:Fault $target context-identity $reply))))
         (AiITP:Fault $target context-shape $reply)))
      ($other (AiITP:Fault $target context-shape $reply)))))
(= (ai-math:itp-context-names $context $index $names $definitions)
   (if (== (get-metatype $names) Expression)
     (foldl-atom $names true $ok $name
       (and $ok (if (== (get-type $name) String)
         (and (ai-math:itp-name-order $context $index (str:concat "Megalodon." $name))
           (if $definitions
             (case (ai-math:get (index-atom $context 1) $name AiMissing)
               (((AiITP:Declaration $i DEF) true) ($other false))) true)) false))) false))
(= (ai-math:itp-prompt-context $context $target $premises $definitions $budget)
   (case $context
     (((AiITP $catalog $root $lean $profile)
       (case (ai-math:get $catalog $target AiMissing)
         (((AiITP:Declaration $index THM)
           (if (and (ai-math:itp-budget-valid $budget)
                    (and (ai-math:itp-context-names $context $index $premises false)
                         (ai-math:itp-context-names $context $index $definitions true)))
             (let (AiITP:Budget $wall $heartbeats $recursion) $budget
               (ai-math:itp-send $context $target $index (AiITP:ContextRequest $premises $definitions)
                 (json:stringify (JsonObject
                   ((JsonPair "schema" "ai-math.itp.v1")
                    (JsonPair "target" $target) (JsonPair "operation" "context")
                    (JsonPair "profile" (ai-math:itp-profile-name $context))
                    (JsonPair "heartbeats" $heartbeats)
                    (JsonPair "recursion" $recursion)
                    (JsonPair "premises" (JsonArray (map-atom $premises $name $name)))
                    (JsonPair "definitions" (JsonArray (map-atom $definitions $name $name)))))) $wall))
             (AiITP:Rejected $target invalid-prompt-context ())))
          ($other (AiITP:Rejected $target unknown-theorem $other)))))
      ($other $other))))
