; Shared dispatch and checkpointing for native experimental algorithms.
; Proof journals reuse the ordinary independent-witness resume boundary.
; Observation artifacts are labelled separately and confer no proof authority.
(= (ai-math:research-sources)
   ("phase1/prop_synth.metta" "phase1/research_strategies.metta" "phase1/proof_state.metta"
    "phase1/incremental.metta" "phase1/alternative_atp.metta" "phase1/proof_plans.metta"
    "phase1/decomposition.metta" "phase1/oracle_chains.metta" "phase1/hybrid_induction.metta"
    "phase1/embedding_python.metta" "phase1/research_analysis.metta" "phase1/research.metta" "phase1/research_main.metta"
    "phase1/llm.metta" "phase1/llm_transport.metta" "phase1/llm_ledger.metta" "phase1/http_transport.metta"
    "phase1/lean_export.metta" "phase1/proof_advice.metta"))
(= (ai-math:research-hints $context $target $options)
   (let* (((AiProver $search $thf $itp $vampire $policy) $context)
          ($index (index-atom (ai-math:get (index-atom $itp 1) $target AiMissing) 1)))
     (if (not (== (ai-math:option $policy slices (16 32 64 128 256 512)) ())) (ai-math:prover-hints $context $target)
       (let* (($ranked (ai-math:entry-names (ai-math:rank $search $index (ai-math:option $options premise-limit 96))))
              ($facts (filter-atom $ranked $name
                (case (ai-math:get (index-atom $itp 1) $name AiMissing)
                  (((AiITP:Declaration $i $kind) (ai-math:contains (THM AXIOM) $kind)) ($other false)))))
              ($defs (ai-math:prover-goal-defs $thf (ai-math:search-goal $search $index))))
         (AiProver:Hints ($facts) $defs $defs "search-only" ())))))
(= (ai-math:research-checked $context $target $mode $hints $script $answer $evidence)
   (let $index (index-atom (ai-math:get (index-atom (index-atom $context 3) 1) $target AiMissing) 1)
     (AiProver:Result $target $index $hints ($evidence)
       (case $answer
         (((AiITP:Accepted $n $used $axioms) (AiProver:Proved $mode 0 (str:symbol->string $mode) $script $used $axioms))
          ((AiITP:Unfinished $n $why $detail) (AiProver:Unfinished ($answer)))
          ((AiITP:Fault $n $why $detail) (AiProver:Faulted ($answer)))
          ((AiITP:Rejected $n $why $detail) (AiProver:NotProved (AiProver:Coverage ($mode))))
          ((AiPlan:NotProved $trace $why) (AiProver:NotProved (AiProver:Coverage ($mode))))
          ((AiDerived:NotProved $trace) (AiProver:NotProved (AiProver:Coverage ($mode))))
          (AiDerived:NoProof (AiProver:NotProved (AiProver:Coverage ($mode))))
          ((AiHybrid:NotProved $trace) (AiProver:NotProved (AiProver:Coverage ($mode))))
          (AiResearch:NoCandidate (AiProver:NotProved (AiProver:Coverage ($mode))))
          (AiProp:NoProof (AiProver:NotProved (AiProver:Coverage ($mode))))
          ((AiPlan:Unfinished $trace $why) (AiProver:Unfinished ($answer)))
          ((AiDerived:Unfinished $trace) (AiProver:Unfinished ($answer)))
          ((AiHybrid:Unfinished $trace) (AiProver:Unfinished ($answer)))
          ($other (AiProver:Faulted ($other))))))))
(= (ai-math:research-zipper $context $target $hints $options)
   (let* (((AiProver $search $thf $itp $vampire $policy) $context)
          ($index (index-atom (ai-math:get (index-atom $itp 1) $target AiMissing) 1))
          ($ranked (ai-math:entry-names (ai-math:rank $search $index (ai-math:option $options premise-limit 96))))
          ($problem (ai-math:thf-problem $thf $index $ranked (ai-math:option $options definition-depth 3)))
          ($report (ai-math:zipperposition $thf $problem
            (ai-math:option $options zipper "zipperposition") (ai-math:option $options seconds 30)
            (ai-math:option $options zipper-mode ""))))
     (case $report
       (((AiATP:ZipperReport (AiATP:Advice "Theorem" $premises $definitions) $observation $envelope)
         (let* (($goal (ai-math:search-goal $search $index))
                ($defs (sort-atom (unique-atom (union-atom $definitions (ai-math:prover-goal-defs $thf $goal)))))
                ($advice (AiProver:Hints ($premises) $defs $defs "Theorem" ((AiResearch:Zipper $report))))
                ($result (ai-math:derived-prove (AiDerivedGoal $itp $target "skip" 0) $advice $options)))
           (case $result
             (((AiDerived:Proved $label $script $receipt)
               (ai-math:research-checked $context $target zipper $advice $script
                 (ai-math:itp-check-with $itp $target $script
                   (ai-math:option $options budget (AiITP:Budget 30000 200000 8000))) $report))
              ($other (ai-math:research-checked $context $target zipper $advice "" $other $report))))))
        ((AiATP:ZipperReport (AiATP:Advice $status $p $d) $observation $envelope)
          (ai-math:research-checked $context $target zipper $hints "" AiResearch:NoCandidate $report))
        ($other (ai-math:research-checked $context $target zipper $hints "" $other $other))))))
(= (ai-math:research-one $context $declarations $target $mode $hints $options $client)
   (let* (((AiProver $search $thf $itp $vampire $policy) $context)
          ($declaration (car-atom (filter-atom $declarations $d (== (ai-math:declaration-name $d) $target)))))
     (case $mode
       ((prop
         (let $result (ai-math:prop-check (ai-math:prop-synth $declarations (ai-math:option $options max-depth 10))
                       $itp $declaration (ai-math:option $options budget (AiITP:Budget 30000 200000 8000)))
           (case $result
             (((AiProp:Result $name $proof $script $answer)
               (ai-math:research-checked $context $target prop $hints $script $answer $result))
              ($other (ai-math:research-checked $context $target prop $hints "" $other $other))))))
        (incremental
         (let (AiInc:Result $name $outcome $statistics) (ai-math:incremental-prove $context $target $hints
           (filter-atom (ai-math:research-option (ai-math:research-option $options probe-budget
               (ai-math:option $options probe-budget (ai-math:option $options budget (AiITP:Budget 30000 200000 8000))))
             check-budget (ai-math:option $options check-budget (ai-math:option $options budget (AiITP:Budget 30000 200000 8000))))
             $entry (ai-math:contains (max-depth max-probes beam k chunk-size deadline-ms probe-budget check-budget) (car-atom $entry))))
           (AiProver:Result $target (ai-math:declaration-index $declaration) $hints ($statistics) $outcome)))
        (decompose
         (let (AiDecomp:Result $name $plan $trace $script $answer)
              (ai-math:decompose-rounds $context $client $target $hints $options)
           (ai-math:research-checked $context $target decompose $hints $script $answer (AiResearch:Plan $plan $trace))))
        (hybrid
         (let (AiHybrid:Result $name $script $answer $trace)
              (ai-math:hybrid-prove $context $declarations $target $hints $options)
           (ai-math:research-checked $context $target hybrid $hints $script $answer (AiResearch:Hybrid $trace))))
        (chain
         (let* (($synth (ai-math:prop-synth $declarations 10))
                ((AiOracle:Chain $hops (AiDecomp:Result $name $plan $trace $script $answer))
                  (ai-math:chain-prove $context $synth $declaration $hints $options)))
           (ai-math:research-checked $context $target chain $hints $script $answer (AiResearch:OracleChain $hops $trace))))
        (duper2
         (let* (((AiProver:Hints $sets $defs $gd $status $trace) $hints)
                ($all (ai-math:derived-candidates duper2 $sets $defs $gd))
                ($limit (ai-math:option $options candidate-limit 0))
                ($candidates (if (== $limit 0) $all (list:take $limit $all)))
                ($budget (ai-math:option $options budget (AiITP:Budget 30000 200000 8000)))
                ($answer (ai-math:prover-run-attempts $itp $target duper $candidates $budget $budget
                           (ai-math:option $options deadline-ms 0)))
                ($attempts (case $answer (((AiITP:Batch $name $rows) (ai-math:prover-attempts duper $candidates $rows 0))
                             ($other ((AiProver:StageFault duper $other)))))))
           (AiProver:Result $target (ai-math:declaration-index $declaration) $hints $attempts
             (case (ai-math:prover-winner $attempts)
               ((AiProver:NoWinner (ai-math:prover-outcome $attempts (duper)))
                ($winner $winner))))))
        (zipper (ai-math:research-zipper $context $target $hints $options))
        ($other (AiResearch:Fault unknown-algorithm))))))
(= (ai-math:research-open $context $corpus $path $mode $options $toolchain $resume)
   (ai-math:run-open-identity $context $path $resume
     (ai-math:research-identity $context $corpus $mode $options $toolchain)))
(= (ai-math:research-identity $context $corpus $mode $options $toolchain)
   (let* (($root (index-atom (index-atom $context 3) 2))
          ($sources (map-atom (ai-math:research-sources) $file
                     ($file (str:sha256 (fs:read-text (str:join "/" ($root $file)))))))
          ($identity (if (foldl-atom $sources true $ok $row (and $ok (== (get-type (index-atom $row 1)) String)))
             (ai-math:run-descriptor $root $corpus
               (AiResearch:Policy $mode $options (ai-math:itp-profile-name (index-atom $context 3))) ($toolchain $sources))
             (AiResearch:Fault missing-runtime-source))))
     $identity))
(= (ai-math:research-publish $owner $target $mode $elapsed $result)
   (case (ai-math:run-result (index-atom $owner 3) $elapsed $result)
     (((JsonObject $fields)
       (let* (($profile (if (== $mode duper2) "duper"
                          (str:symbol->string (index-atom (index-atom (index-atom $owner 1) 3) 4))))
              ($proved (== (json:get (JsonObject $fields) "outcome") "proved"))
              ($row (JsonObject (union-atom (filter-atom $fields $field (not (== (index-atom $field 1) "proof_profile")))
                ((JsonPair "proof_profile" (if $proved $profile JsonNull))
                 (JsonPair "research_mode" (str:symbol->string $mode)) (JsonPair "oracle" (== $mode chain)))))))
         (ai-math:run-publish $owner $target $row)))
      ($other $other))))
(= (ai-math:research-run $owner $declarations $targets $mode $options $client)
   (let* (($context (index-atom $owner 1))
          ($completed (foldl-atom $targets true $ok $target
            (if $ok
              (case (ai-math:run-resume $owner $target (ai-math:option $options budget (AiITP:Budget 30000 200000 8000)))
                ((AiRun:NeedsWork
                  (let* (($hints (if (== $mode prop) (AiProver:Hints (()) () () "not-requested" ())
                                  (ai-math:research-hints $context $target $options))) ($start (system:monotonic-ns))
                         ($answers (collapse (ai-math:research-one $context $declarations $target $mode $hints $options $client)))
                         ($result (case $answers ((($answer) $answer) ($other (AiResearch:Fault ambiguous-backend-result)))))
                         ($published (ai-math:research-publish $owner $target $mode (- (system:monotonic-ns) $start) $result))
                         ($shown (println! $published)))
                    (case $published (((AiRun:Recorded $n $row) true) ($other false)))))
                 ((AiRun:Reused $n $why $row) (let $shown (println! (AiRun:Reused $n $why $row)) true))
                 ($other (let $shown (println! $other) false)))) false))))
     (if $completed (ai-math:run-summary $owner) (AiResearch:Fault interrupted-or-unpublished))))
(= (ai-math:research-observe $context $declarations $target $mode $options $index)
   (let* (($declaration (car-atom (filter-atom $declarations $d (== (ai-math:declaration-name $d) $target))))
          ($ordinal (ai-math:declaration-index $declaration)))
     (case $mode
       ((embedding (JsonArray (ai-math:embedding-python-rank $index $ordinal (ai-math:option $options limit 96))))
        (witness (repr (ai-math:witness-classify $declaration)))
        (oracle-premises (repr (ai-math:oracle-premise-advice $context $declaration $options)))
        (proof-profile
          (let* (($thf (index-atom $context 2))
                 ($ranked (ai-math:entry-names (ai-math:rank (index-atom $context 1) $ordinal
                            (ai-math:option $options limit 64))))
                 ($problem (ai-math:thf-problem $thf $ordinal $ranked (ai-math:option $options definition-depth 3))))
            (repr (ai-math:proof-profile-report (ai-math:vampire $thf $problem (index-atom $context 4)
                     (ai-math:option $options seconds 30))))))
        (recall (repr (ai-math:recall-report
          (((ai-math:entry-names (ai-math:rank (index-atom $context 1) $ordinal (ai-math:option $options limit 64)))
            (ai-math:declaration-dependencies $declaration))) (16 32 64))))
        (oracle (repr (ai-math:oracle-probe $context (ai-math:prop-synth $declarations 10) $declaration
                   (ai-math:research-hints $context $target $options) $options)))
        ($other (AiResearch:Fault unknown-observation))))))
(= (ai-math:research-observations $context $declarations $targets $mode $options $index $identity $directory $resume)
   (case $identity
     (((AiRun:Identity $key $descriptor)
       (case (proc:run ("mkdir" "-p" "--" $directory) ((lifetime owner)))
         (((proc:result (proc:exited 0) proc:normal $out $err $capture)
           (AiResearch:Observations $mode (map-atom $targets $target
             (ai-math:research-observation-one $context $declarations $target $mode $options $index $key $directory $resume))))
          ($other (AiResearch:Fault observation-directory)))))
      ($other $other))))
(= (ai-math:research-observation-one $context $declarations $target $mode $options $index $key $directory $resume)
   (let $path (str:join "/" ($directory (str:concat (str:sha256 $target) ".json")))
     (if (fs:exists $path)
       (if (== $resume Resume)
         (let $row (json:parse (fs:read-text $path))
           (if (and (and (ai-math:run-unique-object $row)
                         (and (== (json:get $row "mode") (str:symbol->string $mode))
                              (== (json:get $row "proof_authority") "none")))
                  (and (== (json:get $row "schema") "ai-math.research-observation.v1")
                 (and (== (json:get $row "run") $key) (and (== (json:get $row "goal") $target)
                   (== (json:get $row "value_sha256") (str:sha256 (json:stringify (json:get $row "value"))))))))
             (AiResearch:Observed $target reused) (AiResearch:Fault incompatible-observation)))
         (AiResearch:Fault existing-observation))
       (let* (($value (ai-math:research-observe $context $declarations $target $mode $options $index))
              ($row (JsonObject ((JsonPair "schema" "ai-math.research-observation.v1") (JsonPair "run" $key)
                (JsonPair "goal" $target) (JsonPair "mode" (str:symbol->string $mode))
                (JsonPair "proof_authority" "none") (JsonPair "value" $value)
                (JsonPair "value_sha256" (str:sha256 (json:stringify $value))))))
              ($written (ai-math:run-publish-file $path (json:stringify $row))))
         (if (== $written ()) (AiResearch:Observed $target recorded) $written)))))
