; Baseline JSONL is advice, never evidence of a checked proof. Import the
; normal experiment, HTTP/chat and proposal modules before this file.

(= (ai-math:proposal-strings $value)
   (case $value
     (((JsonArray $values)
       (let $strings (map-atom $values $item
              (case $item (((JsonString $text) $text) ($other AiProposal:InvalidName))))
         (if (foldl-atom $strings true $ok $name (and $ok (== (get-type $name) String)))
           $strings AiProposal:InvalidNames)))
      ($other AiProposal:InvalidNames))))
(= (ai-math:proposal-read-line (AiProver $s $t (AiITP $catalog $r $l $p) $v $o) $space $state $line)
   (case $state
     (((AiProposal:Baseline $names)
       (if (== (str:trim $line) "") $state
         (let $row (json-parse $line)
           (if (ai-math:run-unique-object $row)
             (if (== (json-object-get $row "schema") (JsonString "ai-math.run.v1")) $state
               (case ((json-object-get $row "goal") (json-object-get $row "vampire"))
                 ((((JsonString $name) (JsonString $status))
                   (case (ai-math:get $catalog $name AiMissing)
                     (((AiITP:Declaration $i THM)
                       (let* (($premises (ai-math:proposal-strings (json-object-get $row "premises")))
                              ($defs (ai-math:proposal-strings (json-object-get $row "defs")))
                              ($label (json-object-get $row "proved_by")))
                         (if (and (not (== $premises AiProposal:InvalidNames))
                                  (and (not (== $defs AiProposal:InvalidNames))
                                    (or (== $label JsonNull)
                                      (case $label (((JsonString $text) true) ($other false))))))
                           (if (== (ai-math:get $space $name AiMissing) AiMissing)
                             (let $stored (ai-math:put $space $name (AiProposal:Advice $i $premises $defs $status))
                               (AiProposal:Baseline (if (or (== $label JsonNull) (== $label (JsonString "")))
                                 (cons-atom $name $names) $names)))
                             (AiProposal:Fault duplicate-baseline-goal $name))
                           (AiProposal:Fault baseline-shape $name))))
                      ($other (AiProposal:Fault unknown-baseline-goal $name)))))
                  ($other (AiProposal:Fault baseline-shape (str:sha256 $line))))))
             (AiProposal:Fault malformed-baseline-line (str:sha256 $line))))))
      ($other $other))))
(= (ai-math:proposal-open $context $client $corpus $baseline $path $toolchain $mode $rounds $budget $resume)
   (if (and (ai-math:contains (direct dsp) $mode)
            (and (ai-math:itp-natural $rounds)
              (and (ai-math:itp-budget-valid $budget)
                (and (not (== $path $baseline))
                     (not (== $path (ai-math:llm-config $client Ledger)))))))
     (case ($context $client (fs:read-text $baseline))
       ((((AiProver $search $thf (AiITP $catalog $root $lean $profile) $vampire $options)
          (AiLLM $config $session) $text)
         (if (== (get-type $text) String)
           (let* (($space (new-space))
                  ($scanned (foldl-atom (str:split "\n" $text) (AiProposal:Baseline ()) $state $line
                    (ai-math:proposal-read-line $context $space $state $line))))
             (case $scanned
               (((AiProposal:Baseline $targets)
                 (let* (($policy (AiProposal:Policy $options $mode $rounds $budget
                          (ai-math:llm-config $client Model) (ai-math:llm-config $client Cap)
                          (ai-math:llm-config $client Options)
                          (str:sha256 (ai-math:llm-config $client Endpoint)) (str:sha256 $text)))
                        ($sources (map-atom
                          ("phase1/llm.metta" "phase1/llm_transport.metta" "phase1/http_transport.metta"
                           "phase1/llm_ledger.metta" "phase1/llm_ledger_main.metta" "phase1/llm_experiment.metta"
                           "phase1/llm_experiment_main.metta")
                          $file ($file (str:sha256 (fs:read-text (str:join "" ($root "/" $file)))))))
                        ($identity (ai-math:run-descriptor $root $corpus $policy ($toolchain $sources)))
                        ($owner (ai-math:run-open-identity $context $path $resume $identity)))
                   (case $owner
                     (((AiRun $c $p $key $store $issues)
                       (AiProposalRun $owner $client $space (list:reverse $targets) $mode $rounds $budget))
                      ($other $other)))))
                ($other $other))))
           (AiProposal:Fault baseline-read ())))
        ($other (AiProposal:Fault preparation ()))))
     (AiProposal:Fault policy ())))
(= (ai-math:proposal-drop $count $names)
   (if (or (== $count 0) (== $names ())) $names
     (ai-math:proposal-drop (- $count 1) (cdr-atom $names))))
(= (ai-math:proposal-select $owner $stride $limit $skip $vampire-only)
   (case $owner
     (((AiProposalRun $run $client $space $names $mode $rounds $budget)
       (if (and (ai-math:itp-natural $stride) (and (> $stride 0)
            (and (ai-math:itp-natural $limit) (and (ai-math:itp-natural $skip)
              (or (== $vampire-only true) (== $vampire-only false))))))
         (let* (($eligible (filter-atom $names $name
                    (or (not $vampire-only) (str:starts-with (index-atom (ai-math:get $space $name AiMissing) 4) "Theorem"))))
                ((AiProposal:Sample $count $selected)
                  (foldl-atom $eligible (AiProposal:Sample 0 ()) $state $name
                    (let (AiProposal:Sample $i $out) $state
                      (AiProposal:Sample (+ $i 1) (if (== (% $i $stride) 0) (cons-atom $name $out) $out)))))
                ($sample (list:reverse $selected))
                ($bounded (if (== $limit 0) $sample (list:take $limit $sample))))
           (ai-math:proposal-drop $skip $bounded))
         (AiProposal:Fault selection-policy ())))
      ($other $other))))
(= (ai-math:proposal-fresh (AiProposalRun $owner $client $space $names $mode $rounds $budget) $target)
   (case (ai-math:get $space $target AiMissing)
     (((AiProposal:Advice $index $original $defs $status)
       (let* (($context (index-atom $owner 1))
              ((AiProver $search $thf $itp $vampire $options) $context)
              ($premises (if (str:starts-with $status "Theorem") $original
                (list:take 16 (filter-atom (ai-math:entry-names (ai-math:rank $search $index 24)) $name
                  (case (ai-math:thf-lookup $thf Name $name)
                    (((AiTHF:Binding $id (AiTHF:Fact $i $kind $n $s $b)) (ai-math:contains (THM AXIOM) $kind))
                     ($other false)))))))
              ($started (system:monotonic-ns))
              ($result (if (== $mode direct)
                (ai-math:llm-prove $context $client $target $premises $defs $rounds $budget)
                (ai-math:dsp-prove $context $client $target $premises $defs $rounds $budget)))
              ($elapsed (- (system:monotonic-ns) $started))
              ($outcome (case $result
                (((AiLLM:Result $n $transcript $done) $done)
                 ((AiDSP:Result $n $draft $transcript $done) $done)
                 ($other (AiProver:Faulted (($other)))))))
              ($row (ai-math:run-result (index-atom $owner 3) $elapsed
                (AiProver:Result $target $index (AiProver:Hints ($premises) $defs () $status ()) $result $outcome))))
         (case $row
           (((JsonObject $fields)
             (ai-math:run-publish $owner $target
               (JsonObject (union-atom $fields
                 ((JsonPair "model" (JsonString (ai-math:llm-config $client Model)))
                  (JsonPair "mode" (JsonString (str:symbol->string $mode))))))))
            ($other $other)))))
      ($other (AiProposal:Fault unknown-target $target)))))
(= (ai-math:proposal-one $owner $target)
   (case $owner
     (((AiProposalRun $run $client $space $names $mode $rounds $budget)
       (case (ai-math:run-resume $run $target $budget)
         ((AiRun:NeedsWork (ai-math:proposal-fresh $owner $target)) ($other $other))))
      ($other $other))))
(= (ai-math:proposal-run $owner $targets)
   (case $owner
     (((AiProposalRun $run $client $space $names $mode $rounds $budget)
       (let $completed (foldl-atom $targets AiRun:Running $state $target
              (if (== $state AiRun:Running)
                (let $result (ai-math:proposal-one $owner $target)
                  (let $printed (println! $result)
                    (case $result
                      (((AiRun:Recorded $n $row) AiRun:Running)
                       ((AiRun:Reused $n $kind $row) AiRun:Running) ($other $other))))) $state))
         (if (== $completed AiRun:Running) (ai-math:run-summary $run) $completed)))
      ($other $other))))
