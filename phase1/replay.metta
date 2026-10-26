; Replay exact published scripts. Import library.metta, itp.metta, proc,
; json, list and system first. No solver, provider or proof discovery is invoked.

(= (ai-math:replay-row-valid $row)
   (case $row
     (((JsonObject $pairs)
       (and (== (sort-atom (ai-math:itp-json-keys $pairs))
                (sort-atom ("goal" "origin" "script" "prelude" "duper")))
         (and (foldl-atom ("goal" "origin" "script" "prelude") true $ok $key
                (and $ok (== (get-type (json:get $row $key)) String)))
           (and (not (== (json:get $row "goal") ""))
             (and (not (== (json:get $row "script") ""))
               (or (== (json:get $row "duper") true) (== (json:get $row "duper") false)))))))
      ($other false))))

(= (ai-math:replay-admit $catalog $seen $state $line)
   (case $state
     (((AiReplay:Rows $ordinal $entries)
       (let $row (json:parse $line)
         (if (ai-math:replay-row-valid $row)
           (let $name (json:get $row "goal")
             (case (ai-math:get $catalog $name AiMissing)
               (((AiITP:Declaration $index THM)
                 (if (== (ai-math:get $seen $name AiMissing) AiMissing)
                   (let $stored (ai-math:put $seen $name true)
                     (AiReplay:Rows (+ $ordinal 1)
                       (cons-atom (AiReplay:Entry $ordinal $row) $entries)))
                   (AiReplay:Fault duplicate-goal ($ordinal $name))))
                ($other (AiReplay:Fault unknown-theorem ($ordinal $name))))))
           (AiReplay:Fault invalid-row $ordinal))))
      ($failure $failure))))

(= (ai-math:replay-prepare $context $lines $shard $shards)
   (if (and (ai-math:natural $shard)
            (and (ai-math:natural $shards) (and (> $shards 0) (< $shard $shards))))
     (case $context
       (((AiITP $catalog $root $lean $profile)
         (if (== (get-metatype $lines) Expression)
           (let $seen (new-space)
             (case (foldl-atom $lines (AiReplay:Rows 0 ()) $state $line
                     (ai-math:replay-admit $catalog $seen $state $line))
               (((AiReplay:Rows $count $reversed)
                 (let $selected (filter-atom (list:reverse $reversed) $entry
                                   (== (% (index-atom $entry 1) $shards) $shard))
                   (if (== $selected ()) (AiReplay:Fault empty-selection $count)
                     (let $needs-duper (foldl-atom $selected false $need $entry
                                           (or $need (json:get (index-atom $entry 2) "duper")))
                       (if (and $needs-duper (not (ai-math:itp-duper-prepared $root)))
                         (AiReplay:Fault missing-duper $root)
                         (AiReplay:Prepared $context $count $selected))))))
                ($failure $failure))))
           (AiReplay:Fault input-read $lines)))
        ($failure (AiReplay:Fault checker-context $failure))))
     (AiReplay:Fault invalid-shard ($shard $shards))))

(= (ai-math:replay-write $row)
   (system:write stdout (str:concat (json:stringify $row) "\n")))

(= (ai-math:replay-step $context $core-budget $duper-budget $state $entry)
   (case $state
     (((AiReplay:Checked $count)
       (let (AiReplay:Entry $ordinal $row) $entry
         (let* (($target (json:get $row "goal"))
                ($duper (json:get $row "duper"))
                ($start (system:monotonic-ns))
                ($result (ai-math:itp-check-program-with
                           (ai-math:itp-select-profile $context (if $duper duper core))
                           $target (json:get $row "prelude") (json:get $row "script")
                           (if $duper $duper-budget $core-budget)))
                ($elapsed (- (system:monotonic-ns) $start))
                ($accepted (case $result (((AiITP:Accepted $name $used $axioms) true) ($other false))))
                ($frontier (case $result (((AiITP:Accepted $name $used $axioms) ($used $axioms)) ($other (() ())))))
                ($record (JsonObject
                  ((JsonPair "schema" "ai-math.replay.result.v1")
                   (JsonPair "ordinal" $ordinal) (JsonPair "goal" $target)
                   (JsonPair "origin" (json:get $row "origin"))
                   (JsonPair "duper" $duper) (JsonPair "ok" $accepted)
                   (JsonPair "nanoseconds" $elapsed)
                   (JsonPair "used" (JsonArray (index-atom $frontier 0)))
                   (JsonPair "axioms" (JsonArray (index-atom $frontier 1)))
                   (JsonPair "result" (repr $result)))))
                ($written (ai-math:replay-write $record)))
           (if (== $written ())
             (if $accepted (AiReplay:Checked (+ $count 1))
               (AiReplay:Stopped $count $ordinal $result))
             (AiReplay:Fault output-write $written)))))
      ($stopped $stopped))))

(= (ai-math:replay-run $prepared $core-budget $duper-budget)
   (if (and (ai-math:itp-budget-valid $core-budget) (ai-math:itp-budget-valid $duper-budget))
     (case $prepared
       (((AiReplay:Prepared $context $total $selected)
         (foldl-atom $selected (AiReplay:Checked 0) $state $entry
           (ai-math:replay-step $context $core-budget $duper-budget $state $entry)))
        ($failure $failure)))
     (AiReplay:Fault invalid-budget ($core-budget $duper-budget))))
