; Isolated process scheduling over the existing experiment and process APIs.
; Configuration and worker requests are JSON data, never executable syntax.

(= (ai-math:workers-value $row $key $default)
   (case (json-object-get $row $key)
     ((JsonNull $default) ((JsonString $text) $text)
      ((JsonNumber $text) (str:string->number $text))
      ((JsonBool $value) $value) ($other AiWorkers:InvalidValue))))
(= (ai-math:workers-strings $value)
   (case $value
     (((JsonArray $items)
       (foldl-atom $items true $ok $item
         (and $ok (case $item (((JsonString $text) true) ($other false))))))
      ($other false))))
(= (ai-math:workers-config-valid $row)
   (and (ai-math:run-unique-object $row)
     (and (foldl-atom (ai-math:itp-json-keys (json-object-pairs $row)) true $ok $key
            (and $ok (ai-math:contains
              ("corpus" "output" "workers" "mode" "profile" "stride" "skip" "limit"
               "goals" "lean" "vampire" "trace" "worker_timeout_ms" "slices"
               "vampire_seconds" "induction" "use_duper" "lean_stages" "itp_runtime") $key)))
       (and (foldl-atom ("corpus" "output") true $ok $key
              (let $text (ai-math:workers-value $row $key AiMissing)
                (and $ok (if (== (get-type $text) String) (> (str:byte-length $text) 0) false))))
         (and (foldl-atom ("workers" "stride" "skip" "limit" "worker_timeout_ms" "vampire_seconds") true $ok $key
                (and $ok (ai-math:itp-natural (ai-math:workers-value $row $key 0))))
           (and (> (ai-math:workers-value $row "workers" 1) 0)
             (and (> (ai-math:workers-value $row "stride" 1) 0)
               (and (ai-math:contains ("Fresh" "Resume") (ai-math:workers-value $row "mode" "Fresh"))
                 (and (ai-math:contains ("PythonV4" "CettaFull") (ai-math:workers-value $row "profile" "PythonV4"))
                   (ai-math:workers-options-valid $row))))))))))
(= (ai-math:workers-options-valid $row)
   (and (ai-math:contains ("interpreted" "native")
          (ai-math:workers-value $row "itp_runtime"
            (system:getenv-or-default "CETTA_ITP_RUNTIME" "interpreted")))
    (and (foldl-atom ("lean" "vampire") true $ok $key
          (and $ok (== (get-type (ai-math:workers-value $row $key "")) String)))
     (and (foldl-atom ("trace" "induction") true $ok $key
            (let $value (ai-math:workers-value $row $key false)
              (and $ok (or (== $value true) (== $value false)))))
       (and (ai-math:contains (true false "Auto") (ai-math:workers-value $row "use_duper" "Auto"))
         (and (case (json-object-get $row "goals")
                ((JsonNull true) ($names (ai-math:workers-strings $names))))
           (and (case (json-object-get $row "slices")
                  ((JsonNull true) ((JsonArray $slice-items)
                    (foldl-atom $slice-items true $slice-ok $slice-item
                      (and $slice-ok (case $slice-item (((JsonNumber $n) (ai-math:itp-natural (str:string->number $n)))
                                            ($bad-slice false)))))) ($bad-slices false)))
             (case (json-object-get $row "lean_stages")
               ((JsonNull true) ((JsonArray $stage-items)
                 (foldl-atom $stage-items true $stage-ok $stage-item
                   (and $stage-ok (case $stage-item (((JsonString $stage)
                     (ai-math:contains ("base" "followup" "apply" "duper") $stage)) ($bad-stage false))))))
                ($bad-stages false))))))))))
(= (ai-math:workers-dirname $path)
   (let $directory (str:join "/" (list:reverse (cdr-atom (list:reverse (str:split "/" $path)))))
     (if (== $directory "") "/" $directory)))
(= (ai-math:workers-path $directory $path)
   (if (str:starts-with $path "/") $path (str:join "/" ($directory $path))))
(= (ai-math:workers-trim-directory $path)
   (if (and (> (str:byte-length $path) 1) (str:ends-with $path "/"))
     (ai-math:workers-trim-directory (str:byte-slice $path 0 (- (str:byte-length $path) 1))) $path))
(= (ai-math:workers-output-path $directory $path)
   (let $absolute (ai-math:workers-trim-directory (ai-math:workers-path $directory $path))
     (if (fs:exists $absolute) (fs:try-canonical-path $absolute)
       (case (fs:try-canonical-path (ai-math:workers-dirname $absolute))
         (((FS:CanonicalPath $parent)
           (FS:CanonicalPath (str:concat (str:concat (ai-math:workers-trim-directory $parent)
             (if (== $parent "/") "" "/")) (car-atom (list:reverse (str:split "/" $absolute))))))
          ($fault $fault))))))
(= (ai-math:workers-executable $directory $path)
   (if (> (size-atom (str:split "/" $path)) 1) (ai-math:workers-path $directory $path) $path))
(= (ai-math:workers-process-text $observation)
   (case $observation
     (((proc:result (proc:exited 0) proc:normal $out $err
         (proc:capture $kept $seen $ek $es proc:eof proc:eof (proc:input $sent $size)))
       (if (and (== $kept $seen) (and (== $ek $es) (== $sent $size)))
         (AiWorkers:Text $out) (AiWorkers:Fault incomplete-process $observation)))
      ((proc:result $termination proc:timed-out $out $err $capture)
       (AiWorkers:Unfinished deadline $termination))
      ((proc:result $termination proc:cancelled $out $err $capture)
       (AiWorkers:Unfinished cancelled $termination))
      ($other (AiWorkers:Fault process $observation)))))
(= (ai-math:workers-config $path $root)
   (let $row (json-parse (fs:read-text $path))
     (if (ai-math:workers-config-valid $row)
       (let* (($directory (ai-math:workers-dirname (fs:canonical-path $path)))
              ($resolved (fs:try-canonical-path (ai-math:workers-path $directory
                            (ai-math:workers-value $row "corpus" ""))))
              ($corpus (case $resolved (((FS:CanonicalPath $name) $name) ($other $other))))
              ($output-result (ai-math:workers-output-path $directory (ai-math:workers-value $row "output" "")))
              ($output (case $output-result (((FS:CanonicalPath $out) $out) ($output-other $output-other))))
              ($binary (fs:canonical-path "/proc/self/exe")))
         (if (and (== (get-type $corpus) String) (== (get-type $output) String))
           (AiWorkers:Config $row $root $corpus $output $binary
             (ai-math:workers-executable $directory (ai-math:workers-value $row "lean"
               (system:getenv-or-default "LEAN_BIN" "lean")))
             (ai-math:workers-executable $directory (ai-math:workers-value $row "vampire"
               (system:getenv-or-default "VAMPIRE_BIN" "vampire"))))
           (AiWorkers:Request paths ($corpus $output))))
       (AiWorkers:Request configuration $path))))
(= (ai-math:workers-options $row $directory)
   (let* (($base (ai-math:prover-profile-options
                    (str:string->symbol (ai-math:workers-value $row "profile" "PythonV4"))))
          ($overrides (collapse (superpose
            ((case (json-object-get $row "slices")
               (((JsonArray $values) (slices (map-atom $values $v (str:string->number (json-number-value $v)))))
                ($other (empty))))
             (case (json-object-get $row "lean_stages")
               (((JsonArray $values) (lean-stages (map-atom $values $v (str:string->symbol (json-string-value $v)))))
                ($other (empty))))
             (case (json-object-get $row "vampire_seconds")
               (((JsonNumber $n) (vampire-seconds (str:string->number $n))) ($other (empty))))
             (case (json-object-get $row "induction")
               (((JsonBool $value) (induction $value)) ($other (empty))))
             (case (json-object-get $row "use_duper")
               (((JsonBool $value) (use-duper $value)) ((JsonString "Auto") (use-duper Auto)) ($other (empty))))
             (if (ai-math:workers-value $row "trace" false)
               (trace-directory $directory) (empty)))))))
     (union-atom $overrides
       (filter-atom $base $entry
         (not (ai-math:contains (map-atom $overrides $pair (car-atom $pair)) (car-atom $entry)))))))
(= (ai-math:workers-targets $declarations $row)
   (case $declarations
     (((Error $reason $where) (AiWorkers:Fault corpus ($reason $where)))
      ($items
       (let* (($all (map-atom (filter-atom $items $d (== (index-atom $d 2) THM)) $d
                       ((index-atom $d 1) (index-atom $d 3))))
              ($selected (case (json-object-get $row "goals")
                           ((JsonNull $all)
                            ((JsonArray $names)
                             (let $wanted (map-atom $names $name (json-string-value $name))
                               (if (and (== (size-atom $wanted) (size-atom (unique-atom $wanted)))
                                        (== (subtraction-atom $wanted (map-atom $all $entry (index-atom $entry 1))) ()))
                                 (filter-atom $all $entry (ai-math:contains $wanted (index-atom $entry 1)))
                                 (AiWorkers:Request goals $wanted)))))))
              ($stride (ai-math:workers-value $row "stride" 1))
              ($skip (ai-math:workers-value $row "skip" 0))
              ($limit (ai-math:workers-value $row "limit" 0)))
         (case $selected
           (((AiWorkers:Request $reason $details) $selected)
            ($targets
             (let (AiWorkers:Selection $position $out)
               (foldl-atom $targets (AiWorkers:Selection 0 ()) $state $target
                 (let (AiWorkers:Selection $i $result) $state
                   (AiWorkers:Selection (+ $i 1)
                     (if (and (>= $i $skip) (and (== (% (- $i $skip) $stride) 0)
                                (or (== $limit 0) (< (size-atom $result) $limit))))
                       (cons-atom $target $result) $result))))
               (list:reverse $out))))))))))
(= (ai-math:workers-partition $targets $count $worker)
   (let (AiWorkers:Selection $position $out)
     (foldl-atom $targets (AiWorkers:Selection 0 ()) $state $target
       (let (AiWorkers:Selection $i $items) $state
         (AiWorkers:Selection (+ $i 1)
           (if (== (% $i $count) $worker) (cons-atom $target $items) $items))))
     (list:reverse $out)))
(= (ai-math:workers-manifest $key $targets $count)
   (JsonObject
     ((JsonPair "schema" (JsonString "ai-math.workers.v1"))
      (JsonPair "run" (JsonString $key))
      (JsonPair "workers" (JsonNumber (str:number->string $count)))
      (JsonPair "targets" (JsonArray (map-atom $targets $target
        (JsonArray ((JsonNumber (str:number->string (index-atom $target 0))) (JsonString (index-atom $target 1))))))))))
(= (ai-math:workers-open $config $manifest)
   (let (AiWorkers:Config $row $root $corpus $output $binary $lean $vampire) $config
     (let $path (str:concat $output "/manifest.json")
       (if (== (ai-math:workers-value $row "mode" "Fresh") "Fresh")
         (if (fs:exists $output) (AiWorkers:Request existing-output $output)
           (case (ai-math:workers-process-text (proc:run ("mkdir" "--" $output) ()))
             (((AiWorkers:Text $text)
               (case (ai-math:run-publish-file $path (str:concat (json-stringify $manifest) "\n"))
                 ((() AiWorkers:Ready) ($fault (AiWorkers:Fault manifest-write $fault)))))
              ($other $other))))
         (if (== (json-parse (fs:read-text $path)) $manifest) AiWorkers:Ready
           (AiWorkers:Request incompatible-manifest $path))))))
(= (ai-math:workers-job $config $targets $worker)
   (let (AiWorkers:Config $row $root $corpus $output $binary $lean $vampire) $config
     (let $prefix (str:join "" ($output "/worker-" (str:number->string $worker)))
       (AiWorkers:Job $worker $targets (str:concat $prefix ".jsonl")
         (str:concat $prefix ".snapshot.jsonl") (str:concat $prefix "-traces")))))
(= (ai-math:workers-request $config $identity $job)
   (let (AiWorkers:Config $row $root $corpus $output $binary $lean $vampire) $config
     (let (AiWorkers:Job $id $targets $journal $snapshot $trace) $job
       (let (AiRun:Identity $key $descriptor) $identity
         (JsonObject
           ((JsonPair "schema" (JsonString "ai-math.worker-request.v1"))
            (JsonPair "config" $row) (JsonPair "corpus" (JsonString $corpus))
            (JsonPair "lean" (JsonString $lean)) (JsonPair "vampire" (JsonString $vampire))
            (JsonPair "build" (JsonString (index-atom (index-atom $descriptor 6) 3)))
            (JsonPair "run" (JsonString $key)) (JsonPair "worker" (JsonNumber (str:number->string $id)))
            (JsonPair "targets" (JsonArray (map-atom $targets $target
              (JsonArray ((JsonNumber (str:number->string (index-atom $target 0))) (JsonString (index-atom $target 1)))))))
            (JsonPair "journal" (JsonString $journal)) (JsonPair "snapshot" (JsonString $snapshot))
            (JsonPair "trace_directory" (JsonString $trace))))))))
(= (ai-math:workers-start $config $identity $job)
   (let (AiWorkers:Config $row $root $corpus $output $binary $lean $vampire) $config
     (AiWorkers:Active $job
       (proc:spawn ("env" (str:concat "TMPDIR=" (str:concat $output "/tmp"))
                    (str:concat "CETTA_ITP_RUNTIME="
                      (ai-math:workers-value $row "itp_runtime"
                        (system:getenv-or-default "CETTA_ITP_RUNTIME" "interpreted")))
                    $binary "--no-results" "--lang" "petta@1.0.6"
                    (str:concat $root "/phase1/experiment_worker_main.metta"))
         ((stdin (json-stringify (ai-math:workers-request $config $identity $job)))
          (timeout-ms (ai-math:workers-value $row "worker_timeout_ms" 0)))))))
(= (ai-math:workers-start-all $config $identity $targets $count $worker)
   (if (== $worker $count) ()
     (let $active (ai-math:workers-start $config $identity
                    (ai-math:workers-job $config
                      (ai-math:workers-partition $targets $count $worker) $worker))
       (cons-atom $active
         (ai-math:workers-start-all $config $identity $targets $count (+ $worker 1))))))
(= (ai-math:workers-json-lines $text)
   (map-atom (filter-atom (str:split "\n" $text) $line (not (== (str:trim $line) "")))
     $line (json-parse $line)))
(= (ai-math:workers-snapshot-valid $rows $identity $targets)
   (let (AiRun:Identity $key $descriptor) $identity
     (if (== $rows ()) false
       (and (== (car-atom $rows) (ai-math:run-header $identity))
         (let $results (cdr-atom $rows)
           (and (== (size-atom $results) (size-atom $targets))
             (and (== (size-atom (unique-atom (map-atom $results $r (json-object-get $r "goal"))))
                      (size-atom $targets))
               (foldl-atom $results true $ok $result
                 (and $ok (and (ai-math:run-unique-object $result)
                   (and (== (json-object-get $result "schema") (JsonString "ai-math.result.v1"))
                     (and (== (json-object-get $result "run") (JsonString $key))
                       (and (ai-math:contains ("proved" "not-proved" "unfinished" "fault")
                              (ai-math:workers-value $result "outcome" AiMissing))
                         (ai-math:contains $targets
                           ((ai-math:workers-value $result "index" -1)
                            (ai-math:workers-value $result "goal" AiMissing))))))))))))))))
(= (ai-math:workers-observe $identity $job $observation)
   (let (AiWorkers:Job $id $targets $journal $snapshot $trace) $job
     (case (ai-math:workers-process-text $observation)
       (((AiWorkers:Text $text)
         (let* (($reply (json-parse $text)) ($data (fs:read-text $snapshot)))
           (if (and (ai-math:run-unique-object $reply)
                (and (== (json-object-get $reply "schema") (JsonString "ai-math.worker.v1"))
                  (and (== (json-object-get $reply "worker") (JsonNumber (str:number->string $id)))
                    (and (== (json-object-get $reply "run") (JsonString (index-atom $identity 1)))
                      (== (get-type $data) String)))))
             (let $rows (ai-math:workers-json-lines $data)
               (if (and (== (json-object-get $reply "snapshot_sha256") (JsonString (str:sha256 $data)))
                        (ai-math:workers-snapshot-valid $rows $identity $targets))
                 (AiWorkers:Done $id (cdr-atom $rows))
                 (AiWorkers:Fault invalid-snapshot $id)))
             (AiWorkers:Fault worker-protocol ($id $text)))))
        ($other (AiWorkers:FailedWorker $id $other))))))
(= (ai-math:workers-poll $identity $state $active)
   (case $state
     (((AiWorkers:Polling $pending $done)
       (let (AiWorkers:Active $job $owner) $active
         (let $result (proc:wait $owner 100)
           (if (== $result proc:pending) (AiWorkers:Polling (cons-atom $active $pending) $done)
             (let* (($closed (proc:close $owner))
                    ($observed (ai-math:workers-observe $identity $job $result)))
               (case $observed
                 (((AiWorkers:Done $id $rows) (AiWorkers:Polling $pending (cons-atom $observed $done)))
                  ($other $other))))))))
      ($other $state))))
(= (ai-math:workers-cancel $active)
   (map-atom $active $entry
     (let (AiWorkers:Active $job $owner) $entry
       (let $cancelled (proc:cancel $owner) (proc:close $owner)))))
(= (ai-math:workers-wait $identity $active $done)
   (if (== $active ()) (AiWorkers:Finished $done)
     (case (foldl-atom $active (AiWorkers:Polling () $done) $state $job
             (ai-math:workers-poll $identity $state $job))
       (((AiWorkers:Polling $pending $completed)
         (ai-math:workers-wait $identity (list:reverse $pending) $completed))
        ($fault (let $cancelled (ai-math:workers-cancel $active) $fault))))))
(= (ai-math:workers-join $config $identity $targets $done)
   (let* (($rows (foldl-atom $done () $out $worker (union-atom (index-atom $worker 2) $out)))
          ($ordered (map-atom (sort-atom (map-atom $rows $row
                          ((ai-math:workers-value $row "index" -1) $row))) $entry (index-atom $entry 1)))
          ($data (str:concat (str:join "\n" (map-atom (cons-atom (ai-math:run-header $identity) $ordered)
                                                   $row (json-stringify $row))) "\n")))
     (if (ai-math:workers-snapshot-valid (cons-atom (ai-math:run-header $identity) $ordered) $identity $targets)
       (case (ai-math:run-publish-file (str:concat (index-atom $config 4) "/joined.jsonl") $data)
         ((() (AiWorkers:Summary (index-atom $identity 1) (size-atom $ordered)
                  (map-atom ("proved" "not-proved" "unfinished" "fault") $kind
                    ($kind (size-atom (filter-atom $ordered $row
                      (== (json-object-get $row "outcome") (JsonString $kind))))))
                  (str:concat (index-atom $config 4) "/joined.jsonl")))
          ($fault (AiWorkers:Fault join-write $fault))))
       (AiWorkers:Fault incomplete-join (size-atom $ordered)))))
(= (ai-math:workers-run-identity $config $targets $identity)
   (case $identity
     (((AiRun:Identity $key $descriptor)
       (let* (($row (index-atom $config 1))
              ($requested (ai-math:workers-value $row "workers" 1))
              ($count (if (< $requested (size-atom $targets)) $requested (size-atom $targets)))
              ($ready (ai-math:workers-open $config (ai-math:workers-manifest $key $targets $count))))
         (if (== $ready AiWorkers:Ready)
           (case (ai-math:workers-process-text
                   (proc:run ("mkdir" "-p" "--" (str:concat (index-atom $config 4) "/tmp")) ()))
             (((AiWorkers:Text $text)
               (let $active (ai-math:workers-start-all $config $identity $targets $count 0)
                 (case (ai-math:workers-wait $identity $active ())
                   (((AiWorkers:Finished $done) (ai-math:workers-join $config $identity $targets $done))
                    ($other $other)))))
              ($other $other))) $ready)))
      ($other $other))))
(= (ai-math:workers-run $config)
   (case $config
     (((AiWorkers:Config $row $root $corpus $output $binary $lean $vampire)
       (let $targets (ai-math:workers-targets (ai-math:load-library $corpus) $row)
         (case $targets
           (((AiWorkers:Fault $reason $details) $targets)
            ((AiWorkers:Request $reason $details) $targets)
            ($names
             (case (ai-math:workers-process-text (proc:run ("sha256sum" "--" $binary) ()))
               (((AiWorkers:Text $digest)
                 (let $build (car-atom (str:split " " (str:trim $digest)))
                   (ai-math:workers-run-identity $config $names
                     (ai-math:run-descriptor $root $corpus
                       (ai-math:run-effective-options $root (ai-math:workers-options $row $output))
                       (AiRun:Toolchain $lean $vampire $build
                         (AiRun:ITPRuntime (ai-math:workers-value $row "itp_runtime"
                           (system:getenv-or-default "CETTA_ITP_RUNTIME" "interpreted"))))))))
                ($other $other))))))))
      ($other $other))))
(= (ai-math:workers-exit-code $result)
   (case $result
     (((AiWorkers:Summary $key $count $outcomes $path)
       (if (> (index-atom (index-atom $outcomes 3) 1) 0) 2
         (if (> (index-atom (index-atom $outcomes 2) 1) 0) 3 0)))
      ((AiWorkers:Unfinished $why $details) 3)
      ((AiWorkers:FailedWorker $id (AiWorkers:Unfinished $why $details)) 3)
      ($other 2))))

; A completed snapshot contains only the current, rechecked store, not the
; unverified historical rows that run-open retained for possible resume.
(= (ai-math:worker-snapshot $owner $targets $path)
   (let (AiRun $context $journal $key $store $issues) $owner
     (let* (($rows (map-atom $targets $entry (ai-math:get $store (index-atom $entry 1) AiMissing)))
            ($header (car-atom (ai-math:workers-json-lines (fs:read-text $journal))))
            ($data (str:concat (str:join "\n" (map-atom (cons-atom $header $rows)
                                                 $row (json-stringify $row))) "\n")))
       (case (ai-math:run-publish-file $path $data)
         ((() (AiWorkers:Snapshot (str:sha256 $data)))
          ($fault (AiWorkers:Fault snapshot-write $fault)))))))
(= (ai-math:worker-run $request $root)
   (let* (($row (json-object-get $request "config"))
          ($corpus (ai-math:workers-value $request "corpus" AiMissing))
          ($lean (ai-math:workers-value $request "lean" AiMissing))
          ($vampire (ai-math:workers-value $request "vampire" AiMissing))
          ($trace (ai-math:workers-value $request "trace_directory" AiMissing))
          ($journal (ai-math:workers-value $request "journal" AiMissing))
          ($targets (map-atom (json-array-items (json-object-get $request "targets")) $item
                       ((str:string->number (json-number-value (index-atom (json-array-items $item) 0)))
                        (json-string-value (index-atom (json-array-items $item) 1)))))
          ($options (ai-math:workers-options $row $trace))
          ($context (ai-math:prover-with (ai-math:load-library $corpus) $corpus $root $lean $vampire $options))
          ($identity (ai-math:run-descriptor $root $corpus (ai-math:run-effective-options $root $options)
                        (AiRun:Toolchain $lean $vampire (ai-math:workers-value $request "build" AiMissing)
                          (AiRun:ITPRuntime (ai-math:workers-value $row "itp_runtime"
                            (system:getenv-or-default "CETTA_ITP_RUNTIME" "interpreted")))))))
     (if (and (== (json-object-get $request "schema") (JsonString "ai-math.worker-request.v1"))
              (and (ai-math:workers-config-valid $row)
                (== (json-object-get $request "run") (JsonString (index-atom $identity 1)))))
       (let $ready (if (ai-math:workers-value $row "trace" false)
                     (ai-math:workers-process-text (proc:run ("mkdir" "-p" "--" $trace) ()))
                     (AiWorkers:Text ""))
         (case $ready
           (((AiWorkers:Text $text)
             (let $owner (ai-math:run-open-identity $context $journal
                            (if (fs:exists $journal) Resume Fresh) $identity)
               (let $summary (ai-math:run-quiet $owner (map-atom $targets $entry (index-atom $entry 1))
                                (AiITP:Budget 300000 1000000 8000))
                 (case $summary
                   (((AiRun:Summary $key $count $outcomes $issues)
                     (case (ai-math:worker-snapshot $owner $targets
                             (ai-math:workers-value $request "snapshot" AiMissing))
                       (((AiWorkers:Snapshot $hash)
                         (JsonObject
                           ((JsonPair "schema" (JsonString "ai-math.worker.v1"))
                            (JsonPair "run" (JsonString $key))
                            (JsonPair "worker" (json-object-get $request "worker"))
                            (JsonPair "snapshot_sha256" (JsonString $hash)))))
                        ($other $other))))
                    ($other $other))))))
            ($other $other))))
       (AiWorkers:Fault worker-request invalid))))
