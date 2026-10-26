; cetta --no-results --lang petta phase1/replay_main.metta corpus bundle [lean [shard shards]]
!(import! &self "library.metta")
!(import! &self proc)
!(import! &self json)
!(import! &self system)
!(import! &self (library list))
!(import! &self "itp.metta")
!(import! &self "replay.metta")

(= (ai-replay-main:text $value)
   (if (== (get-metatype $value) Symbol) (str:symbol->string $value) $value))
(= (ai-replay-main:finish $result)
   (let $count (case $result (((AiReplay:Checked $n) $n) ((AiReplay:Stopped $n $i $why) $n) ($other 0)))
     (let $ok (case $result (((AiReplay:Checked $n) true) ($other false)))
       (let $written (ai-math:replay-write (JsonObject
              ((JsonPair "schema" "ai-math.replay.summary.v1")
               (JsonPair "ok" $ok) (JsonPair "checked" $count)
               (JsonPair "result" (repr $result)))))
         (system:exit (if (and $ok (== $written ())) 0 1))))))

!(if (not (ai-math:contains (2 3 5) (system:argc)))
   (let $printed (system:write stderr "usage: replay_main.metta corpus bundle [lean [shard shards]]\n")
     (system:exit 2))
   (let* (($corpus (ai-replay-main:text (system:arg 0)))
          ($bundle (ai-replay-main:text (system:arg 1)))
          ($lean (if (> (system:argc) 2) (ai-replay-main:text (system:arg 2))
                    (system:getenv-or-default "LEAN_BIN" "lean")))
          ($shard (if (> (system:argc) 3) (str:string->number (ai-replay-main:text (system:arg 3))) 0))
          ($shards (if (> (system:argc) 4) (str:string->number (ai-replay-main:text (system:arg 4))) 1))
          ($root (fs:canonical-path (str:concat (system:entry-directory) "/..")))
          ($declarations (ai-math:load-library $corpus)))
     (case $declarations
       (((Error $reason $where) (ai-replay-main:finish (AiReplay:Fault corpus ($reason $where))))
        ($items
         (let* (($context (ai-math:itp $items $root $lean))
                ($prepared (ai-math:replay-prepare $context (fs:read-lines $bundle) $shard $shards)))
           (case $prepared
             (((AiReplay:Prepared $itp $count $selected)
               (let $written (ai-math:replay-write (JsonObject
                      ((JsonPair "schema" "ai-math.replay.header.v1")
                       (JsonPair "entries" $count) (JsonPair "selected" (size-atom $selected))
                       (JsonPair "shard" $shard) (JsonPair "shards" $shards))))
                 (if (== $written ())
                   (ai-replay-main:finish (ai-math:replay-run $prepared
                     (AiITP:Budget 300000 200000 8000) (AiITP:Budget 600000 1000000 8000)))
                   (ai-replay-main:finish (AiReplay:Fault output-write $written)))))
              ($failure (ai-replay-main:finish $failure))))))))))
