; Zipperposition consumes the existing THF boundary. Status and premise
; names are untrusted advice; reconstruction still goes through Lean.
(= (ai-math:zipperposition $context $problem $executable $seconds $mode)
   (if (and (ai-math:natural $seconds)
            (and (== (get-type $executable) String) (== (get-type $mode) String)))
     (let $text (ai-math:thf-text $context $problem)
       (if (== (get-type $text) String)
         (let $command (union-atom
            ($executable "--input" "tptp" "--output" "tptp" "--timeout" (str:number->string $seconds))
            (if (== $mode "") () ("--mode" $mode)))
           (ai-math:zipper-observation $context $problem
             (proc:run $command ((lifetime owner) (stdin $text)
               (timeout-ms (if (== $seconds 0) 0 (+ (* 1000 $seconds) 20000)))))))
         $text)) (AiATP:ZipperFault invalid-policy)))
(= (ai-math:zipper-inputs $records)
   (map-atom (filter-atom (list:to-expression $records) $record
       (case (tptp:record-role $record)
         (((TPTP:RecordRole $role) (ai-math:contains (axiom hypothesis definition) $role)) ($other false))))
     $record (let (TPTP:RecordName $id) (tptp:record-name $record)
       (TPTP:InputReference $id "stdin" $id))))
(= (ai-math:zipper-payload $context $envelope)
   (let* (((AiTHF $count $index (AiTHF:Formats $reader $printer)) $context)
          ($blocks (tptp:szs-data $envelope)))
     (foldl-atom $blocks (AiATP:ZipperInputs ()) $state $block
       (case $state
         (((AiATP:ZipperInputs $out)
           (let (TPTP:SZSData $kind $body $start $end) $block
             (if (ai-math:contains ("Proof" "Refutation" "CNFRefutation") $kind)
               (let $records (tptp:read-text $reader mixed $body)
                 (if (list:is-list $records)
                   (AiATP:ZipperInputs (union-atom $out (ai-math:zipper-inputs $records)))
                   (AiATP:PayloadInterpretationNeeded $records))) $state)))
          ($other $other))))))
(= (ai-math:zipper-observation $context $problem $observation)
   (case $observation
     (((proc:result (proc:exited 0) proc:normal $stdout $stderr
         (proc:capture $seen $kept $es $ek proc:eof proc:eof (proc:input $size $sent)))
       (let $envelope (tptp:szs-output $stdout)
         (if (and (== $seen $kept) (and (== $es $ek) (== $size $sent)))
           (ai-math:zipper-envelope $context $problem $observation $envelope)
           (AiATP:ZipperReport (AiATP:IncompleteCapture (tptp:szs-status $envelope)) $observation $envelope))))
      ($other (AiATP:ZipperReport (AiATP:UnfinishedOrFaulted $other) $other ())))))
(= (ai-math:zipper-envelope $context $problem $observation $envelope)
   (case $envelope
     (((TPTP:SZSEnvelope $statuses $blocks TPTP:SZSComplete ())
       (case (tptp:szs-status $envelope)
         (((TPTP:SZSReported $word)
           (AiATP:ZipperReport (ai-math:zipper-summary $context $problem $envelope $word) $observation $envelope))
          ($other (AiATP:ZipperReport (AiATP:UnresolvedStatus $other) $observation $envelope)))))
      ($other (AiATP:ZipperReport (AiATP:UnresolvedStatus $envelope) $observation $envelope)))))
(= (ai-math:zipper-summary $context $problem $envelope $word)
   (if (ai-math:contains ("Theorem" "Unsatisfiable" "ContradictoryAxioms") $word)
     (if (== (tptp:szs-data $envelope) ()) (AiATP:PayloadInterpretationNeeded missing-refutation)
       (case (ai-math:zipper-payload $context $envelope)
         (((AiATP:ZipperInputs $references)
           (AiATP:Advice "Theorem" (ai-math:vampire-premises $problem $references)
             (ai-math:vampire-definitions $context $references)))
          ($other $other))))
     (AiATP:Advice $word () ())))
