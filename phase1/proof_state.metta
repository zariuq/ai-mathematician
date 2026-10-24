; Partial states are advisory observations, never certificates. The fixed
; instrumentation runs in the existing isolated proposer. A closed prefix
; must still be checked without instrumentation before it is published.
(= (ai-math:probe-instrumentation)
   "\nrun_tac\n  let gs ← Lean.Elab.Tactic.getGoals\n  let states ← gs.toArray.mapM fun g => do\n    return (← Lean.Meta.ppGoal g).pretty\n  Lean.logInfo m!\"CETTA-PROBE-V1:{(Lean.toJson states).compress}\"\n")
(= (ai-math:probe-decode $answer)
   (case $answer
     (((AiITP:Accepted $name $used $axioms) (AiProbe:Closed $answer))
      ((AiITP:Rejected $name "lean-errors" $reply)
       (case (json:get $reply "messages")
         (((JsonArray $messages)
           (let* (($markers (filter-atom $messages $text
                     (> (size-atom (str:split "CETTA-PROBE-V1:" $text)) 1)))
                  ($errors (filter-atom $messages $text
                     (and (> (size-atom (str:split "error:" $text)) 1)
                       (== (size-atom (str:split "error: unsolved goals" $text)) 1)))))
             (if (and (== (size-atom $markers) 1) (== $errors ()))
               (let $parts (str:split "CETTA-PROBE-V1:" (car-atom $markers))
                 (if (== (size-atom $parts) 2)
                   (case (json:parse (str:trim (index-atom $parts 1)))
                     (((JsonArray $states)
                       (if (and (> (size-atom $states) 0) (ai-math:itp-string-array $states))
                         (AiProbe:Open $states) (AiProbe:Error invalid-state-record)))
                      ($other (AiProbe:Error invalid-state-record))))
                   (AiProbe:Error ambiguous-state-record)))
               (AiProbe:Error $answer))))
          ($other (AiProbe:Error $answer)))))
      ((AiITP:Unfinished $name $why $evidence) (AiProbe:Unfinished $answer))
      ((AiITP:Fault $name $why $evidence) (AiProbe:Fault $answer))
      ($other (AiProbe:Error $answer)))))
(= (ai-math:probe-batch $itp $target $candidates $budget)
   (case (ai-math:itp-batch-with $itp $target
     (map-atom $candidates $candidate
       (let (AiITP:Candidate $label $script) $candidate
         (AiITP:Candidate $label (str:concat $script (ai-math:probe-instrumentation))))) $budget)
     (((AiITP:Batch $name $rows)
       (AiProbe:Batch $name (map-atom $rows $row
         (let (AiITP:Attempt $label $answer) $row (AiProbe:Attempt $label (ai-math:probe-decode $answer))))))
      ($other (ai-math:probe-decode $other)))))
(= (ai-math:probe-with $itp $target $script $budget)
   (case (ai-math:probe-batch $itp $target ((AiITP:Candidate "probe" $script)) $budget)
     (((AiProbe:Batch $name ((AiProbe:Attempt "probe" $answer))) $answer)
      ($other $other))))
(= (ai-math:state-symbols (AiITP $facts $root $lean $profile) $text)
   (let* (($plain (str:join "" (str:split "✝" $text)))
          ($parser (re:prepare (re:pattern "«[^»]+»|[A-Za-z_][A-Za-z_0-9']*"))))
     (case (re:find-all $parser $plain)
       (((re:matches $matches)
         (sort-atom (unique-atom (filter-atom
           (map-atom (ai-math:llm-piece-list $matches) $match
             (let $name (re:group-text $match $plain 0)
               (if (str:starts-with $name "«")
                 (str:from-codepoints (list:take (- (str:codepoint-count $name) 2)
                   (list:drop 1 (str:codepoints $name)))) $name)))
           $name (not (== (ai-math:get $facts $name AiMissing) AiMissing))))))
        ($other ())))))
