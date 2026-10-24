; Best-first search over partial scripts, using the current goal state's
; symbols for premise selection. Import the prover, llm and proof_state APIs.

(= (ai-math:research-concat $blocks)
   (foldl-atom $blocks () $out $block (union-atom $out $block)))
(= (ai-math:incremental-steps $search $itp $target $state $have $used $k $definitions $seed)
   (let* (($index (index-atom (ai-math:get (index-atom $itp 1) $target AiMissing) 1))
          ($original (ai-math:search-goal $search $index))
          ($symbols (ai-math:state-symbols $itp $state))
          ($query (AiSearchFact $index THM $target $symbols () (ai-math:declaration-features $original)))
          ($ranked (ai-math:entry-names (ai-math:rank-for $search $index $query 60 ())))
          ($pool (unique-atom (union-atom
            (filter-atom $seed $name (not (ai-math:contains $used $name)))
            (filter-atom $ranked $name
              (case (ai-math:get (index-atom $itp 1) $name AiMissing)
                (((AiITP:Declaration $i $kind)
                  (and (ai-math:contains (THM AXIOM) $kind) (not (ai-math:contains $used $name))))
                 ($other false)))))))
          ($facts (list:take $k (filter-atom $pool $name
             (ai-math:itp-context-names $itp $index ($name) false))))
          ($live (filter-atom $symbols $name
            (and (not (ai-math:contains ("True" "False" "not" "and" "or" "iff" "eq" "neq" "ex") $name))
              (case (ai-math:get (index-atom $itp 1) $name AiMissing)
                (((AiITP:Declaration $i DEF) true) ($other false))))))
          ($bridge (ai-math:prover-bridge))
          ($unfold (str:join ", " (cons-atom $bridge (ai-math:lean-names (if (== $live ()) $definitions $live)))))
          ($all (if (== $facts ()) "True.intro" (str:join ", " (ai-math:lean-names $facts))))
          ($bulk (str:join "" (map-atom (collapse (ai-math:positions 0 (size-atom $facts))) $i
            (str:join "" ("have hq" (str:number->string (+ $have $i)) " := @"
              (ai-math:lean-name (index-atom $facts $i)) "\n")))))
          ($sweep (str:join "" ("all_goals ((try intros); (try simp only [" $bridge
            "] at *); (first | grind | solve_by_elim (maxDepth := 10) [" $all "]))")))
          ($have-name (str:concat "h" (str:number->string $have))))
     (ai-math:research-concat
       ((if (== $facts ()) ()
          (union-atom
            ((AiITP:Candidate "have-all" (str:trim $bulk))
             (AiITP:Candidate "have-all-grind" (str:join "" ($bulk "simp only [" $bridge "] at *\ngrind"))))
            (map-atom (collapse (ai-math:positions 0 (size-atom (list:take 4 $facts)))) $i
              (AiITP:Candidate (str:concat "apply-sweep-" (index-atom $facts $i))
                (str:join "" ($bulk "apply hq" (str:number->string (+ $have $i)) "\n" $sweep))))))
        ((AiITP:Candidate "grind" "grind")
         (AiITP:Candidate "norm-grind" (str:join "" ("simp only [" $bridge "] at *\ngrind")))
         (AiITP:Candidate "all-grind" "all_goals grind")
         (AiITP:Candidate "all-norm-grind" (str:join "" ("all_goals (simp only [" $bridge "] at * <;> grind)"))))
        (if (== $facts ()) ()
          ((AiITP:Candidate "grind-prem" (str:join "" ("simp only [" $bridge "] at *\ngrind [" $all "]")))
           (AiITP:Candidate "sbe-prem" (str:join "" ("simp only [" $bridge "] at *\nsolve_by_elim (maxDepth := 8) [" $all "]")))))
        (if (== $live ()) ()
          ((AiITP:Candidate "unfold-grind" (str:join "" ("simp only [" $unfold "] at *\ngrind")))))
        ((AiITP:Candidate "intros" "intros")
         (AiITP:Candidate "norm" (str:join "" ("simp only [" $bridge "] at *"))))
        (map-atom (list:take 3 $live) $definition
          (AiITP:Candidate (str:concat "unfold-" $definition)
            (str:join "" ("simp only [" (ai-math:lean-name $definition) "] at *\ntry intros"))))
        (ai-math:research-concat (map-atom $facts $fact
          ((AiITP:Candidate (str:concat "have-" $fact) (str:join "" ("have " $have-name " := @" (ai-math:lean-name $fact))))
           (AiITP:Candidate (str:concat "apply-" $fact) (str:concat "apply @" (ai-math:lean-name $fact))))))
        (ai-math:research-concat (map-atom (list:take 3 $facts) $fact
          ((AiITP:Candidate (str:concat "rw-" $fact)
             (str:join "" ("simp only [" $bridge "] at *\nrw [@" (ai-math:lean-name $fact) "]")))
           (AiITP:Candidate (str:concat "rwr-" $fact)
             (str:join "" ("simp only [" $bridge "] at *\nrw [← @" (ai-math:lean-name $fact) "]"))))))))))

(= (ai-math:inc-add $statistics $key $amount)
   (ai-math:put $statistics $key (+ (ai-math:get $statistics $key 0) $amount)))
(= (ai-math:inc-issue $statistics $issue $fault)
   (let* (($recorded (ai-math:put $statistics Issues (cons-atom $issue (ai-math:get $statistics Issues ()))))
          ($counted (ai-math:inc-add $statistics (if $fault Faults Unfinished) 1))) ()))
(= (ai-math:inc-elapsed (AiInc:Run $s $itp $n $seed $defs $gd $battery $options $stats $seen $started))
   (let $ns (- (system:monotonic-ns) $started) (/ (- $ns (% $ns 1000000)) 1000000)))
(= (ai-math:inc-active $run)
   (let (AiInc:Run $s $itp $n $seed $defs $gd $b $options $stats $seen $started) $run
     (and (== (ai-math:get $stats Winner AiInc:NoWinner) AiInc:NoWinner)
       (and (< (ai-math:get $stats Probes 0) (ai-math:option $options max-probes 10))
         (ai-math:inc-before-deadline $run)))))
(= (ai-math:inc-before-deadline $run)
   (let $deadline (ai-math:option (index-atom $run 8) deadline-ms 0)
     (or (== $deadline 0) (< (ai-math:inc-elapsed $run) $deadline))))
(= (ai-math:inc-budget $run $key)
   (let (AiInc:Run $s $itp $n $seed $defs $gd $b $options $stats $seen $started) $run
     (ai-math:itp-retry-budget (ai-math:option $options $key (AiITP:Budget 30000 200000 8000))
       (ai-math:option $options deadline-ms 0) (ai-math:inc-elapsed $run))))
(= (ai-math:inc-node-key (AiInc:Node $script $goals $depth $used $have))
   (json:stringify (JsonArray $goals)))
(= (ai-math:inc-sort-nodes $nodes)
   (map-atom (sort-atom (map-atom (collapse (ai-math:positions 0 (size-atom $nodes))) $i
       (let (AiInc:Node $script $goals $depth $used $have) (index-atom $nodes $i)
         ($depth (size-atom $goals) (foldl-atom $goals 0 $sum $goal (+ $sum (str:codepoint-count $goal)))
           $i (index-atom $nodes $i))))) $row (index-atom $row 4)))
(= (ai-math:inc-unique-candidates $candidates)
   (let* (($seen (new-space))
          ($out (foldl-atom $candidates () $out $candidate
            (let $script (index-atom $candidate 2)
              (if (ai-math:get $seen $script false) $out
                (let $saved (ai-math:put $seen $script true) (cons-atom $candidate $out)))))))
     (list:reverse $out)))
(= (ai-math:incremental-options-valid $options)
   (if (== (get-metatype $options) Expression)
     (and (foldl-atom $options true $ok $entry
       (and $ok (case $entry
         ((($key $value)
           (if (ai-math:contains (max-depth max-probes beam k chunk-size deadline-ms) $key)
             (ai-math:natural $value)
             (if (ai-math:contains (probe-budget check-budget) $key) (ai-math:itp-budget-valid $value) false)))
          ($other false)))))
       (and (> (ai-math:option $options max-probes 10) 0)
         (and (> (ai-math:option $options beam 3) 0) (> (ai-math:option $options chunk-size 10) 0)))) false))
(= (ai-math:incremental-prove $context $target $hints $options)
   (if (ai-math:incremental-options-valid $options)
     (case ($context $hints)
       ((((AiProver $search $thf $itp $vampire $policy) (AiProver:Hints $sets $defs $goal-defs $status $trace))
         (case (ai-math:get (index-atom $itp 1) $target AiMissing)
           (((AiITP:Declaration $index THM)
             (let* (($definitions (sort-atom (unique-atom (union-atom $defs $goal-defs))))
                    ($seed (unique-atom (ai-math:research-concat $sets)))
                    ($battery (ai-math:inc-unique-candidates
                      (union-atom (ai-math:research-concat (map-atom (if (== $sets ()) (()) $sets) $premises
                        (ai-math:candidate-tactics $premises $definitions $goal-defs)))
                        (if (== $seed ()) () (ai-math:apply2-tactics (list:take 6 $seed) $definitions)))))
                    ($stats (new-space)) ($seen (new-space))
                    ($run (AiInc:Run $search $itp $target $seed $definitions $goal-defs $battery $options $stats $seen (system:monotonic-ns))))
               (if (and (ai-math:itp-context-names $itp $index $seed false)
                        (ai-math:itp-context-names $itp $index $definitions true))
                 (if (ai-math:inc-active $run)
                   (let* (($counted (ai-math:inc-add $stats Probes 1))
                          ($root (ai-math:probe-with $itp $target "skip" (ai-math:inc-budget $run probe-budget))))
                     (case $root
                       (((AiProbe:Open $goals)
                         (let* (($node (AiInc:Node "" $goals 0 () 0))
                                ($saved (ai-math:put $seen (ai-math:inc-node-key $node) true)))
                           (ai-math:inc-search $run ($node))))
                        ($other (let $issue (ai-math:inc-issue $stats $other
                                  (case $other (((AiProbe:Unfinished $why) false) ($other true))))
                          (ai-math:inc-finish $run root-failure))))))
                   (ai-math:inc-finish $run deadline))
                 (AiInc:Fault invalid-source-context))))
            ($other (AiInc:Fault unknown-target)))))
        ($other (AiInc:Fault preparation))))
     (AiInc:Fault invalid-policy)))
(= (ai-math:inc-finish $run $reason)
   (let (AiInc:Run $s $itp $target $seed $defs $gd $b $options $stats $seen $started) $run
     (let* (($issues (list:reverse (ai-math:get $stats Issues ())))
            ($outcome (ai-math:get $stats Winner
              (if (> (ai-math:get $stats Faults 0) 0) (AiProver:Faulted $issues)
                (if (not (== $issues ())) (AiProver:Unfinished $issues)
                  (AiProver:NotProved (AiProver:Coverage (incremental))))))))
       (AiInc:Result $target $outcome
         (AiInc:Statistics (ai-math:get $stats Probes 0) (ai-math:get $stats Candidates 0)
           (ai-math:get $stats Closed 0) (ai-math:get $stats Errors 0) (ai-math:get $stats Repeated 0)
           $issues $reason)))))
(= (ai-math:inc-search $run $frontier)
   (let (AiInc:Run $search $itp $target $seed $defs $gd $battery $options $stats $seen $started) $run
     (if (or (== $frontier ()) (not (ai-math:inc-active $run)))
       (ai-math:inc-finish $run (if (== $frontier ()) exhausted budget))
       (let* (($ordered (ai-math:inc-sort-nodes $frontier))
              ((AiInc:Node $prefix $goals $depth $used $have) (car-atom $ordered))
              ($rest (list:take (* 4 (ai-math:option $options beam 3)) (cdr-atom $ordered))))
         (if (>= $depth (ai-math:option $options max-depth 3)) (ai-math:inc-search $run $rest)
           (let* (($steps (ai-math:incremental-steps $search $itp $target (car-atom $goals) $have $used
                           (ai-math:option $options k 6) $defs $seed))
                  ($candidates (union-atom (if (== $depth 0) (list:take 24 $battery) ()) $steps))
                  ($counted (ai-math:inc-add $stats Candidates (size-atom $candidates)))
                  ($kids (ai-math:inc-chunks $run (car-atom $ordered) $candidates ()))
                  ($next (union-atom (list:take (ai-math:option $options beam 3) (ai-math:inc-sort-nodes $kids)) $rest)))
             (ai-math:inc-search $run $next)))))))
(= (ai-math:inc-chunks $run $node $candidates $children)
   (if (or (== $candidates ()) (not (ai-math:inc-active $run))) $children
     (let* (((AiInc:Run $s $itp $target $seed $defs $gd $b $options $stats $seen $started) $run)
            ((AiInc:Node $prefix $goals $depth $used $have) $node)
            ($size (ai-math:option $options chunk-size 10))
            ($chunk (list:take $size $candidates))
            ($full (map-atom $chunk $candidate
              (let (AiITP:Candidate $label $script) $candidate
                (AiITP:Candidate $label (if (== $prefix "") $script (str:join "\n" ($prefix $script)))))))
            ($counted (ai-math:inc-add $stats Probes 1))
            ($observed (ai-math:probe-batch $itp $target $full (ai-math:inc-budget $run probe-budget)))
            ($kids (case $observed
              (((AiProbe:Batch $name $rows) (ai-math:inc-observe-rows $run $node $full $rows $children))
               ($other (let $issue (ai-math:inc-issue $stats $other
                 (case $other (((AiProbe:Unfinished $evidence) false) ($other true)))) $children))))))
       (ai-math:inc-chunks $run $node (list:drop $size $candidates) $kids))))
(= (ai-math:inc-observe-rows $run $node $candidates $observations $children)
   (if (or (== $candidates ())
           (not (== (ai-math:get (index-atom $run 9) Winner AiInc:NoWinner) AiInc:NoWinner))) $children
     (let* (((AiITP:Candidate $label $script) (car-atom $candidates))
            ((AiProbe:Attempt $same $observation) (car-atom $observations))
            ($next (ai-math:inc-observe $run $node $label $script $observation $children)))
       (ai-math:inc-observe-rows $run $node (cdr-atom $candidates) (cdr-atom $observations) $next))))
(= (ai-math:inc-observe $run $node $label $script $observation $children)
   (let* (((AiInc:Run $s $itp $target $seed $defs $gd $b $options $stats $seen $started) $run)
          ((AiInc:Node $prefix $old-goals $depth $used $have) $node))
     (case $observation
       (((AiProbe:Closed $advice)
         (if (ai-math:inc-before-deadline $run)
          (let* (($counted (ai-math:inc-add $stats Closed 1))
                ($checked (ai-math:itp-check-with $itp $target $script (ai-math:inc-budget $run check-budget))))
           (case $checked
             (((AiITP:Accepted $name $dependencies $axioms)
               (let $saved (ai-math:put $stats Winner
                 (AiProver:Proved incremental $depth $label $script $dependencies $axioms)) $children))
              ((AiITP:Rejected $n $why $details) (let $counted (ai-math:inc-add $stats Errors 1) $children))
              ($other (let $issue (ai-math:inc-issue $stats $other
                        (case $other (((AiITP:Fault $n $why $evidence) true) ($other false)))) $children)))))
          (let $issue (ai-math:inc-issue $stats (AiITP:Unfinished $target deadline ()) false) $children)))
        ((AiProbe:Open $goals)
         (let* (($is-have (str:starts-with $label "have-"))
                ($kid (AiInc:Node $script $goals (+ $depth 1)
                  (if $is-have (unique-atom (cons-atom (str:byte-slice $label 5 (str:byte-length $label)) $used)) $used)
                  (if $is-have (+ $have 1) $have)))
                ($key (ai-math:inc-node-key $kid)))
           (if (ai-math:get $seen $key false)
             (let $counted (ai-math:inc-add $stats Repeated 1) $children)
             (let $saved (ai-math:put $seen $key true) (cons-atom $kid $children)))))
        ((AiProbe:Error $why) (let $counted (ai-math:inc-add $stats Errors 1) $children))
        ($other (let $issue (ai-math:inc-issue $stats $other
                   (case $other (((AiProbe:Fault $evidence) true) ($other false)))) $children))))))
