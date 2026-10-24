; Untrusted Lean proposals with checked feedback. Import re and the
; application HTTP/chat transports in addition to the normal prover APIs.

(= (ai-math:llm-code-parser)
   (let* (($fences (re:prepare (re:pattern "(?s)```(?:lean4?|)\\s*\\n(.*?)```")))
          ($header (re:prepare (re:pattern "(?s)^\\s*(?:theorem|lemma|example)\\b.*?:=\\s*by\\s*\\n(.*)$")))
          ($lines (re:prepare (re:pattern "\\r\\n|[\\n\\r\\x{b}\\x{c}\\x{1c}-\\x{1e}\\x{85}\\x{2028}\\x{2029}]")))
          ($bridge (re:prepare (re:pattern "^simp only \\[\\s*(?:b_\\w+\\s*,\\s*)*b_\\w+\\s*\\] at \\*\\s*$")))
          ($rstrip (re:prepare (re:pattern "[\\s\\x{1c}-\\x{1f}]+$"))))
     (AiLLM:CodeParser $fences $header $lines $bridge $rstrip)))
(= (ai-math:llm-last-block $matches $reply $last)
   (case $matches
     ((LNil $last)
      ((LCons $match $rest)
       (let $text (re:group-text $match $reply 1)
         (if (== (get-type $text) String) (ai-math:llm-last-block $rest $reply $text)
           (AiLLM:Fault code-extraction)))))))
(= (ai-math:llm-leading $line $position)
   (if (>= $position (str:byte-length $line)) $position
     (if (ai-math:contains (" " "\t") (str:byte-slice $line $position (+ $position 1)))
       (ai-math:llm-leading $line (+ $position 1)) $position)))
(= (ai-math:llm-unindent $text)
   (let* (($lines (str:split "\n" $text))
          ($nonempty (filter-atom $lines $line (not (== (str:trim $line) ""))))
          ($pad (if (== $nonempty ()) 0
            (foldl-atom $nonempty (str:byte-length (car-atom $nonempty)) $minimum $line
              (let $count (ai-math:llm-leading $line 0) (if (< $count $minimum) $count $minimum))))))
     (str:trim (str:join "\n" (map-atom $lines $line
       (str:byte-slice $line (if (< (str:byte-length $line) $pad) (str:byte-length $line) $pad) (str:byte-length $line)))))))
(= (ai-math:llm-strip-fence-label $text)
   (let* (($lines (str:split "\n" $text)) ($head (str:trim (car-atom $lines))))
     (if (ai-math:contains ("" "lean" "lean4") $head) (str:join "\n" (cdr-atom $lines)) $text)))
(= (ai-math:llm-extract (AiLLM:CodeParser $fences $header $lines $bridge $rstrip) $reply)
   (case (re:find-all $fences $reply)
     (((re:matches $matches)
       (let* (($block (ai-math:llm-last-block $matches $reply AiLLM:NoBlock))
              ($raw (if (== $block AiLLM:NoBlock)
                (let $parts (str:split "```" $reply)
                  (if (> (size-atom $parts) 1)
                    (ai-math:llm-strip-fence-label (index-atom $parts (- (size-atom $parts) 1))) $reply)) $block))
              ($text (ai-math:llm-unindent $raw))
              ($head (re:find $header $text))
              ($part (re:group-text $head $text 1))
              ($body (if (== (get-type $part) String) (ai-math:llm-unindent $part) $text)))
         (if (str:starts-with $body "by\n") (str:byte-slice $body 3 (str:byte-length $body)) $body)))
      ($other (AiLLM:Fault code-extraction)))))
; Formatting produces proposals only. Every normalized or repaired script
; returns through the same independent proof checker as the original.
(= (ai-math:llm-piece-list LNil) ())
(= (ai-math:llm-piece-list (LCons $head $rest))
   (cons-atom $head (ai-math:llm-piece-list $rest)))
(= (ai-math:llm-lines (AiLLM:CodeParser $f $h $lines $b $r) $text)
   (if (== $text "") ()
     (case (re:split $lines $text)
       (((re:pieces $pieces)
         (let $reversed (list:reverse (ai-math:llm-piece-list $pieces))
           (list:reverse (if (== (car-atom $reversed) "") (cdr-atom $reversed) $reversed))))
        ($other (AiLLM:Fault line-split))))))
(= (ai-math:llm-dedented $lines)
   (if (== $lines ()) AiLLM:NoRepair
     (let* (($head (car-atom $lines)) ($body (cdr-atom $lines))
            ($nonempty (filter-atom $body $line (not (== (str:trim $line) "")))))
       (if (or (== $nonempty ())
               (or (str:starts-with $head " ") (str:starts-with $head "\t"))) AiLLM:NoRepair
         (if (foldl-atom ("by" ":=" "=>" "·") false $found $suffix
               (or $found (str:ends-with (str:trim $head) $suffix))) AiLLM:NoRepair
           (let $pad (foldl-atom $nonempty (str:byte-length (car-atom $nonempty)) $minimum $line
                        (let $count (ai-math:llm-leading $line 0) (if (< $count $minimum) $count $minimum)))
             (if (== $pad 0) AiLLM:NoRepair
               (AiLLM:Lines (cons-atom $head (map-atom $body $line
                 (if (== (str:trim $line) "") $line
                   (str:byte-slice $line $pad (str:byte-length $line)))))))))))))
(= (ai-math:llm-dedent-or $lines)
   (case (ai-math:llm-dedented $lines)
     (((AiLLM:Lines $changed) $changed) ($other $lines))))
(= (ai-math:llm-normalize (AiLLM:CodeParser $f $h $line-parser $bridge $r) $script)
   (str:join "\n" (map-atom
     (ai-math:llm-dedent-or (ai-math:llm-lines (AiLLM:CodeParser $f $h $line-parser $bridge $r) $script)) $line
     (if (re:is-match $bridge $line) (str:concat "try " $line) $line))))
(= (ai-math:llm-rstrip (AiLLM:CodeParser $f $h $l $b $rstrip) $script)
   (let $text (re:replace-literal $rstrip $script "")
     (if (== (get-type $text) String) $text (AiLLM:Fault whitespace-repair))))
(= (ai-math:llm-insert-bridge $lines $wanted $index)
   (if (== $lines ()) ()
     (if (== $wanted $index)
       (cons-atom (str:join "" ("simp only [" (ai-math:prover-bridge) "] at *")) $lines)
       (cons-atom (car-atom $lines)
         (ai-math:llm-insert-bridge (cdr-atom $lines) $wanted (+ $index 1))))))
(= (ai-math:llm-bridged $lines)
   (let (AiLLM:Last $count $last)
     (foldl-atom $lines (AiLLM:Last 0 -1) $state $line
       (let (AiLLM:Last $i $last) $state
         (AiLLM:Last (+ $i 1)
           (if (and (not (== (str:trim $line) ""))
                    (not (or (str:starts-with $line " ")
                         (or (str:starts-with $line "\t") (str:starts-with $line "--"))))) $i $last))))
     (if (> $last 0) (AiLLM:Lines (ai-math:llm-insert-bridge $lines $last 0)) AiLLM:NoRepair)))
(= (ai-math:llm-repair-bases $lines)
   (let* (($bridge (case (ai-math:llm-bridged $lines)
                    (((AiLLM:Lines $ls) (("-bridge" $ls))) ($other ()))))
          ($dedent (case (ai-math:llm-dedented $lines)
                    (((AiLLM:Lines $ls)
                      (union-atom (("-dedent" $ls))
                        (case (ai-math:llm-bridged $ls)
                          (((AiLLM:Lines $both) (("-dedent-bridge" $both))) ($other ())))))
                     ($other ())))))
     (union-atom (("" $lines)) (union-atom $bridge $dedent))))
(= (ai-math:llm-repair-variants $parser $script $why $premises $label)
   (let $lines (ai-math:llm-lines $parser (ai-math:llm-rstrip $parser $script))
     (if (== $lines ()) ()
       (let* (($bases (ai-math:llm-repair-bases $lines))
              ($sbe (str:join "" ("solve_by_elim (maxDepth := 8)"
                      (if (== $premises ()) "" (str:join "" (" [" (str:join ", " (ai-math:lean-names $premises)) "]"))))))
              ($closer ((str:join "" ("all_goals (try simp only [" (ai-math:prover-bridge) "] at *)"))
                         (str:join "" ("all_goals (first | grind | " $sbe " | (intros; grind) | assumption)"))))
              ($repairs (map-atom (cdr-atom $bases) $base
                          (let ($tag $ls) $base
                            (AiITP:Candidate (str:concat $label $tag) (str:join "\n" $ls)))))
              ($finish (if (or (> (size-atom (str:split "unsolved goals" $why)) 1)
                               (not (== (ai-math:llm-dedented $lines) AiLLM:NoRepair)))
                         (map-atom $bases $base (let ($tag $ls) $base
                           (AiITP:Candidate (str:join "" ($label $tag "-finish"))
                             (str:join "\n" (union-atom $ls $closer))))) ())))
         (union-atom $repairs $finish)))))
(= (ai-math:llm-error-text $result)
   (case $result
     (((AiITP:Rejected $n $r $reply) (ai-math:llm-diagnostics $reply $result))
      ((AiITP:Unfinished $n $r $reply) (ai-math:llm-diagnostics $reply $result))
      ($other (repr $result)))))
(= (ai-math:llm-diagnostics $reply $fallback)
   (case (json:get $reply "messages")
     (((JsonArray $messages)
       (str:join "\n" (map-atom $messages $entry
         (if (== (get-type $entry) String) $entry ""))))
      ($other (let $message (json:get $reply "message")
        (if (== (get-type $message) String) $message (repr $fallback)))))))

(= (ai-math:llm-system)
   "Write a Lean 4 tactic script, core Lean only, without Mathlib. Work in namespace Megalodon. The goal type is fixed. Use only the listed earlier facts and definitions; never use the theorem being proved. Megalodon.set is an opaque type, not an inductive set datatype. Membership facts need the listed introduction/elimination lemmas, not cases on set membership. Encoded logic can be rewritten by the proved bridge lemmas b_True, b_False, b_not, b_and, b_or, b_iff, b_eq, b_neq, b_ex, for example: try simp only [b_True, b_False, b_not, b_and, b_or, b_iff, b_eq, b_neq, b_ex] at *. For induction apply a listed earlier induction principle with an explicit motive. Introduce your own names for bound variables. Return one lean code block containing only the tactic script, with no theorem header, no admissions, no new axioms and no commands outside the proof.")
(= (ai-math:llm-prompt (AiITP:PromptContext $target $statement $definitions $facts))
   (str:join "\n" ((str:concat "Prove the fixed theorem «" (str:concat $target "»."))
     "Goal type:" $statement "Definitions:"
     (str:join "\n" (map-atom $definitions $row (index-atom $row 2)))
     "Available facts (types only):"
     (str:join "\n" (map-atom $facts $row (index-atom $row 2))))))
(= (ai-math:llm-clip $text $limit)
   (if (or (== $limit 0) (<= (str:codepoint-count $text) $limit)) $text
     (str:from-codepoints (list:take $limit (str:codepoints $text)))))
; Application-error hints are display data, never proof dependencies. Names
; must pass the same earlier-source check as the initial prompt. Signatures
; come from Lean's existing type-only context operation, not proof bodies or
; an unversioned external cache.
(= (ai-math:llm-misused-lemmas $why)
   (let $parser (re:prepare (re:pattern "in the application\\s*\\n\\s*@?([A-Za-z_][\\w'.]*)"))
     (case (re:find-all $parser $why)
       (((re:matches $matches)
          (unique-atom (map-atom (ai-math:llm-piece-list $matches) $match
            (let* (($name (re:group-text $match $why 1))
                   ($parts (str:split "." $name)))
              (index-atom $parts (- (size-atom $parts) 1))))))
        ($other ())))))
(= (ai-math:llm-signature-feedback $itp $target $why $budget $limit)
   (let $body (ai-math:llm-clip $why $limit)
     (case $itp
       (((AiITP $catalog $root $lean $profile)
          (case (ai-math:get $catalog $target AiMissing)
            (((AiITP:Declaration $index THM)
               (let $names (list:take 3
                 (filter-atom (ai-math:llm-misused-lemmas $why) $name
                   (ai-math:itp-context-names $itp $index ($name) false)))
                 (if (== $names ()) $body
                   (case (ai-math:itp-prompt-context $itp $target $names () $budget)
                     (((AiITP:PromptContext $name $statement $definitions $facts)
                        (str:join "\n" ($body
                          "" "The arguments must follow each lemma's signature, in this order:"
                          (str:join "\n" (map-atom $facts $fact (index-atom $fact 2))))))
                      ($other $body))))))
             ($other $body))))
        ($other $body)))))
(= (ai-math:llm-context-rows $rows $limit)
   (let (AiLLM:ContextSize $size $out $full)
     (foldl-atom $rows (AiLLM:ContextSize 0 () false) $state $row
       (let (AiLLM:ContextSize $seen $kept $stopped) $state
         (if $stopped $state
           (let $next (+ $seen (str:codepoint-count (index-atom $row 2)))
             (if (and (> $limit 0) (> $next $limit)) (AiLLM:ContextSize $seen $kept true)
               (AiLLM:ContextSize $next (cons-atom $row $kept) false))))))
     (list:reverse $out)))
(= (ai-math:llm-prompt-with (AiITP:PromptContext $name $statement $definitions $facts) $options)
   (ai-math:llm-prompt (AiITP:PromptContext $name $statement
     (ai-math:llm-context-rows $definitions (ai-math:option $options definition-chars 12000))
     (ai-math:llm-context-rows $facts (ai-math:option $options context-chars 80000)))))

; Examples are proposals until checked at their own source frontier. Their
; displayed statements come from Lean, never from a caller-supplied signature.
(= (ai-math:llm-example-pool $value)
   (case $value
     (((JsonObject $pairs)
       (let $examples (map-atom $pairs $pair
              (case $pair (((JsonPair $name $script) (AiLLM:Example $name $script))
                ($other AiLLM:InvalidExample))))
         (if (ai-math:llm-examples-valid $examples) $examples
           (AiLLM:Fault invalid-example-pool))))
      ($other (AiLLM:Fault invalid-example-pool)))))
(= (ai-math:llm-example-earlier (AiITP $catalog $r $l $p) $target $example)
   (case ((ai-math:get $catalog $target AiMissing)
          (ai-math:get $catalog (index-atom $example 1) AiMissing))
     ((((AiITP:Declaration $cutoff THM) (AiITP:Declaration $index THM)) (< $index $cutoff))
      ($other false))))
(= (ai-math:llm-select-examples $search $itp $target $pool $count)
   (let $earlier (filter-atom $pool $example (ai-math:llm-example-earlier $itp $target $example))
     (case $search
       (((AiSearch $size $facts $weights $training)
         (let* (($cutoff (index-atom (ai-math:get (index-atom $itp 1) $target AiMissing) 1))
                ($goal (ai-math:search-goal $search $cutoff))
                ($scored (map-atom $earlier $example
                  (let* (($name (index-atom $example 1))
                         ($index (index-atom (ai-math:get (index-atom $itp 1) $name AiMissing) 1))
                         ($fact (ai-math:search-fact-at $search $index)))
                    ((ai-math:overlap $search (ai-math:declaration-symbols $goal) $fact) $name $example)))))
           (map-atom (list:take $count (list:reverse (sort-atom
             (filter-atom $scored $row (> (index-atom $row 0) 0.0))))) $row (index-atom $row 2))))
        ($other (list:take $count $earlier))))))
(= (ai-math:llm-example-block $itp (AiLLM:Example $name $script) $budget)
   (case (ai-math:itp-check-with $itp $name $script $budget)
     (((AiITP:Accepted $same $used $axioms)
       (case (ai-math:itp-statement $itp $name)
         (((AiITP:Statement $same $statement)
           (AiLLM:ExampleBlock (str:join "" ("theorem «" $name "» : " $statement " := by\n"
             (str:join "\n" (map-atom (str:split "\n" $script) $line (str:concat "  " $line)))))))
          ($other (AiLLM:Fault example-statement)))))
      ($other (AiLLM:Fault example-not-checked)))))
(= (ai-math:llm-proof-prompt $search $itp $target $prompt $options $budget)
   (let* (($pool (ai-math:option $options examples ()))
          ($selected (ai-math:llm-select-examples $search $itp $target $pool
                       (ai-math:option $options example-count 3)))
          ($blocks (foldl-atom $selected (AiLLM:ExampleBlocks ()) $state $example
            (case $state
              (((AiLLM:ExampleBlocks $out)
                (case (ai-math:llm-example-block $itp $example $budget)
                  (((AiLLM:ExampleBlock $text) (AiLLM:ExampleBlocks (cons-atom $text $out)))
                   ($other $other)))) ($other $other))))))
     (case $blocks
       (((AiLLM:ExampleBlocks $out)
         (AiLLM:Prompt (if (== $out ()) $prompt
           (str:join "\n\n" ("Accepted Lean proofs of similar EARLIER theorems in this library:"
             (str:join "\n\n" (list:reverse $out)) "---" $prompt)))))
        ($other $other)))))

; Name suggestions are bounded type-only advice. Character-bigram overlap is
; a spelling heuristic, not proof evidence or a premise-ranking replacement.
(= (ai-math:llm-unknown-names $why)
   (let $parser (re:prepare (re:pattern "[Uu]nknown (?:identifier|constant) `([^`]+)`"))
     (case (re:find-all $parser $why)
       (((re:matches $matches)
         (list:take 4 (unique-atom (map-atom (ai-math:llm-piece-list $matches) $match
           (let $name (re:group-text $match $why 1)
             (if (str:starts-with $name "Megalodon.")
               (str:byte-slice $name 10 (str:byte-length $name)) $name))))))
        ($other ())))))
(= (ai-math:llm-name-grams $name)
   (let $characters (str:codepoints $name)
     (if (< (size-atom $characters) 2) $characters
       (unique-atom (map-atom (collapse (ai-math:positions 1 (size-atom $characters))) $i
         ((index-atom $characters (- $i 1)) (index-atom $characters $i)))))))
(= (ai-math:llm-near-names (AiITP $catalog $r $l $p) $target $unknown)
   (let* (($cutoff (index-atom (ai-math:get $catalog $target AiMissing) 1))
          ($names (collapse (match $catalog (AiEntry $name (AiITP:Declaration $i $kind))
            (if (and (< $i $cutoff) (ai-math:contains (THM AXIOM DEF) $kind)) $name (empty)))))
          ($grams (ai-math:llm-name-grams $unknown))
          ($scores (map-atom (sort-atom $names) $name
            (let* (($other (ai-math:llm-name-grams $name))
                   ($total (+ (size-atom $grams) (size-atom $other))))
              ($name (if (== $total 0) 0.0
                (/ (* 2.0 (size-atom (intersection-atom $grams $other))) $total)))))))
     (ai-math:entry-names (list:take 4 (ai-math:sort-scores
       (filter-atom $scores $row (>= (index-atom $row 1) 0.5)))))))
(= (ai-math:llm-name-feedback $itp $target $why $budget)
   (str:join "\n\n" (map-atom (ai-math:llm-unknown-names $why) $unknown
     (let $near (ai-math:llm-near-names $itp $target $unknown)
       (if (== $near ()) (str:concat $unknown " does not exist; use only listed facts.")
         (case (ai-math:itp-prompt-context $itp $target $near () $budget)
           (((AiITP:PromptContext $n $s $defs $facts)
             (str:join "\n" ((str:concat $unknown " does not exist. Closest real earlier names (types only):")
               (str:join "\n" (map-atom $facts $row (index-atom $row 2))))))
            ($other (str:concat $unknown " does not exist; use only listed facts.")))))))))
(= (ai-math:llm-feedback $itp $target $why $budget $limit)
   (let* (($body (ai-math:llm-signature-feedback $itp $target $why $budget $limit))
          ($hints (ai-math:llm-clip (ai-math:llm-name-feedback $itp $target $why $budget) 2500)))
     (if (== $hints "") $body (str:join "\n\n" ($body $hints)))))
(= (ai-math:llm-goal-state $itp $target $budget)
   (let* (($script (str:join "" ("intros\ntry simp only [" (ai-math:prover-bridge) "] at *\ndone")))
          ($checked (ai-math:itp-check-with $itp $target $script $budget))
          ($why (ai-math:llm-error-text $checked))
          ($parts (str:split "unsolved goals\n" $why)))
     (if (> (size-atom $parts) 1) (ai-math:llm-clip (str:trim (index-atom $parts 1)) 3000) "")))
(= (ai-math:llm-message $role $content)
   (JsonObject ((JsonPair "role" $role) (JsonPair "content" $content))))
(= (ai-math:llm-advice $context $client $target)
   (let $options (ai-math:llm-config $client Options)
     (if (ai-math:option $options proof-advice false)
       (ai-math:proof-advice $context $target (ai-math:option $options proof-chars 12000))
       AiATP:ProofDisabled)))
(= (ai-math:llm-advised-prompt $prompt $advice)
   (case $advice
     (((AiATP:ProofAdvice $name $slice $text $used $defs $evidence)
       (str:join "\n\n" ($prompt $text)))
      ($other $prompt))))
(= (ai-math:llm-advice-record $advice)
   (case $advice
     ((AiATP:ProofDisabled ())
      ((AiATP:ProofAdvice $name $slice $text $used $defs $evidence)
       ((AiLLM:ProofContext $name $slice $used $defs (str:sha256 $text))))
      ($other ((AiLLM:ProofContextUnavailable $other))))))
(= (ai-math:llm-trims $script)
   (let $lines (str:split "\n" $script)
     (map-atom (filter-atom (1 2 3) $count (< $count (size-atom $lines))) $count
       (AiITP:Candidate (str:concat "trim" (str:number->string $count))
         (str:join "\n" (list:take (- (size-atom $lines) $count) $lines))))))
(= (ai-math:llm-check-script $itp $target $script $budget)
   (ai-math:llm-check-script $itp $target $script $budget (ai-math:llm-code-parser) ()))
(= (ai-math:llm-check-script $itp $target $script $budget $parser $premises)
   (let (AiLLM:Checked $candidate $checked) (ai-math:llm-check-trims $itp $target $script $budget)
     (case $checked
       (((AiITP:Rejected $n $reason $details)
         (let $repairs (ai-math:llm-repair-variants $parser $candidate
                         (ai-math:llm-error-text $checked) $premises "repair")
           (if (== $repairs ()) (AiLLM:Checked $candidate $checked)
             (case (ai-math:itp-batch-with $itp $target $repairs $budget)
               (((AiITP:Batch $name $answers)
                 (case (ai-math:prover-winner (ai-math:prover-attempts llm-repair $repairs $answers 0))
                   (((AiProver:Proved $s $i $label $tactic $used $axioms)
                     (AiLLM:Checked $tactic (AiITP:Accepted $target $used $axioms)))
                    ($other (AiLLM:Checked $candidate $checked)))))
                ($other (AiLLM:Checked $candidate $checked)))))))
        ($other (AiLLM:Checked $candidate $checked))))))
(= (ai-math:llm-check-trims $itp $target $script $budget)
   (let $checked (ai-math:itp-check-with $itp $target $script $budget)
     (if (== (get-type (str:find (repr $checked) "No goals to be solved")) Number)
       (let $candidates (ai-math:llm-trims $script)
         (case (ai-math:itp-batch-with $itp $target $candidates $budget)
           (((AiITP:Batch $name $answers)
             (let $winner (ai-math:prover-winner (ai-math:prover-attempts llm-trim $candidates $answers 0))
               (case $winner
                 (((AiProver:Proved $stage $ordinal $label $tactic $used $axioms)
                   (AiLLM:Checked $tactic (AiITP:Accepted $target $used $axioms)))
                  ($other (AiLLM:Checked $script $checked))))))
            ($other (AiLLM:Checked $script $checked)))))
       (AiLLM:Checked $script $checked))))
(= (ai-math:llm-failure $target $reason)
   (case $reason
     (((AiLLM:Limit $cap) (AiITP:Unfinished $target call-budget $cap))
      ((AiLLM:ProviderRequest $kind) (AiITP:Unfinished $target interpretation-request $kind))
      ((AiLLM:AttemptFailed $n (AiHTTP:Unfinished $why) $usage) (AiITP:Unfinished $target $why $n))
      ((AiITP:Unfinished $n $why $details) $reason)
      ((AiITP:Fault $n $why $details) $reason)
      ($other (AiITP:Fault $target llm $other)))))
(= (ai-math:llm-finished $target $transcript)
   (let $attempts (foldl-atom $transcript () $out $entry
     (case $entry
       (((AiLLM:Round $round $label $script $result $receipt)
         (union-atom $out ((AiProver:Attempt llm $round $label $script $result))))
        ((AiLLM:RoundFault $round $reason)
         (union-atom $out ((AiProver:StageFault llm (ai-math:llm-failure $target $reason)))))
        ((AiLLM:ProofContext $name $slice $used $defs $digest) $out)
        ((AiLLM:ProofContextUnavailable $reason) $out)
        ($other (union-atom $out ((AiProver:StageFault llm (AiITP:Fault $target transcript $other))))))))
     (AiLLM:Result $target $transcript (ai-math:prover-outcome $attempts (llm)))))
(= (ai-math:proposal-loop $itp $client $target $parser $prefix $messages $round $remaining $budget $transcript $premises)
   (if (== $remaining 0) (ai-math:llm-finished $target $transcript)
     (case (ai-math:llm-chat $client $messages
             (ai-math:option (ai-math:llm-config $client Options) retries 4))
       (((AiLLM:Reply $reply $receipt)
         (let $sketch (ai-math:llm-normalize $parser (ai-math:llm-extract $parser $reply))
           (if (== (get-type $sketch) String)
             (let* (($script (str:concat $prefix $sketch))
                    ((AiLLM:Checked $candidate $result) (ai-math:llm-check-script $itp $target $script $budget $parser $premises))
                    ($label (str:concat "llm-r" (str:number->string $round)))
                    ($entry (AiLLM:Round $round $label $candidate $result $receipt))
                    ($next (union-atom $transcript ($entry)))
                    ($winner (ai-math:prover-winner ((AiProver:Attempt llm $round $label $candidate $result)))))
               (if (== $winner AiProver:NoWinner)
                 (ai-math:proposal-loop $itp $client $target $parser $prefix
                   (union-atom $messages
                     ((ai-math:llm-message "assistant" (str:join "" ("```lean\n" $sketch "\n```")))
                      (ai-math:llm-message "user" (str:concat "Lean did not accept this proposal. Fix it; return only a lean tactic block.\n"
                        (ai-math:llm-feedback $itp $target (ai-math:llm-error-text $result) $budget
                          (ai-math:option (ai-math:llm-config $client Options) feedback-chars 2500))))))
                   (+ $round 1) (- $remaining 1) $budget $next $premises)
                 (AiLLM:Result $target $next $winner)))
             (ai-math:llm-finished $target (union-atom $transcript ((AiLLM:RoundFault $round $sketch)))))))
        ($other (ai-math:llm-finished $target (union-atom $transcript ((AiLLM:RoundFault $round $other)))))))))
(= (ai-math:llm-prove $context $client $target $premises $definitions $rounds $budget)
   (case $context
     (((AiProver $search $thf $itp $vampire $options)
       (if (and (ai-math:itp-natural $rounds) (ai-math:itp-budget-valid $budget))
         (case (ai-math:itp-prompt-context $itp $target $premises $definitions $budget)
           (((AiITP:PromptContext $name $statement $defs $facts)
             (let* (($parser (ai-math:llm-code-parser))
                    ($policy (ai-math:llm-config $client Options))
                    ($state (if (ai-math:option $policy goal-state true)
                              (ai-math:llm-goal-state $itp $target $budget) ""))
                    ($prompt (ai-math:llm-proof-prompt $search $itp $target
                      (ai-math:llm-prompt-with (AiITP:PromptContext $name $statement $defs $facts) $policy) $policy $budget)))
               (case $prompt
                 (((AiLLM:Prompt $text)
                   (let* (($advice (ai-math:llm-advice $context $client $target))
                          ($advised (ai-math:llm-advised-prompt $text $advice))
                          ($messages ((ai-math:llm-message "system" (ai-math:llm-system))
                            (ai-math:llm-message "user" (if (== $state "") $advised
                              (str:join "\n" ($advised "Lean's goal state after introductions and bridging:" $state)))))))
                     (ai-math:proposal-loop $itp $client $target $parser "" $messages 1 $rounds $budget
                       (ai-math:llm-advice-record $advice) $premises)))
                  ($other $other)))))
            ($other (AiLLM:Fault prompt-context))))
         (AiLLM:Fault proof-policy)))
      ($other $other))))

; A draft is advice about proof structure. Sketch steps use a normal Lean
; closing tactic, not textual admissions filled by string replacement.
(= (ai-math:dsp-system)
   "Write a careful informal proof in Megalodon's higher-order set theory. Use only the listed facts, never the theorem itself. Give numbered steps with named facts. For induction state the motive and the available induction principle. Return the informal proof only.")
(= (ai-math:dsp-instruction $definitions)
   (str:join "" ("Formalize the draft as a lean tactic block with explicit intermediate have steps. "
     "For a routine step you may use ai_math_auto [" (str:join ", " (ai-math:lean-names $definitions))
     "]. In term position write `by ai_math_auto [...]`. This closing tactic fails if automation cannot prove the step. "
     "Do not use admissions, new axioms or commands outside the proof. The available premises are inserted as local facts automatically; do not repeat that prefix.")))
(= (ai-math:dsp-prove $context $client $target $premises $definitions $repairs $budget)
   (case $context
     (((AiProver $search $thf $itp $vampire $options)
       (if (and (ai-math:itp-natural $repairs) (ai-math:itp-budget-valid $budget))
         (case (ai-math:itp-prompt-context $itp $target $premises $definitions $budget)
           (((AiITP:PromptContext $name $statement $defs $facts)
             (case (ai-math:llm-proof-prompt $search $itp $target
                     (ai-math:llm-prompt-with (AiITP:PromptContext $name $statement $defs $facts)
                       (ai-math:llm-config $client Options))
                     (ai-math:llm-config $client Options) $budget)
               (((AiLLM:Prompt $text)
                (let* (($advice (ai-math:llm-advice $context $client $target))
                    ($prompt (ai-math:llm-advised-prompt
                      $text $advice)))
               (case (ai-math:llm-chat $client
                       ((ai-math:llm-message "system" (ai-math:dsp-system))
                        (ai-math:llm-message "user" $prompt))
                       (ai-math:option (ai-math:llm-config $client Options) retries 4))
                 (((AiLLM:Reply $draft $receipt)
                   (let* (($parser (ai-math:llm-code-parser))
                          ($prefix (ai-math:prover-haves (ai-math:lean-names $premises)))
                          ($messages ((ai-math:llm-message "system" (ai-math:llm-system))
                            (ai-math:llm-message "user" (str:join "\n" ($prompt "Informal draft:" $draft
                              (ai-math:dsp-instruction $definitions)))))))
                     (case (ai-math:proposal-loop $itp $client $target $parser $prefix $messages 1 (+ $repairs 1) $budget
                             (ai-math:llm-advice-record $advice) $premises)
                       (((AiLLM:Result $n $transcript $outcome)
                         (AiDSP:Result $target (AiDSP:Draft $draft $receipt) $transcript $outcome))
                        ($other $other)))))
                  ($other (AiDSP:Result $target (AiDSP:DraftFailure $other) ()
                    (ai-math:prover-outcome ((AiProver:StageFault llm (ai-math:llm-failure $target $other))) (draft))))))))
                ($other $other))))
            ($other (AiLLM:Fault prompt-context))))
         (AiLLM:Fault proof-policy)))
      ($other $other))))
