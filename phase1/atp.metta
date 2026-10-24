; ATP advice from typed Megalodon declarations. Target: PeTTa 1.0.6.
; Entry points load library.metta, search.metta and the shared libraries.
; THF is constructed as compact TPTP data and printed by lib_tptp.
; Problem-local c_N symbols are injective; the catalogue retains source names.
; Vampire's report is advice, never a checked theorem.
; The prepared catalogue retains statements and definition bodies only.
; Original proofs remain in the source library, not in translation closures.

(= (ai-math:thf-last $entries $default)
   (foldl-atom (sort-atom $entries) $default $out $entry (index-atom $entry 1)))
(= (ai-math:thf-lookup (AiTHF $count $index $reader) $kind $key)
   (ai-math:thf-last
     (collapse (match $index (AiTHF:Entry $kind $key $ordinal $value) ($ordinal $value)))
     AiTHF:Missing))
(= (ai-math:thf-id $ordinal)
   (str:string->symbol (str:concat "c_" (str:number->string $ordinal))))
(= (ai-math:thf-suffix $id $suffix)
   (str:string->symbol (str:concat (str:symbol->string $id) $suffix)))
(= (ai-math:thf-index $index $ordinal
      (Decl $i $kind $name $hash $stmt $body $syms $deps $features))
   (let* (($fact (AiTHF:Fact $i $kind $name $stmt (if (== $kind DEF) $body NoBody)))
          ($binding (AiTHF:Binding (ai-math:thf-id $ordinal) $fact))
          ($named (add-atom $index (AiTHF:Entry Name $name $ordinal $binding)))
          ($numbered (add-atom $index (AiTHF:Entry Ordinal $ordinal $ordinal $fact)))
          ($hashed (add-atom $index (AiTHF:Entry Hash $hash $ordinal $name)))
          ($definition
            (if (== $kind DEF)
              (let $definition-id (ai-math:thf-suffix (ai-math:thf-id $ordinal) "_def")
                (add-atom $index (AiTHF:Entry Definition $definition-id $ordinal $name))) ())))
     (+ $ordinal 1)))
(= (ai-math:thf-from-primitives $decls $primitives)
   (ai-math:thf-from-primitives $decls $primitives
     (AiTHF:Formats (tptp:open-reader strict) (tptp:open-record-printer))))
(= (ai-math:thf-from-primitives $decls $primitives $formats)
   (let* (($index (new-space))
          ($names (foldl-atom $decls 0 $ordinal $decl
                    (ai-math:thf-index $index $ordinal $decl)))
          ($prims (foldl-atom $primitives 0 $ordinal $entry
                    (let ($id $name) $entry
                      (let $stored (add-atom $index (AiTHF:Entry Primitive $id $ordinal $name))
                        (+ $ordinal 1))))))
     (AiTHF (size-atom $decls) $index $formats)))
(= (ai-math:thf $decls $corpus-path)
   (ai-math:thf $decls $corpus-path
     (AiTHF:Formats (tptp:open-reader strict) (tptp:open-record-printer))))
(= (ai-math:thf $decls $corpus-path $formats)
   (case (fs:read-lines $corpus-path)
     (((Error $reason $where) (Error $reason $where))
      ($lines
       (ai-math:thf-from-primitives $decls
         (foldl-atom $lines () $out $line
           (case (ai-math:read-line $line)
             (((AiForm $form)
               (case (ai-math:without-source-line $form)
                 (((PRIM $id $name $hash $ty) (union-atom $out (($id $name))))
                  ($other $out))))
              ($other $out)))) $formats)))))

; Translation results carry their dependencies explicitly. A valid source
; term without a realization remains an interpretation request with its input.
(= (ai-math:thf-values $results)
   (foldl-atom $results (AiTHF:Value (list:from-expression ()) ()) $state $result
     (case $state
       (((AiTHF:Value $nodes $used)
         (case $result
           (((AiTHF:Value $node $uses)
             (AiTHF:Value (list:push $nodes $node) (unique-atom (union-atom $used $uses))))
            ($request $request))))
        ($request $request)))))
(= (ai-math:thf-node $operator $results)
   (case (ai-math:thf-values $results)
     (((AiTHF:Value $nodes $used)
       (AiTHF:Value (ai-math:thf-expression $operator $nodes) $used))
      ($request $request))))
; Compact TPTP terms are finite expressions. Construct that carrier through
; the shared list API, rather than export PeTTa's internal open-cons spine.
(= (ai-math:thf-expression $operator $arguments)
   (list:to-expression (cons-atom $operator $arguments)))
(= (ai-math:thf-type $node $variables)
   (case $node
     (((SET) (AiTHF:Value set ()))
      ((PROP) (AiTHF:Value §o ()))
      ((AR $left $right)
       (ai-math:thf-node ⇒ ((ai-math:thf-type $left $variables)
                           (ai-math:thf-type $right $variables))))
      ((TPVAR $index)
       (if (and (>= $index 0) (< $index (size-atom $variables)))
         (AiTHF:Value (index-atom $variables (- (- (size-atom $variables) $index) 1)) ())
         (AiTHF:InterpretationRequest free-type-variable $node)))
      ($other (AiTHF:InterpretationRequest type $other)))))
(= (ai-math:thf-binder $operator $variable $type $body)
   (case (ai-math:thf-values ($type $body))
     (((AiTHF:Value $parts $used)
       (let* (($ty (index-atom $parts 0)) ($term (index-atom $parts 1)))
         (AiTHF:Value ($operator ((: $variable $ty)) $term) $used)))
      ($request $request))))
(= (ai-math:thf-term $context $node $env $tvars)
   (case $node
     (((DB $index)
       (if (and (>= $index 0) (< $index (size-atom $env)))
         (AiTHF:Value (index-atom $env (- (- (size-atom $env) $index) 1)) ())
         (AiTHF:InterpretationRequest free-term-variable $node)))
      ((LAM $type $body)
       (let $variable (str:string->symbol (str:concat "X" (str:number->string (size-atom $env))))
         (ai-math:thf-binder λ $variable (ai-math:thf-type $type $tvars)
           (ai-math:thf-term $context $body (union-atom $env ($variable)) $tvars))))
      ((ALL $type $body)
       (let $variable (str:string->symbol (str:concat "X" (str:number->string (size-atom $env))))
         (ai-math:thf-binder ∀ $variable (ai-math:thf-type $type $tvars)
           (ai-math:thf-term $context $body (union-atom $env ($variable)) $tvars))))
      ((IMP $left $right)
       (ai-math:thf-node → ((ai-math:thf-term $context $left $env $tvars)
                           (ai-math:thf-term $context $right $env $tvars))))
      ((AP $fn $arg) (ai-math:thf-application $context $node $env $tvars))
      ((TMH $hash) (ai-math:thf-head $context $node $env $tvars))
      ((PRIM $index) (ai-math:thf-head $context $node $env $tvars))
      ((TPAP $fn $type) (ai-math:thf-head $context $node $env $tvars))
      ($other (AiTHF:InterpretationRequest term $other)))))
(= (ai-math:thf-instantiation $node $types)
   (case $node
     (((TPAP $fn $ty) (ai-math:thf-instantiation $fn (cons-atom $ty $types)))
      ($other (AiTHF:Instantiation $other $types)))))
(= (ai-math:thf-constant-name $context $node)
   (case $node
     (((TMH $hash) (ai-math:thf-lookup $context Hash $hash))
      ((PRIM $index) (ai-math:thf-lookup $context Primitive $index))
      ($other AiTHF:Missing))))
(= (ai-math:thf-binary $name)
   (case $name (("and" ∧) ("or" ∨) ("iff" ↔) ($other AiTHF:Missing))))
(= (ai-math:thf-head $context $node $env $tvars)
   (let (AiTHF:Instantiation $head $source-types) (ai-math:thf-instantiation $node ())
     (case (ai-math:thf-values (map-atom $source-types $ty (ai-math:thf-type $ty $tvars)))
       (((AiTHF:Value $types $used)
         (let $name (ai-math:thf-constant-name $context $head)
           (case $name
             (("True" (AiTHF:Value §true ()))
              ("False" (AiTHF:Value §false ()))
              ("not" (AiTHF:Value (λ ((: A §o)) (¬ A)) ()))
              ("and" (AiTHF:Value (λ ((: A §o) (: B §o)) (∧ A B)) ()))
              ("or" (AiTHF:Value (λ ((: A §o) (: B §o)) (∨ A B)) ()))
              ("iff" (AiTHF:Value (λ ((: A §o) (: B §o)) (↔ A B)) ()))
              ($other (ai-math:thf-typed-head $context $node $name $types))))))
        ($request $request)))))
(= (ai-math:thf-typed-head $context $node $name $types)
   (if (and (ai-math:contains ("eq" "neq" "ex") $name) (== (size-atom $types) 1))
     (let $ty (car-atom $types)
       (case $name
         (("eq" (AiTHF:Value (λ ((: A $ty) (: B $ty)) (≈ A B)) ()))
          ("neq" (AiTHF:Value (λ ((: A $ty) (: B $ty)) (≉ A B)) ()))
          ("ex" (AiTHF:Value (λ ((: P (⇒ $ty §o))) (∃ ((: Z $ty)) (P Z))) ())))))
     (if (> (size-atom $types) 0)
       (AiTHF:InterpretationRequest polymorphic-constant $node)
       (case (ai-math:thf-lookup $context Name $name)
         (((AiTHF:Binding $id $decl) (AiTHF:Value $id ($name)))
          ($missing (AiTHF:InterpretationRequest unresolved-constant $node)))))))
(= (ai-math:thf-application $context $node $env $tvars)
   (let (AiApplication $head $args) (ai-math:application $node ())
     (let (AiTHF:Instantiation $base $types) (ai-math:thf-instantiation $head ())
       (case (ai-math:thf-values
               (map-atom $args $arg (ai-math:thf-term $context $arg $env $tvars)))
         (((AiTHF:Value $terms $used)
           (ai-math:thf-applied $context $head $env $tvars
             (ai-math:thf-constant-name $context $base) $types $terms $used))
          ($request $request))))))
(= (ai-math:thf-applied $context $head $env $tvars $name $types $terms $used)
   (if (and (== $name "not") (== (size-atom $terms) 1))
     (AiTHF:Value (¬ (car-atom $terms)) $used)
     (if (and (ai-math:contains ("and" "or" "iff") $name) (== (size-atom $terms) 2))
       (AiTHF:Value (ai-math:thf-expression (ai-math:thf-binary $name) $terms) $used)
       (if (and (ai-math:contains ("eq" "neq") $name)
                (and (== (size-atom $terms) 2) (== (size-atom $types) 1)))
         (AiTHF:Value (ai-math:thf-expression (if (== $name "eq") ≈ ≉) $terms) $used)
         (if (and (== $name "ex")
                  (and (== (size-atom $terms) 1) (== (size-atom $types) 1)))
           (let $variable (str:string->symbol (str:concat "Z" (str:number->string (size-atom $env))))
             (ai-math:thf-binder ∃ $variable (ai-math:thf-type (car-atom $types) $tvars)
               (AiTHF:Value ((car-atom $terms) $variable) $used)))
           (case (ai-math:thf-term $context $head $env $tvars)
             (((AiTHF:Value $function $uses)
               (AiTHF:Value (ai-math:thf-expression $function $terms)
                 (unique-atom (union-atom $used $uses))))
              ($request $request))))))))

(= (ai-math:thf-premise $context
      (AiTHF:Premises $records $ids $skipped $used) $name)
   (case (ai-math:thf-lookup $context Name $name)
     (((AiTHF:Binding $id (AiTHF:Fact $i $kind $n $stmt $body))
       (if (ai-math:contains (AXIOM THM) $kind)
         (case (ai-math:thf-term $context $stmt () ())
           (((AiTHF:Value $term $uses)
             (AiTHF:Premises (union-atom $records ((thf $id axiom $term)))
               (union-atom $ids ((AiTHF:Premise $id $name))) $skipped
               (unique-atom (union-atom $used $uses))))
            ($request (AiTHF:Premises $records $ids
              (union-atom $skipped ((AiTHF:Skipped $name $request))) $used))))
         (AiTHF:Premises $records $ids $skipped $used)))
      ($missing (AiTHF:Premises $records $ids $skipped $used)))))
(= (ai-math:thf-definition $context (AiTHF:Definitions $records $skipped $used $next) $name)
   (case (ai-math:thf-lookup $context Name $name)
     (((AiTHF:Binding $id (AiTHF:Fact $i DEF $n $ty $body))
       (case (ai-math:thf-term $context $body () ())
         (((AiTHF:Value $term $uses)
           (AiTHF:Definitions
             (union-atom $records ((thf (ai-math:thf-suffix $id "_def") definition (≈ $id $term))))
             $skipped (unique-atom (union-atom $used $uses)) (union-atom $next $uses)))
          ($request (AiTHF:Definitions $records
             (union-atom $skipped ((AiTHF:Skipped $name $request))) $used $next)))))
      ($other (AiTHF:Definitions $records $skipped $used $next)))))
(= (ai-math:thf-definitions $context $frontier $seen $depth $limit $records $skipped $used)
   (if (== $frontier ()) (AiTHF:DefinitionClosure $records $skipped $used ())
     (if (if (== $limit All) false (> $depth $limit))
       (AiTHF:DefinitionClosure $records $skipped $used $frontier)
       (let (AiTHF:Definitions $new-records $new-skipped $new-used $next)
         (foldl-atom (sort-atom $frontier) (AiTHF:Definitions $records $skipped $used ())
           $state $name (ai-math:thf-definition $context $state $name))
         (let $visited (unique-atom (union-atom $seen $frontier))
           (ai-math:thf-definitions $context
             (subtraction-atom (unique-atom $next) $visited) $visited (+ $depth 1) $limit
             $new-records $new-skipped $new-used))))))
(= (ai-math:thf-type-declaration $context (AiTHF:Types $records $skipped) $name)
   (case (ai-math:thf-lookup $context Name $name)
     (((AiTHF:Binding $id (AiTHF:Fact $i $kind $n $ty $body))
       (if (ai-math:contains (PARAM PRIM DEF) $kind)
         (case (ai-math:thf-type $ty ())
           (((AiTHF:Value $type $unused)
             (AiTHF:Types (union-atom $records
               ((thf (ai-math:thf-suffix $id "_type") type (: $id $type)))) $skipped))
            ($request (AiTHF:Types $records
              (union-atom $skipped ((AiTHF:Skipped $name $request)))))))
         (AiTHF:Types $records $skipped)))
      ($other (AiTHF:Types $records $skipped)))))
(= (ai-math:thf-problem $context $goal-index $premises)
   (ai-math:thf-problem $context $goal-index $premises All))
(= (ai-math:thf-problem (AiTHF $count $index $reader) $goal-index $premises $definition-depth)
   (let $context (AiTHF $count $index $reader)
     (if (or (< $goal-index 0) (>= $goal-index $count))
       (AiTHF:InterpretationRequest goal-index $goal-index)
       (case (ai-math:thf-lookup $context Ordinal $goal-index)
         (((AiTHF:Fact $i THM $name $stmt $body)
           (ai-math:thf-statement-problem $context $stmt $premises $definition-depth))
          ($other (AiTHF:InterpretationRequest non-theorem-goal $other)))))))

; Arbitrary closed case statements use the same exporter and prepared
; catalogue. They do not need temporary declarations or copied contexts.
(= (ai-math:thf-statement-problem $context $statement $premises $definition-depth)
           (case (ai-math:thf-term $context $statement () ())
             (((AiTHF:Value $goal $goal-uses)
               (let* (($premise-state (foldl-atom $premises
                          (AiTHF:Premises () () () $goal-uses) $state $premise
                          (ai-math:thf-premise $context $state $premise)))
                      ((AiTHF:Premises $axioms $ids $omitted $used) $premise-state)
                      ((AiTHF:DefinitionClosure $definitions $skipped $all-used $unexpanded)
                        (ai-math:thf-definitions $context (unique-atom $used) () 0
                          $definition-depth () $omitted $used))
                      ((AiTHF:Types $types $all-skipped)
                        (foldl-atom (sort-atom $all-used)
                          (AiTHF:Types ((thf set_type type (: set §tType))) $skipped)
                          $state $constant (ai-math:thf-type-declaration $context $state $constant))))
                 (AiTHF:Problem
                   (list:from-expression
                     (union-atom $types (union-atom $definitions
                       (union-atom $axioms ((thf goal conjecture $goal))))))
                   $ids $all-skipped $unexpanded)))
              ($request $request))))
(= (ai-math:thf-text (AiTHF $count $index (AiTHF:Formats $reader $printer))
      (AiTHF:Problem $records $ids $skipped $unexpanded))
   (tptp:print-records-with $printer $records))

; One prepared reader per corpus context; neither printing nor proof parsing
; prepares the TPTP language for each attempt. Ordinary process observations
; retain stdout/stderr, termination, deadlines and capture completeness.
; Seconds is Vampire's own budget; the process watchdog adds fifteen seconds.
; Zero leaves both unbounded. The watchdog cannot preempt host process creation.
(= (ai-math:vampire $context $problem $executable $seconds)
   (case $problem
     (((AiTHF:Problem $records $ids $skipped $unexpanded)
       (let $text (ai-math:thf-text $context $problem)
         (case $text
           (((Error $reason $where) (Error $reason $where))
            ($input
             (ai-math:vampire-observation $context $problem
               (proc:run ($executable "--mode" "portfolio" "--input_syntax" "tptp"
                          "--proof" "tptp"
                          "-t" (str:number->string $seconds))
                 ((lifetime owner) (stdin $input) (timeout-ms (if (== $seconds 0) 0 (+ (* $seconds 1000) 15000)))))))))))
      ($request $request))))
(= (ai-math:vampire-observation $context $problem $observation)
   (case $observation
     (((proc:result $termination $completion $stdout $stderr $capture)
       (ai-math:vampire-report $context $problem $termination $completion $stdout $stderr $capture))
      ($other (AiATP:ProcessObservation $other)))))
(= (ai-math:vampire-report (AiTHF $count $index (AiTHF:Formats $reader $printer)) $problem
      $termination $completion $stdout $stderr $capture)
   (let* (($envelope (tptp:szs-output $stdout))
          ($payloads (map-atom (tptp:szs-data $envelope) $block
                       (let (TPTP:SZSData $kind $body $start $end) $block
                         (if (ai-math:contains ("Proof" "CNFRefutation" "Refutation") $kind)
                           (ai-math:vampire-read-advice-payload $index $reader $body) ()))))
          ($references (foldl-atom $payloads () $out $records
                         (union-atom $out (ai-math:vampire-payload-references $records))))
          ($names (ai-math:vampire-premises $problem $references))
          ($definitions (ai-math:vampire-definitions
                          (AiTHF $count $index (AiTHF:Formats $reader $printer)) $references)))
     (AiATP:Report (tptp:szs-status $envelope) $names $definitions $references
       (proc:result $termination $completion $stdout $stderr $capture) $envelope $payloads)))
(= (ai-math:vampire-premises (AiTHF:Problem $records $ids $skipped $unexpanded) $references)
   (unique-atom
     (foldl-atom $references () $out $reference
       (let $source-name (ai-math:vampire-reference-name $reference)
         (foldl-atom $ids $out $names $entry
           (let (AiTHF:Premise $id $name) $entry
             (if (== $id (ai-math:vampire-record-id $source-name))
               (union-atom $names ($name)) $names)))))))
; Quoting a TPTP input name does not change its identity. Keep the raw
; annotation in the report, but compare its spelling against our generated IDs.
(= (ai-math:vampire-record-id $name)
   (if (== (get-type $name) String) (str:string->symbol $name) $name))
(= (ai-math:vampire-definitions $context $references)
   (unique-atom
     (foldl-atom $references () $out $reference
       (let $source-name (ai-math:vampire-reference-name $reference)
         (case (ai-math:thf-lookup $context Definition (ai-math:vampire-record-id $source-name))
           ((AiTHF:Missing $out) ($name (union-atom $out ($name)))))))))

; A compact scripting view is offered only for an intact, finished process
; observation and complete payloads. Lexical producer hints remain explicitly
; distinct from parsed proof records in the retained report.
(= (ai-math:atp-summary $report)
   (case $report
     (((AiATP:Report $status $names $definitions $refs $observation $envelope $payloads)
       (case ($observation $envelope)
         ((((proc:result (proc:exited $exit) proc:normal $stdout $stderr
              (proc:capture $out-seen $out-kept $err-seen $err-kept proc:eof proc:eof
                (proc:input $input-size $input-sent)))
            (TPTP:SZSEnvelope $statuses $blocks TPTP:SZSComplete ()))
           ; Vampire's normal unsuccessful return is 1. It does not license
           ; proof advice, missing status, abnormal termination or partial I/O.
           (let $compatible (case ($exit $status)
                  (((0 $reported) true)
                   ((1 (TPTP:SZSReported $word))
                    (ai-math:contains ("Timeout" "ResourceOut" "MemoryOut" "GaveUp") $word))
                   ($other false)))
             (if $compatible
               (if (and (== $out-seen $out-kept)
                        (and (== $err-seen $err-kept) (== $input-size $input-sent)))
                 (if (foldl-atom $payloads true $ok $payload
                       (and $ok (if (== $payload ()) true
                         (ai-math:vampire-payload-advice-ready $payload))))
                   (case $status
                     (((TPTP:SZSReported $word) (AiATP:Advice $word $names $definitions))
                      ($other (AiATP:UnresolvedStatus $other))))
                   (AiATP:PayloadInterpretationNeeded $payloads))
                 (AiATP:IncompleteCapture $status))
               (AiATP:UnfinishedOrFaulted $status $observation $envelope))))
          ($other (AiATP:UnfinishedOrFaulted $status $observation $envelope)))))
      ($other $other))))

(= (ai-math:atp-goal $context $search $goal-name $executable $seconds $limit)
   (case (ai-math:thf-lookup $context Name $goal-name)
     (((AiTHF:Binding $id (AiTHF:Fact $i THM $n $stmt $body))
       (let $problem (ai-math:thf-problem $context $i
                        (ai-math:entry-names (ai-math:rank $search $i $limit)))
         (case $problem
           (((AiTHF:Problem $records $ids $skipped $unexpanded)
             (AiATP:Attempt $goal-name
               (ai-math:atp-summary (ai-math:vampire $context $problem $executable $seconds))
               $skipped $unexpanded))
            ($request $request)))))
      ($other (AiTHF:InterpretationRequest theorem-name $goal-name)))))
