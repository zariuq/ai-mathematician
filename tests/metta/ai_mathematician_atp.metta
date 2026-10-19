!(import! &self proc)
!(import! &self "../../phase1/library.metta")
!(import! &self (library list))
!(import! &self (library lib_tptp))
!(import! &self re)
!(import! &self "../../phase1/vampire_output.metta")
!(import! &self "../../phase1/search.metta")
!(import! &self "../../phase1/atp.metta")

(= (atp-test:context)
   (ai-math:thf-from-primitives
     (ai-math:load-library "tests/fixtures/ai_mathematician_atp.sexpr") ((7 "member"))))
(= (atp-test:summary $stdout $capture)
   (let* (($context (atp-test:context))
          ($problem (ai-math:thf-problem $context 6 ("p_fact"))))
     (ai-math:atp-summary (ai-math:vampire-observation $context $problem
       (proc:result (proc:exited 0) proc:normal $stdout "" $capture)))))
(= (atp-test:complete $stdout)
   (let $size (str:byte-length $stdout)
     (atp-test:summary $stdout
       (proc:capture $size $size 0 0 proc:eof proc:eof (proc:input 0 0)))))

; Types and bound variables remain structured data.
!(test (ai-math:thf-type (AR (SET) (PROP)) ()) (quote (AiTHF:Value (⇒ set §o) ())))
!(test (ai-math:thf-term (atp-test:context) (ALL (SET) (DB 0)) () ())
       (AiTHF:Value (∀ ((: X0 set)) X0) ()))
!(test (ai-math:thf-term (atp-test:context) (DB 0) () ())
       (AiTHF:InterpretationRequest free-term-variable (DB 0)))
!(test (ai-math:thf-type (TPVAR 0) ())
       (AiTHF:InterpretationRequest free-type-variable (TPVAR 0)))
!(test (ai-math:thf-term (atp-test:context) (TMH "unknown") () ())
       (AiTHF:InterpretationRequest unresolved-constant (TMH "unknown")))

; A partial logical constant is a typed lambda, not an untyped name.
!(test (ai-math:thf-term (atp-test:context) (TPAP (TMH "heq") (SET)) () ())
       (AiTHF:Value (λ ((: A set) (: B set)) (≈ A B)) ()))
; Names that collide under Python's spelling rule remain different symbols.
!(test
   (let $context (atp-test:context)
     (== (ai-math:thf-lookup $context Name "odd'")
         (ai-math:thf-lookup $context Name "odd_39_")))
   false)

; The prepared authored printer supplies parentheses needed by Vampire.
!(test
   (let* (($context (atp-test:context)) ($problem (ai-math:thf-problem $context 8 ())))
     (ai-math:thf-text $context $problem))
   "thf(set_type,type,set:$tType).\nthf(goal,conjecture,![X0:set]:(X0=X0)).\n")
!(test
   (let* (($context (atp-test:context))
          ($problem (ai-math:thf-problem $context 6 ("p_fact" "p_implies_q"))))
     (let (AiTHF:Problem $records $ids $skipped $unexpanded) $problem
       ($ids $skipped $unexpanded)))
   (((AiTHF:Premise c_4 "p_fact") (AiTHF:Premise c_5 "p_implies_q")) () ()))

; SZS metadata is independent of the logical payload's formula family.
!(test (tptp:szs-status (tptp:szs-output "% SZS status Theorem for x\n"))
       (TPTP:SZSReported "Theorem"))
!(test (tptp:szs-status (tptp:szs-output "noise\n% SZS status GaveUp for x\n"))
       (TPTP:SZSReported "GaveUp"))
!(test (tptp:szs-status (tptp:szs-output "% SZS status VendorFutureStatus for x\n"))
       (TPTP:SZSReported "VendorFutureStatus"))
!(test (tptp:szs-status (tptp:szs-output "\"SZS status Theorem\"\n"))
       TPTP:SZSUnreported)
!(test
   (tptp:szs-status
     (tptp:szs-output "% SZS status Theorem for x\n% SZS status CounterSatisfiable for x\n"))
   (TPTP:SZSConflictingStatuses ("Theorem" "CounterSatisfiable")))
!(test
   (tptp:szs-pending (tptp:szs-output "% SZS output start Proof for x\nfof(a,axiom,p)."))
   (TPTP:SZSUnfinished "Proof" "fof(a,axiom,p)." 0))
!(test
   (tptp:szs-data
     (tptp:szs-output "% SZS output start Proof for x\nfof(a,axiom,p).\n% SZS output end Proof for x"))
   ((TPTP:SZSData "Proof" "fof(a,axiom,p)." 0 2)))

; Only actual parsed source annotations supply premise references.
!(test
   (tptp:input-references
     (tptp:read-text "fof(a,axiom,p,file('input.p',c_4)). fof(b,plain,p,inference(copy,[],[a]))."))
   ((TPTP:InputReference a "input.p" c_4)))
!(test
   (tptp:input-references (tptp:read-text "fof(a,axiom,'file(input,c_4)')."))
   ())

; Higher-order application retains its function and lexical binder scope.
!(test
   (let $printer (tptp:open-record-printer)
     (let $text (tptp:print-records-with $printer
           (list:from-expression ((thf g conjecture ((λ ((: X §o)) X) §true)))))
       (== (tptp:read-text $text)
           (tptp:read-text "thf(g,conjecture,((^[X:$o]:X) @ $true))."))))
   true)
!(test
   (let $printer (tptp:open-record-printer)
     (let $text (tptp:print-records-with $printer
           (list:from-expression ((thf g conjecture (∃ ((: Z §o)) ((λ ((: X §o)) X) Z))))))
       (== (tptp:read-text $text)
           (tptp:read-text "thf(g,conjecture,?[Z:$o]:((^[X:$o]:X) @ Z))."))))
   true)
; Negative: explicit list values remain data, not function applications.
!(test
   (let $printer (tptp:open-record-printer)
     (let $text (tptp:print-records-with $printer
           (tptp:read-text "fof(g,axiom,p,inference(copy,[status(thm)],[a,b]))."))
       (== (tptp:read-text $text)
           (tptp:read-text "fof(g,axiom,p,inference(copy,[status(thm)],[a,b]))."))))
   true)
; THF's extra grouping must not leak into CNF's narrower literal grammar.
!(test
   (let $printer (tptp:open-record-printer)
     (let $records (tptp:read-text "cnf(a,axiom,p|~q).")
       (== $records (tptp:read-text (tptp:print-records-with $printer $records)))))
   true)
!(test
   (let $printer (tptp:open-record-printer)
     (let $text (tptp:print-records-with $printer
           (list:from-expression ((thf g conjecture (¬ (≉ (f x) x))))))
       (== (tptp:read-text $text)
           (tptp:read-text "thf(g,conjecture,~((f @ x)!=x))."))))
   true)

; A provisional report cannot become completed advice after a deadline.
!(test
   (let* (($context (atp-test:context)) ($problem (ai-math:thf-problem $context 6 ("p_fact")))
          ($report (ai-math:vampire-observation $context $problem
            (proc:result (proc:exited 0) proc:timed-out "% SZS status Theorem for x\n" ""
              (proc:capture 27 27 0 0 proc:eof proc:eof (proc:input 0 0))))))
     (case (ai-math:atp-summary $report)
       (((AiATP:UnfinishedOrFaulted $status $observation $envelope) Incomplete)
        ($other IncorrectlyCompleted))))
   Incomplete)

; Repeated agreement is harmless; incomplete protocol or payloads stay visible.
!(test
   (tptp:szs-status (tptp:szs-output
     "% SZS status Theorem for x\n% SZS status Theorem for x\n"))
   (TPTP:SZSReported "Theorem"))
!(test
   (tptp:szs-pending (tptp:szs-output
     "% SZS output start Proof for x\n% SZS output end Model for x"))
   (TPTP:SZSUnfinished "Proof" "" 0))
!(test
   (let (TPTP:SZSEnvelope $statuses $blocks $pending $issues)
     (tptp:szs-output "% SZS output start Proof for x\n% SZS output start Model for x\n% SZS output end Proof for x")
     (size-atom $issues))
   1)
!(test
   (case (atp-test:complete
     "% SZS status Theorem for x\n% SZS output start Proof for x\nnot-a-tptp-record\n% SZS output end Proof for x")
     (((AiATP:PayloadInterpretationNeeded $payloads) Uninterpreted)
      ($other IncorrectlyCompleted)))
   Uninterpreted)
!(test
   (atp-test:complete
     "% SZS status Theorem for x\n% SZS output start Proof for x\nthf(a,plain,p,file('input',c_11_def)).\n% SZS output end Proof for x")
   (AiATP:Advice "Theorem" () ("alias")))
!(test
   (atp-test:complete
     "% SZS status Theorem for x\n% SZS output start Proof for x\nthf(a,axiom,p,file('input','c_4')).\nthf(b,plain,p,file('input','c_11_def')).\n% SZS output end Proof for x")
   (AiATP:Advice "Theorem" ("p_fact") ("alias")))
!(test
   (atp-test:complete "diagnostic only\n")
   (AiATP:UnresolvedStatus TPTP:SZSUnreported))
!(test
   (let $text "% SZS status Theorem for x\n"
     (atp-test:summary $text
       (proc:capture (+ (str:byte-length $text) 1) (str:byte-length $text)
         0 0 proc:eof proc:eof (proc:input 0 0))))
   (AiATP:IncompleteCapture (TPTP:SZSReported "Theorem")))
!(test
   (let $text "% SZS status Theorem for x\n"
     (atp-test:summary $text
       (proc:capture (str:byte-length $text) (str:byte-length $text)
         0 0 proc:eof proc:eof (proc:input 10 5))))
   (AiATP:IncompleteCapture (TPTP:SZSReported "Theorem")))
!(test
   (ai-math:thf-term (atp-test:context) (PRIM 7) () ())
   (AiTHF:Value c_3 ("member")))
!(test
   (ai-math:thf-problem (atp-test:context) 13 ())
   (AiTHF:InterpretationRequest unresolved-constant (TMH "unknown")))

; The translation view excludes proofs and search features, but not the
; statements or definition bodies that determine the generated problem.
!(test
   (ai-math:thf-lookup (atp-test:context) Name "q_goal")
   (AiTHF:Binding c_6 (AiTHF:Fact 6 THM "q_goal" (TMH "hq") NoBody)))
!(test
   (ai-math:thf-lookup (atp-test:context) Name "alias")
   (AiTHF:Binding c_11 (AiTHF:Fact 11 DEF "alias" (PROP) (TMH "hp"))))
!(test
   (case (ai-math:thf-problem (atp-test:context) 99 ())
     (((AiTHF:InterpretationRequest goal-index 99) OutOfRange)
      ($other IncorrectlyTranslated)))
   OutOfRange)
