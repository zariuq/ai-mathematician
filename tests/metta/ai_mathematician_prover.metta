!(import! &self proc)
!(import! &self "../../phase1/library.metta")
!(import! &self (library list))
!(import! &self (library lib_tptp))
!(import! &self re)
!(import! &self "../../phase1/vampire_output.metta")
!(import! &self "../../phase1/search.metta")
!(import! &self "../../phase1/atp.metta")
!(import! &self json)
!(import! &self system)
!(import! &self "../../phase1/itp.metta")
!(import! &self "../../phase1/proof_strategy.metta")
!(import! &self "../../phase1/induction.metta")
!(import! &self "../../phase1/induction_prover.metta")
!(import! &self "../../phase1/prover.metta")

!(test (ai-math:prover-bridge-attempts "g"
   ((AiProver:Slice 16 (AiATP:Advice "Theorem" ("p") ()) () ()))) ())
!(test (ai-math:prover-outcome (ai-math:prover-bridge-attempts "g"
   ((AiProver:Slice 16 (AiATP:Advice "Timeout" () ()) () ()))) (atp))
   (AiProver:Unfinished ((AiProver:StageFault atp (AiITP:Unfinished "g" vampire-resource (16 "Timeout"))))))
!(test (ai-math:prover-outcome (ai-math:prover-bridge-attempts "g"
   ((AiProver:Slice 16 (Error printer "failed") () ()))) (atp))
   (AiProver:Faulted ((AiProver:StageFault atp (AiITP:Fault "g" thf-print (16 printer "failed"))))))

(= (prover-example:context) (AiITP (new-space) "" "" core))
(= (prover-example:transport $value)
   (case $value
     (((AiITP:Fault $t $r $e) BadTransport)
      ((AiITP:Batch $target $rows) (Batch $target (size-atom $rows)))
      ($other $other))))
(= (prover-example:batch $rows)
   (ai-math:itp-batch-ready (prover-example:context) "goal" 7
     ((AiITP:Candidate "same" "exact proposal")) (json:parse $rows)))

!(test (ai-math:itp-budget-valid (AiITP:Budget 0 0 0)) true)
!(test (ai-math:itp-budget-valid (AiITP:Budget 30000 200000 8000)) true)
!(test (ai-math:itp-budget-valid (AiITP:Budget -1 0 0)) false)
!(test (ai-math:itp-budget-valid (AiITP:Budget 0 1.5 0)) false)
!(test (ai-math:itp-budget-valid (AiITP:Budget "0" 0 0)) false)
!(test (ai-math:itp-candidates-valid ()) true)
!(test (ai-math:itp-candidates-valid ((AiITP:Candidate "same" "one") (AiITP:Candidate "same" "two"))) true)
!(test (ai-math:itp-candidates-valid ((AiITP:Candidate "x" unquoted))) false)
!(test (ai-math:itp-candidates-valid not-a-sequence) false)
!(test (ai-math:prover-options-valid ()) true)
!(test (ai-math:prover-options-valid
   ((slices ()) (vampire-seconds 0) (lean-stages (base apply))
    (base (AiProver:LeanPolicy (AiITP:Budget 0 0 0) (AiITP:Budget 0 0 0) 0)))) true)
!(test (ai-math:prover-options-valid ((slices (8 -1)))) false)
!(test (ai-math:prover-options-valid ((lean-stages (base unknown)))) false)
!(test (ai-math:prover-options-valid ((base (AiProver:LeanPolicy (AiITP:Budget 0 0 0) bad-budget 0)))) false)
!(test (ai-math:prover-options-valid ((unknown-option 1))) false)
!(test (ai-math:prover-options-valid ((definition-depth All))) true)
!(test (ai-math:prover-options-valid ((definition-depth 3))) true)
!(test (ai-math:prover-options-valid ((definition-depth -1))) false)
!(test (ai-math:prover-options-valid ((definition-depth 1.5))) false)
!(test (ai-math:option (ai-math:prover-profile-options PythonV4) definition-depth All) 3)
!(test (ai-math:option (ai-math:prover-profile-options CettaFull) definition-depth All) All)
!(test (ai-math:option (ai-math:prover-profile-options PythonV4) slices ()) (16 32 64 128 256 512))
!(test (ai-math:option (ai-math:prover-profile-options PythonV4) induction-slices ()) (16 32 64))
!(test (ai-math:option (ai-math:prover-profile-options PythonV4) vampire-seconds 0) 30)
!(test (ai-math:option (ai-math:prover-profile-options PythonV4) induction-seconds 0) 5)
!(test (ai-math:prover-options-valid (ai-math:prover-profile-options PythonV4)) true)
!(test (ai-math:prover-profile-options UnknownProfile) (AiProver:InvalidProfile UnknownProfile))
!(test
   (ai-math:prover-advice
     (AiATP:ArchivedAdvice (AiATP:Advice "Theorem" ("a") ("d"))
       (AiATP:TraceRef "ai-math.tstp.v1" "g" 8
         (AiATP:TraceObject Problem "p" 1) (AiATP:TraceObject Solver "s" 2) "r")))
   (AiATP:Advice "Theorem" ("a") ("d")))
!(test
   (ai-math:prover-advice
     (AiATP:TraceFailure (AiATP:Advice "Theorem" ("a") ()) (AiATP:WriteFailure "p" denied)))
   (AiATP:Advice "Theorem" ("a") ()))

; Positive transport controls contain rejected proposals, not proof evidence.
!(test (prover-example:transport (prover-example:batch
   "[{\"index\":0,\"label\":\"same\",\"result\":{\"schema\":\"ai-math.itp.v1\",\"target\":\"goal\",\"kind\":\"rejected\",\"reason\":\"lean-errors\"}}]"))
   (Batch "goal" 1))
!(test (prover-example:transport
   (ai-math:itp-batch-ready (prover-example:context) "goal" 7 () (JsonArray ()))) (Batch "goal" 0))
!(test (prover-example:transport (prover-example:batch "[]")) BadTransport)
!(test (prover-example:transport (prover-example:batch
   "[{\"index\":1,\"label\":\"same\",\"result\":{}}]")) BadTransport)
!(test (prover-example:transport (prover-example:batch
   "[{\"index\":0,\"label\":\"other\",\"result\":{}}]")) BadTransport)
!(test (prover-example:transport (prover-example:batch
   "[{\"index\":0,\"index\":0,\"label\":\"same\",\"result\":{}}]")) BadTransport)
!(test (case (prover-example:batch
   "[{\"index\":0,\"label\":\"same\",\"result\":{\"schema\":\"ai-math.itp.v1\",\"target\":\"another\",\"kind\":\"rejected\"}}]")
     (((AiITP:Batch $target ((AiITP:Attempt $label (AiITP:Fault $t response-identity $e)))) BadIdentity)
      ($other Wrong))) BadIdentity)
!(test (prover-example:transport
   (ai-math:itp-decode (prover-example:context) "goal" 7 "check"
     (json:parse "{\"schema\":\"ai-math.itp.v1\",\"target\":\"goal\",\"kind\":\"batch\",\"attempts\":[]}"))) BadTransport)

!(test
   (ai-math:prover-summarize-hints ("a" "b") ("z")
     ((AiProver:Slice 8 (AiATP:Advice "Theorem" ("a") ("x")) () ())
      (AiProver:Slice 16 (AiATP:Advice "Theorem" ("a") ("y")) () ())
      (AiProver:Slice 32 (AiATP:Advice "Timeout" () ()) () ())))
   (AiProver:Hints (("a") ("a" "b")) ("x" "y" "z") ("z") "Theorem@8,16"
     ((AiProver:Slice 8 (AiATP:Advice "Theorem" ("a") ("x")) () ())
      (AiProver:Slice 16 (AiATP:Advice "Theorem" ("a") ("y")) () ())
      (AiProver:Slice 32 (AiATP:Advice "Timeout" () ()) () ()))))
!(test
   (ai-math:prover-summarize-hints ("b" "a") ()
     ((AiProver:Slice 8 (AiATP:Advice "Timeout" () ()) () ())))
   (AiProver:Hints (("b" "a")) () () "Timeout"
     ((AiProver:Slice 8 (AiATP:Advice "Timeout" () ()) () ()))))
!(test
   (ai-math:prover-winner ((AiProver:Attempt base 0 "solver" "" (AiATP:Advice "Theorem" () ()))) )
   AiProver:NoWinner)
!(test (ai-math:prover-outcome ((AiProver:StageFault base (AiITP:Unfinished "g" deadline ()))) (base))
   (AiProver:Unfinished ((AiProver:StageFault base (AiITP:Unfinished "g" deadline ())))))
!(test (ai-math:prover-outcome ((AiProver:Attempt base 0 "x" "" (AiITP:Unfinished "g" heartbeat ()))) (base))
   (AiProver:Unfinished ((AiProver:Attempt base 0 "x" "" (AiITP:Unfinished "g" heartbeat ())))))
!(test (ai-math:prover-outcome ((AiProver:StageFault base (AiITP:Fault "g" protocol ()))) (base))
   (AiProver:Faulted ((AiProver:StageFault base (AiITP:Fault "g" protocol ())))))
!(test (ai-math:prover-outcome ((AiProver:Attempt base 0 "x" "" (AiITP:Rejected "g" lean-errors ()))) (base))
   (AiProver:NotProved (AiProver:Coverage (base))))
!(test
   (let* (($old (AiProver:StageFault atp (AiITP:Unfinished "g" vampire-resource (16 "Timeout"))))
          ($fault (AiProver:StageFault induction (AiITP:Fault "g" process ())))
          ($later (AiProver:Attempt induction-case 0 "x" "" (AiITP:Unfinished "g" retry-deadline ()))))
     ((ai-math:induction-outcome (AiProver:Unfinished ($old)) ($old $fault))
      (ai-math:induction-outcome (AiProver:Unfinished ($old)) ($old $later))))
   ((AiProver:Faulted ((AiProver:StageFault induction (AiITP:Fault "g" process ()))))
    (AiProver:Unfinished
      ((AiProver:StageFault atp (AiITP:Unfinished "g" vampire-resource (16 "Timeout")))
       (AiProver:Attempt induction-case 0 "x" "" (AiITP:Unfinished "g" retry-deadline ()))))))
!(test (ai-math:induction-outcome (AiProver:NotProved (AiProver:Coverage (base))) ())
   (AiProver:NotProved (AiProver:Coverage (base induction))))
!(test (ai-math:itp-retry-budget (AiITP:Budget 30000 100 80) 5000 1234) (AiITP:Budget 3766 100 80))
!(test (ai-math:itp-retry-budget (AiITP:Budget 30000 100 80) 0 100000) (AiITP:Budget 30000 100 80))
