!(import! &self "../../phase1/library.metta")
!(import! &self proc)
!(import! &self json)
!(import! &self system)
!(import! &self "../../phase1/itp.metta")

(= (itp-example:context)
   (let $index (new-space)
     (let* (($a (ai-math:put $index "or" (AiITP:Declaration 0 DEF)))
            ($b (ai-math:put $index "orIL" (AiITP:Declaration 1 THM)))
            ($c (ai-math:put $index "later" (AiITP:Declaration 2 THM))))
       (AiITP $index "" "" core))))

; Earlier facts and the exact proved bridge vocabulary are eligible.
!(test (ai-math:itp-name-order (itp-example:context) 1 "Megalodon.or") true)
!(test (ai-math:itp-name-order (itp-example:context) 1 "Megalodon.b_or") true)
!(test (ai-math:itp-name-order (itp-example:context) 1 "Megalodon.orIL") false)
!(test (ai-math:itp-name-order (itp-example:context) 1 "Megalodon.later") false)
!(test (ai-math:itp-name-order (itp-example:context) 1 "Megalodon.b_invented") false)
!(test (ai-math:itp-axiom (itp-example:context) 1 "propext") true)
!(test (ai-math:itp-axiom (itp-example:context) 1 "sorryAx") false)
!(test (ai-math:itp-axiom (itp-example:context) 1 "Lean.ofReduceBool") false)

; These are transport controls, not manufactured proof certificates.
!(test
   (case (ai-math:itp-decode (itp-example:context) "orIL" 1 "check"
      (json-parse "{\"schema\":\"wrong\",\"target\":\"orIL\",\"kind\":\"checked\",\"used\":[],\"axioms\":[]}"))
     (((AiITP:Fault $target $reason $evidence) RejectedTransport) ($other Wrong)))
   RejectedTransport)
!(test
   (case (ai-math:itp-decode (itp-example:context) "orIL" 1 "check"
      (json-parse "{\"schema\":\"ai-math.itp.v1\",\"target\":\"orIL\",\"kind\":\"checked\",\"kind\":\"checked\",\"used\":[],\"axioms\":[]}"))
     (((AiITP:Fault $target $reason $evidence) RejectedDuplicate) ($other Wrong)))
   RejectedDuplicate)

!(test
   (case (ai-math:itp-observation (itp-example:context) "orIL" 1 "check"
      (proc:result (proc:exited 1) proc:normal "{}" "failed"
        (proc:capture 2 2 6 6 proc:eof proc:eof (proc:input 0 0))))
     (((AiITP:Fault $target $reason $evidence) FailedProcess) ($other Wrong)))
   FailedProcess)
!(test
   (case (ai-math:itp-observation (itp-example:context) "orIL" 1 "check"
      (proc:result (proc:exited 0) proc:normal "{}" ""
        (proc:capture 2 8 0 0 proc:eof proc:eof (proc:input 0 0))))
     (((AiITP:Unfinished $target $reason $evidence) IncompleteOutput) ($other Wrong)))
   IncompleteOutput)

; A statement catalogue is ordinary indexed data, with an exact domain.
!(test
   (ai-math:itp-signature
     (ai-math:itp-statements-ready (itp-example:context)
       (JsonArray ((JsonArray ((JsonString "orIL") (JsonString "P -> or P Q")))
                   (JsonArray ((JsonString "later") (JsonString "Q")))))) "orIL")
   "P -> or P Q")
!(test
   (ai-math:itp-signature
     (ai-math:itp-statements-ready (itp-example:context)
       (JsonArray ((JsonArray ((JsonString "later") (JsonString "Q")))
                   (JsonArray ((JsonString "orIL") (JsonString "P -> or P Q")))))) "later")
   "Q")
!(test
   (case (ai-math:itp-statements-ready (itp-example:context)
      (JsonArray ((JsonArray ((JsonString "orIL") (JsonString "P -> or P Q"))))))
     (((AiITP:Fault $target $reason $data) IncompleteDomain) ($other Wrong)))
   IncompleteDomain)

!(test (ai-math:itp-runtime (itp-example:context)) AiITP:Interpreted)
!(test (ai-math:itp-complete-process-text
   (proc:result (proc:exited 0) proc:normal "prefix" ""
     (proc:capture 6 6 0 0 proc:eof proc:eof (proc:input 0 0))))
   (AiITP:ProcessText "prefix"))
!(test (case (ai-math:itp-complete-process-text
   (proc:result (proc:exited 0) proc:normal "partial" ""
     (proc:capture 12 7 0 0 proc:eof proc:eof (proc:input 0 0))))
   (((AiITP:Fault $target $reason $details) $reason) ($other Wrong))) preparation-capture)
!(test (let* (($index (new-space))
              ($stored (ai-math:put $index (AiITPRuntime "/application" "lean")
                (AiITP:Native "/tools with spaces/guard" "/tools with spaces/worker"
                  "/lean prefix" "/compiled library"))))
   (ai-math:itp-command (AiITP $index "/application" "lean" core)))
   ("env" "LEAN_PATH=/compiled library" "LEAN_SYSROOT=/lean prefix"
    "/tools with spaces/guard" "--worker" "/tools with spaces/worker"))
!(test (let* (($index (new-space))
              ($stored (ai-math:put $index (AiITPRuntime "/application" "lean")
                (AiITP:Native "guard" "worker" "prefix" "library"))))
   (ai-math:itp-runtime (AiITP $index "/application" "another-lean" core)))
   AiITP:Interpreted)
