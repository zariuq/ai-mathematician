!(import! &self proc)
!(import! &self "../../phase1/library.metta")
!(import! &self (library list))
!(import! &self json)
!(import! &self system)
!(import! &self "../../phase1/itp.metta")
!(import! &self "../../phase1/prover.metta")
!(import! &self "../../phase1/experiment.metta")
!(import! &self "../../phase1/experiment_workers.metta")

!(test (ai-math:option ((enabled false)) enabled true) false)
!(test (ai-math:option ((enabled false)) missing true) true)
!(test (ai-math:prover-stages-at "." ((lean-stages (base)))) (base))

!(test (ai-math:workers-config-valid
   (json:parse "{\"corpus\":\"corpus.sexpr\",\"output\":\"run\"}")) true)
!(test (ai-math:workers-config-valid
   (json:parse "{\"corpus\":\"corpus.sexpr\",\"output\":\"run\",\"workers\":2,\"mode\":\"Resume\"}")) true)
!(test (ai-math:workers-config-valid
   (json:parse "{\"corpus\":\"corpus.sexpr\",\"output\":\"run\",\"workers\":0}")) false)
!(test (ai-math:workers-config-valid
   (json:parse "{\"corpus\":\"corpus.sexpr\",\"output\":\"run\",\"unknown\":true}")) false)
!(test (ai-math:workers-config-valid
   (json:parse "{\"corpus\":\"corpus.sexpr\",\"output\":\"run\",\"itp_runtime\":\"native\"}")) true)
!(test (ai-math:workers-config-valid
   (json:parse "{\"corpus\":\"corpus.sexpr\",\"output\":\"run\",\"itp_runtime\":\"unrecognised\"}")) false)
!(test (ai-math:workers-partition ((7 "a") (11 "b") (14 "c")) 2 0) ((7 "a") (14 "c")))
!(test (ai-math:workers-partition ((7 "a") (11 "b") (14 "c")) 2 1) ((11 "b")))
!(test (ai-math:workers-partition () 2 0) ())
!(test (ai-math:workers-options
   (json:parse "{\"profile\":\"CettaFull\",\"slices\":[],\"lean_stages\":[\"base\"],\"induction\":false}") "unused")
   ((slices ()) (lean-stages (base)) (induction false)))
!(test (ai-math:workers-dirname "/a path/config.json") "/a path")
!(test (ai-math:workers-trim-directory "/a path///") "/a path")
!(test (ai-math:workers-executable "/a path" "lean") "lean")
!(test (ai-math:workers-executable "/a path" "tools/lean") "/a path/tools/lean")
!(test (ai-math:workers-process-text
   (proc:result (proc:exited 0) proc:normal "ok" ""
     (proc:capture 2 2 0 0 proc:eof proc:eof (proc:input 0 0)))) (AiWorkers:Text "ok"))
!(test (ai-math:workers-process-text
   (proc:result (proc:signaled 9) proc:timed-out "" ""
     (proc:capture 0 0 0 0 proc:eof proc:eof (proc:input 0 0))))
   (AiWorkers:Unfinished deadline (proc:signaled 9)))
!(test (ai-math:workers-exit-code
   (AiWorkers:Summary "key" 1 (("proved" 0) ("not-proved" 1) ("unfinished" 0) ("fault" 0)) "joined.jsonl")) 0)
