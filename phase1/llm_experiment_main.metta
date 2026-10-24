; Explicitly enabled proposal runs. Credentials are environment inputs;
; they are never command arguments, configuration fields or log values.
!(import! &self proc)
!(import! &self "library.metta")
!(import! &self (library list))
!(import! &self (library lib_tptp))
!(import! &self re)
!(import! &self "vampire_output.metta")
!(import! &self "search.metta")
!(import! &self "atp.metta")
!(import! &self json)
!(import! &self system)
!(import! &self "itp.metta")
!(import! &self "proof_strategy.metta")
!(import! &self "induction.metta")
!(import! &self "smt_bridge.metta")
!(import! &self "induction_prover.metta")
!(import! &self "prover.metta")
!(import! &self "proof_advice.metta")
!(import! &self "experiment.metta")
!(import! &self io)
!(import! &self "http_transport.metta")
!(import! &self "llm_transport.metta")
!(import! &self "llm.metta")
!(import! &self "llm_experiment.metta")

(= (ai-proposal-main:option $row $key $default)
   (let $value (json:get $row $key)
     (if (== $value JsonNull) $default
       (if (or (== (get-type $value) String)
               (or (== (get-type $value) Number)
                   (or (== $value true) (== $value false))))
         $value AiProposal:InvalidConfig))))
(= (ai-proposal-main:valid $row)
   (and (ai-math:run-unique-object $row)
       (and (foldl-atom ("corpus" "baseline" "output" "model" "ledger") true $ok $key
              (and $ok (== (get-type (ai-proposal-main:option $row $key AiMissing)) String)))
         (and (ai-proposal-main:policy $row)
          (foldl-atom (ai-math:itp-json-keys (json:object-pairs $row)) true $ok $key
           (and $ok (ai-math:contains
             ("corpus" "baseline" "output" "model" "ledger" "call_cap" "rounds" "mode"
              "stride" "limit" "skip" "vampire_only" "resume" "lean" "vampire"
              "token_field" "premise_limit" "context_chars" "definition_chars" "feedback_chars"
              "goal_state" "salvage" "timeout_ms" "proof_advice" "proof_chars"
              "example_pool" "examples" "temperature" "max_tokens" "retries") $key)))))))
(= (ai-proposal-main:policy $row)
   (and (foldl-atom ("call_cap" "rounds" "stride" "limit" "skip" "premise_limit" "context_chars"
                    "definition_chars" "feedback_chars" "timeout_ms" "proof_chars"
                    "examples" "max_tokens" "retries") true $ok $key
          (and $ok (ai-math:itp-natural (ai-proposal-main:option $row $key 0))))
     (and (> (ai-proposal-main:option $row "stride" 1) 0)
       (and (foldl-atom ("resume" "vampire_only" "goal_state" "salvage" "proof_advice") true $ok $key
              (let $value (ai-proposal-main:option $row $key false)
                (and $ok (or (== $value true) (== $value false)))))
         (and (ai-math:contains ("direct" "dsp") (ai-proposal-main:option $row "mode" "direct"))
           (and (ai-math:contains ("max_tokens" "max_completion_tokens")
                  (ai-proposal-main:option $row "token_field" "max_tokens"))
             (and (let $temperature (ai-proposal-main:option $row "temperature" 0.2)
                    (if (== (get-type $temperature) Number)
                      (and (>= $temperature 0.0) (<= $temperature 2.0)) false))
               (and (> (ai-proposal-main:option $row "retries" 4) 0)
                 (foldl-atom ("lean" "vampire" "example_pool") true $ok $key
                   (and $ok (== (get-type (ai-proposal-main:option $row $key "")) String)))))))))))
(= (ai-proposal-main:run $row)
   (if (ai-proposal-main:valid $row)
     (let* (($secret (system:getenv-or-default "LLM_API_KEY" ""))
            ($endpoint (system:getenv-or-default "LLM_BASE_URL" "")))
       (if (and (> (str:byte-length $secret) 0) (> (str:byte-length $endpoint) 0))
         (if (ai-math:contains (io:capabilities) http)
           (let* (($root (fs:canonical-path (str:concat (system:entry-directory) "/..")))
                  ($corpus (ai-proposal-main:option $row "corpus" AiMissing))
                  ($lean (ai-proposal-main:option $row "lean" (system:getenv-or-default "LEAN_BIN" "lean")))
                  ($vampire (ai-proposal-main:option $row "vampire" (system:getenv-or-default "VAMPIRE_BIN" "vampire")))
                  ($context (ai-math:prover-with (ai-math:load-library $corpus) $corpus $root $lean $vampire
                    ((use-duper false) (induction false))))
                  ($cap (ai-proposal-main:option $row "call_cap" 0))
                  ($pool-file (ai-proposal-main:option $row "example_pool" ""))
                  ($pool (if (== $pool-file "") ()
                    (ai-math:llm-example-pool (json:parse (fs:read-text $pool-file)))))
                  ($client (ai-math:llm-client $root (ai-math:http-session) $endpoint
                    (ai-proposal-main:option $row "model" AiMissing) $secret
                    (ai-proposal-main:option $row "ledger" AiMissing) $cap
                    ((token-field (ai-proposal-main:option $row "token_field" "max_tokens"))
                     (max-tokens (ai-proposal-main:option $row "max_tokens" 16000))
                     (temperature (ai-proposal-main:option $row "temperature"
                       (str:string->number (system:getenv-or-default "LLM_TEMPERATURE" "0.2"))))
                     (retries (ai-proposal-main:option $row "retries" 4))
                     (examples $pool)
                     (example-count (ai-proposal-main:option $row "examples" 0))
                     (premise-limit (ai-proposal-main:option $row "premise_limit" 96))
                     (context-chars (ai-proposal-main:option $row "context_chars" 80000))
                     (definition-chars (ai-proposal-main:option $row "definition_chars" 12000))
                     (feedback-chars (ai-proposal-main:option $row "feedback_chars" 2500))
                     (proof-advice (ai-proposal-main:option $row "proof_advice" false))
                     (proof-chars (ai-proposal-main:option $row "proof_chars" 12000))
                     (goal-state (ai-proposal-main:option $row "goal_state" true))
                     (salvage (ai-proposal-main:option $row "salvage" true))
                     (timeout-ms (ai-proposal-main:option $row "timeout_ms" 600000)))))
                  ($owner (ai-math:proposal-open $context $client $corpus
                    (ai-proposal-main:option $row "baseline" AiMissing) (ai-proposal-main:option $row "output" AiMissing)
                    (AiRun:Toolchain $lean $vampire (system:getenv-or-default "CETTA_BUILD_ID" "unspecified"))
                    (str:string->symbol (ai-proposal-main:option $row "mode" "direct"))
                    (ai-proposal-main:option $row "rounds" 3) (AiITP:Budget 300000 200000 8000)
                    (if (ai-proposal-main:option $row "resume" false) Resume Fresh)))
                  ($targets (ai-math:proposal-select $owner
                    (ai-proposal-main:option $row "stride" 1) (ai-proposal-main:option $row "limit" 0)
                    (ai-proposal-main:option $row "skip" 0) (ai-proposal-main:option $row "vampire_only" false))))
             (if (== (get-metatype $targets) Expression)
               (case $targets
                 (((AiProposal:Fault $why $details) $targets)
                  ($names (ai-math:proposal-run $owner $names)))) $targets))
           (AiLLM:ProviderRequest http))
         (AiProposal:Request credentials)))
     (AiProposal:Request configuration)))
!(if (== (system:argc) 1)
   (let* (($arg (system:arg 0)) ($path (if (== (get-metatype $arg) Symbol) (str:symbol->string $arg) $arg))
          ($result (ai-proposal-main:run (json:parse (fs:read-text $path)))))
     (let $printed (println! $result)
       (system:exit (case $result (((AiRun:Summary $key $count $outcomes $issues) 0) ($other 2))))))
   (let $printed (println! "usage: llm_experiment_main.metta run-config.json") (system:exit 2)))
