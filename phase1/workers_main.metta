; One coordinator owns a run directory; flock releases ownership on exit.
!(import! &self proc)
!(import! &self "library.metta")
!(import! &self (library list))
!(import! &self json)
!(import! &self system)
!(import! &self "itp.metta")
!(import! &self "prover.metta")
!(import! &self "experiment.metta")
!(import! &self "experiment_workers.metta")

!(if (== (system:argc) 1)
   (let* (($arg (system:arg 0)) ($path (if (== (get-metatype $arg) Symbol) (str:symbol->string $arg) $arg))
          ($root (fs:canonical-path (str:concat (system:entry-directory) "/..")))
          ($config (ai-math:workers-config $path $root)))
     (case $config
       (((AiWorkers:Config $row $app $corpus $output $binary $lean $vampire)
         (case (proc:run
                 ("flock" "--exclusive" "--nonblock" "--conflict-exit-code" "4"
                   (str:concat $output ".lock") $binary "--no-results" "--lang" "petta"
                   (str:concat $root "/phase1/workers_driver.metta") (fs:canonical-path $path)) ((lifetime owner)))
           (((proc:result (proc:exited $code) proc:normal $out $err
               (proc:capture $kept $seen $ek $es proc:eof proc:eof (proc:input $sent $size)))
             (if (and (== $kept $seen) (and (== $ek $es) (== $sent $size)))
               (let* (($wrote-out (system:write stdout $out)) ($wrote-err (system:write stderr $err)))
                 (system:exit $code))
               (let $printed (println! (AiWorkers:Fault coordinator-capture)) (system:exit 2))))
            ($fault (let $printed (println! (AiWorkers:Fault coordinator-process $fault)) (system:exit 2))))))
        ($fault (let $printed (println! $fault) (system:exit 2))))))
   (let $printed (println! "usage: workers_main.metta run-config.json") (system:exit 2)))
