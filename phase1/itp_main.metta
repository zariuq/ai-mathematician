; cetta --no-results --lang petta@1.0.6 phase1/itp_main.metta corpus.sexpr goal tactic-file [lean]
!(import! &self "library.metta")
!(import! &self proc)
!(import! &self json)
!(import! &self system)
!(import! &self "itp.metta")

(= (ai-itp-main:text $value)
   (if (== (get-metatype $value) Symbol) (str:symbol->string $value) $value))

(= (ai-itp-main:exit-code $result)
   (case $result
     (((AiITP:Accepted $target $used $axioms) 0)
      ((AiITP:Rejected $target $reason $detail) 1)
      ((AiITP:Unfinished $target $reason $detail) 3)
      ($other 2))))

!(if (< (system:argc) 3)
   (let $printed (println! "usage: itp_main.metta corpus.sexpr goal tactic-file [lean]")
     (system:exit 2))
   (let* (($corpus (ai-itp-main:text (system:arg 0)))
          ($target (ai-itp-main:text (system:arg 1)))
          ($tactic (fs:read-text (ai-itp-main:text (system:arg 2))))
          ($lean (ai-itp-main:text (if (> (system:argc) 3) (system:arg 3)
                   (system:getenv-or-default "LEAN_BIN" "lean")))))
     (case (ai-math:load-library $corpus)
       (((Error $reason $where)
         (let $printed (println! (Error $reason $where)) (system:exit 1)))
        ($decls
         (let $root (fs:canonical-path (str:concat (system:entry-directory) "/.."))
           (let $result (ai-math:itp-check (ai-math:itp $decls $root $lean) $target $tactic)
             (let $printed (println! $result)
               (system:exit (ai-itp-main:exit-code $result))))))))))
