; cetta --lang petta@1.0.6 phase1/atp_main.metta corpus.sexpr goal-name [vampire]
!(import! &self proc)
!(import! &self "library.metta")
!(import! &self (library list))
!(import! &self (library lib_tptp))
!(import! &self re)
!(import! &self "vampire_output.metta")
!(import! &self "search.metta")
!(import! &self "atp.metta")
!(import! &self system)

; Command-line operands may arrive as MeTTa symbols. Names in the corpus are
; strings, so normalize that public CLI boundary without changing either API.
(= (ai-atp-main:text $argument)
   (if (== (get-metatype $argument) Symbol) (str:symbol->string $argument) $argument))

!(if (< (system:argc) 2)
   (let $printed (println! "usage: atp_main.metta corpus.sexpr goal-name [vampire]")
     (system:exit 2))
   (let* (($path (ai-atp-main:text (system:arg 0)))
          ($goal (ai-atp-main:text (system:arg 1)))
          ($executable (ai-atp-main:text (if (> (system:argc) 2) (system:arg 2)
                         (system:getenv-or-default "VAMPIRE_BIN" "vampire")))))
     (case (ai-math:load-library $path)
       (((Error $reason $where)
         (let $printed (println! (Error $reason $where)) (system:exit 1)))
        ($decls
         (let* (($search (ai-math:search $decls))
                ($context (ai-math:thf $decls $path)))
           (println! (ai-math:atp-goal $context $search $goal $executable 10 32))))))))
