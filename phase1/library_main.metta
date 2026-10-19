; cetta --lang petta@1.0.6 phase1/library_main.metta corpus.sexpr
; Without an argument, use data/corpus.sexpr, as the Python entry point does.
!(import! &self "library.metta")
!(import! &self system)

!(let $path (if (system:has-args) (system:arg 0) "data/corpus.sexpr")
   (case (ai-math:load-library $path)
     (((Error $reason $context)
       (let $printed (println! (Error $reason $context)) (system:exit 1)))
      ($decls
       (let $printed (println! (ai-math:library-summary $decls))
         (ai-math:library-diagnostics $decls))))))
