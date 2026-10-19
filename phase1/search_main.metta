; cetta --lang petta@1.0.6 phase1/search_main.metta corpus.sexpr
!(import! &self "library.metta")
!(import! &self (library list))
!(import! &self "search.metta")
!(import! &self system)

!(let $path (if (system:has-args) (system:arg 0) "data/corpus.sexpr")
   (case (ai-math:load-library $path)
     (((Error $reason $where)
       (let $printed (println! (Error $reason $where)) (system:exit 1)))
      ($decls (ai-math:evaluate-recall $decls)))))
