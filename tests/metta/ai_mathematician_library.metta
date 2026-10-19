!(import! &self "../../phase1/library.metta")

; Two positive ingestion examples: a definition uses its body for symbols;
; a theorem enters the library at PROOF, with actual cited facts only.
!(test
   (ai-math:library-from-lines
     ("(PARAM \"p\" \"hp\" 0 (PROP))"
      "(DEF \"id\" \"hi\" 0 (TMH \"not-a-dependency\") (TMH \"hp\"))"))
   ((Decl 0 PARAM "p" "hp" (PROP) NoBody () () ("concl:PROP"))
    (Decl 1 DEF "id" "hi" (TMH "not-a-dependency") (TMH "hp")
      ("p") () ("p" "concl:p"))))

!(test
   (ai-math:library-from-lines
     ("(PARAM \"p\" \"hp\" 0 (PROP))"
      "(THM \"t\" \"ht\" \"pt\" 0 (TMH \"hp\"))"
      "(PROOF \"t\" (PAIR (KNOWN \"hp\") (TMH \"not-cited\")))"))
   ((Decl 0 PARAM "p" "hp" (PROP) NoBody () () ("concl:PROP"))
    (Decl 1 THM "t" "ht" (TMH "hp")
      (PAIR (KNOWN "hp") (TMH "not-cited")) ("p") ("p") ("p" "concl:p"))))

; Negative controls: no invented theorem, no declaration from a truncated
; line, and no silently accepted malformed declaration or unreadable file.
!(test
   (ai-math:library-from-lines
     ("WARNING: not an expression"
      "(THM \"unproved\" \"h\" \"p\" 0 (PROP))"
      "(PROOF \"orphan\" (KNOWN \"h\"))"
      "(PARAM \"truncated\""))
   ())

!(test
   (case (catch (ai-math:library-from-lines ("(PARAM wrong-shape)")))
     (((Error $reason $context) Rejected) ($other IncorrectlyAccepted)))
   Rejected)

!(test
   (case (catch (ai-math:load-library "tests/fixtures/does-not-exist.sexpr"))
     (((Error $reason $context) MissingFile) ($other IncorrectlyAccepted)))
   MissingFile)

; Replacing a keyed value leaves one entry, unlike merely adding two facts.
!(test
   (let $space (new-space)
     (let $first (ai-math:put $space key 1)
       (let $second (ai-math:put $space key 2)
         (collapse (match $space (AiEntry key $value) $value)))))
   (2))

; Separate loads have separate working spaces and do not leak names.
!(test
   (let $first (ai-math:library-from-lines ("(PARAM \"p\" \"h\" 0 (PROP))"))
     (ai-math:library-from-lines ("(DEF \"d\" \"hd\" 0 (PROP) (TMH \"h\"))")))
   ((Decl 0 DEF "d" "hd" (PROP) (TMH "h") () () ("?" "concl:?"))))

; Empty input is a usable library, including its summary.
!(test
   (ai-math:library-summary ())
   (LibrarySummary 0 () (Theorems 0 (FactsCited 0) (MeanCitations NoTheorems))))
