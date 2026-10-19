; An explicit producer-spelling adapter, not a change to strict TPTP.
; Some Vampire proofs print hyphenated inference-rule names without quotes.
; Protect quoted words/objects and comments, then quote only that argument.
; The strict reader still validates every resulting record. Raw process/SZS
; observations are retained separately, and every edit has original byte spans.

(= (ai-math:vampire-codec)
   (let* (($quoted "'(?:\\\\.|[^'\\\\])*'|\"(?:\\\\.|[^\"\\\\])*\"|%[^\\n]*(?:\\n|$)|/\\*.*?\\*/")
          ($lexical-text (str:join "" ("(?s)(?:" $quoted "|[^'\"/%]|/(?!\\*))*")))
          ($scanner-text (str:join "" ("(?s)" $quoted
              "|(inference[ \\t\\r\\n]*\\([ \\t\\r\\n]*)([a-z][A-Za-z0-9_]*(?:-[A-Za-z0-9_]+)+)([ \\t\\r\\n]*,)|[A-Za-z_$][A-Za-z0-9_$]*")))
          ($lexical (re:prepare (re:pattern $lexical-text)))
          ($scanner (re:prepare (re:pattern $scanner-text))))
     (AiATP:VampireCodec $lexical $scanner)))
(= (ai-math:vampire-patch $matches $body $cursor $pieces $repairs)
   (case $matches
     ((LNil
       (AiATP:ProducerText (str:join "" (list:reverse
           (cons-atom (str:byte-slice $body $cursor (str:byte-length $body)) $pieces)))
         (list:reverse $repairs)))
      ((LCons $match $rest)
       (case (re:group-span $match 2)
         (((re:span $start $end)
           (let* (($rule (str:byte-slice $body $start $end))
                  ($quoted (str:join "" ("'" $rule "'")))
                  ($prefix (str:byte-slice $body $cursor $start)))
             (ai-math:vampire-patch $rest $body $end
               (cons-atom $quoted (cons-atom $prefix $pieces))
               (cons-atom (AiATP:RuleNameQuote $start $end $rule) $repairs))))
          ((re:unmatched $group) (ai-math:vampire-patch $rest $body $cursor $pieces $repairs))
          ($other (AiATP:ProducerInterpretationNeeded capture-layout))))))))
(= (ai-math:vampire-normalize (AiATP:VampireCodec $lexical $scanner) $body)
   (case (re:full-match $lexical $body)
     (((re:match $start $end $captures)
       (case (re:find-all $scanner $body)
         (((re:matches $matches) (ai-math:vampire-patch $matches $body 0 () ()))
          ($other (AiATP:ProducerInterpretationNeeded lexical-scan)))))
      ($other (AiATP:ProducerInterpretationNeeded incomplete-lexical-input)))))
(= (ai-math:vampire-context-codec $index)
   (case (ai-math:get $index (Format VampireRuleNames) AiMissing)
     ((AiMissing
       (let $codec (ai-math:vampire-codec)
         (let $stored (ai-math:put $index (Format VampireRuleNames) $codec) $codec)))
      ($codec $codec))))
(= (ai-math:vampire-read-payload $index $reader $body)
   (let $strict (tptp:read-text $reader $body)
     (case $strict
       (((TPTP:NoParse $offset $start-symbol)
         (if (== (get-type (str:find $body "-")) Number)
           (case (ai-math:vampire-normalize (ai-math:vampire-context-codec $index) $body)
             (((AiATP:ProducerText $text $repairs)
               (if (== $repairs ()) $strict
                 (let $records (tptp:read-text $reader $text)
                   (if (list:is-list $records)
                     (AiATP:ProducerPayload VampireRuleNames $records $repairs) $records))))
              ($other $strict))) $strict))
        ($other $strict)))))
(= (ai-math:vampire-payload-records $payload)
   (case $payload
     (((AiATP:ProducerPayload VampireRuleNames $records $repairs) $records)
      ($other $other))))

; A complete producer block may contain annotations outside strict TPTP.
; Lexical references are search hints only: retain the failed strict parse,
; the raw spellings and byte spans, and never call this a parsed proof.
(= (ai-math:vampire-reference-scanner $index)
   (case (ai-math:get $index (Format VampireReferenceHints) AiMissing)
     ((AiMissing
       (let* (($quoted "'(?:\\\\.|[^'\\\\])*'|\"(?:\\\\.|[^\"\\\\])*\"|%[^\\n]*(?:\\n|$)|/\\*.*?\\*/")
              ($space "(?:[ \\t\\r\\n]|%[^\\n]*(?:\\n|$)|/\\*.*?\\*/)*")
              ($word "(?:'(?:\\\\.|[^'\\\\])*'|[a-z][A-Za-z0-9_]*|[0-9]+)")
              ($pattern (str:join "" ("(?s)" $quoted "|file" $space "\\(" $space
                "(" $word ")" $space "," $space "(" $word ")" $space
                "\\)|[A-Za-z_$][A-Za-z0-9_$]*")))
              ($scanner (re:prepare (re:pattern $pattern))))
         (let $stored (ai-math:put $index (Format VampireReferenceHints) $scanner) $scanner)))
      ($scanner $scanner))))
(= (ai-math:vampire-reference-hints $matches $body)
   (case $matches
     ((LNil ())
      ((LCons $match $rest)
       (let $tail (ai-math:vampire-reference-hints $rest $body)
         (case (re:group-span $match 2)
           (((re:span $start $end)
             (cons-atom (AiATP:LexicalReference $start $end
               (re:group-text $match $body 1) (str:byte-slice $body $start $end)) $tail))
            ($other $tail))))))))
(= (ai-math:vampire-read-advice-payload $index $reader $body)
   (let $strict (ai-math:vampire-read-payload $index $reader $body)
     (if (list:is-list (ai-math:vampire-payload-records $strict)) $strict
       (let (AiATP:VampireCodec $lexical $rules) (ai-math:vampire-context-codec $index)
         (case (re:full-match $lexical $body)
           (((re:match $start $end $captures)
             (case (re:find-all (ai-math:vampire-reference-scanner $index) $body)
               (((re:matches $matches)
                 (let $references (ai-math:vampire-reference-hints $matches $body)
                   (if (== $references ()) $strict
                     (AiATP:LexicalAdvicePayload $references $strict))))
                ($other $strict))))
            ($other $strict)))))))
(= (ai-math:vampire-payload-references $payload)
   (case $payload
     (((AiATP:LexicalAdvicePayload $references $strict) $references)
      ($other (let $records (ai-math:vampire-payload-records $other)
                (if (list:is-list $records) (tptp:input-references $records) ()))))))
(= (ai-math:vampire-payload-advice-ready $payload)
   (case $payload
     (((AiATP:LexicalAdvicePayload $references $strict) (not (== $references ())))
      ($other (list:is-list (ai-math:vampire-payload-records $other))))))
(= (ai-math:vampire-reference-name $reference)
   (case $reference
     (((TPTP:InputReference $record $path $name) $name)
      ((AiATP:LexicalReference $start $end $path $raw)
       (if (str:starts-with $raw "'")
         (str:byte-slice $raw 1 (- (str:byte-length $raw) 1)) $raw)))))
