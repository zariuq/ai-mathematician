; Compatibility with the statement-embedding experiment. This explicitly
; named profile reuses document vectors for queries and uses normalized dot
; products, including Python's zero-vector convention. Qwen's separate
; document/query modes and the ordinary cosine API are unchanged.
(= (ai-math:embedding-lean-texts $path)
   (let* (($source (fs:read-text $path)) ($space (new-space))
          ($parser (re:prepare (re:pattern "^(axiom|noncomputable def|theorem)\\s+(\\S+)")))
          ($loaded (map-atom (str:split "\n" $source) $line
            (case (re:find-all $parser $line)
              (((re:matches (LCons $match $rest))
                (let* (($kind (re:group-text $match $line 1)) ($raw (re:group-text $match $line 2))
                       ($name (if (and (str:starts-with $raw "«") (str:ends-with $raw "»"))
                         (str:from-codepoints (list:take (- (str:codepoint-count $raw) 2)
                           (list:drop 1 (str:codepoints $raw)))) $raw))
                       ($text (if (== $kind "theorem") (car-atom (str:split " := " $line)) $line)))
                  (ai-math:put $space $name (str:trim $text)))) ($other ()))))))
     (AiEmbeddingTexts (str:sha256 $source) $space)))
(= (ai-math:embedding-python-rows $declarations (AiEmbeddingTexts $source $texts))
   (ai-math:research-concat (map-atom $declarations $decl
     (let* (($name (ai-math:declaration-name $decl)) ($text (ai-math:get $texts $name NoEmbeddingText)))
       (if (== $text NoEmbeddingText) ()
         ((AiPythonEmbeddingRow (ai-math:declaration-index $decl) (ai-math:declaration-kind $decl)
           $name (ai-math:embedding-python-text $name $text))))))))
(= (ai-math:embedding-python-text $name $declaration-text)
   (let* (($header (re:prepare (re:pattern "^(theorem|axiom|noncomputable def)\\s+\\S+\\s*")))
          ($variables (re:prepare (re:pattern "x\\d+")))
          ($statement (re:replace-literal $variables (re:replace-literal $header $declaration-text "") "x")))
     (str:join "" ((str:join " " (str:split "_" $name)) " : "
       (str:from-codepoints (list:take 1500 (str:codepoints $statement)))))))
(= (ai-math:embedding-python-normalize $vector)
   (let* (($width (car-atom (tensor:shape $vector)))
          ($dot (tensor:matvec (tensor:reshape $vector (1 $width)) $vector sequential))
          ((tensor:present $sum) (tensor:at $dot (0)))
          ($norm (sqrt-math $sum)))
     (if (== $norm 0.0) $vector
       (tensor:convert (tensor:zip-map f64 ($vector) ai-math:embedding-python-divide ($norm)) dense))))
(= (ai-math:embedding-python-divide $norm $value) (/ $value $norm))
(= (ai-math:embedding-python-rows-valid $rows)
   (and (foldl-atom $rows true $ok $row
     (and $ok (case $row
       (((AiPythonEmbeddingRow $source $kind $name $text)
         (and (ai-math:natural $source) (and (ai-math:contains (PARAM PRIM DEF THM AXIOM) $kind)
           (and (== (get-type $name) String) (== (get-type $text) String))))) ($other false)))))
     (and (== (size-atom $rows) (size-atom (unique-atom (map-atom $rows $row (index-atom $row 1)))))
          (== (size-atom $rows) (size-atom (unique-atom (map-atom $rows $row (index-atom $row 3))))))))
(= (ai-math:embedding-python-build $profile $rows $vectors)
   (if (and (ai-math:embedding-python-rows-valid $rows)
        (and (== (size-atom $rows) (size-atom $vectors))
            (foldl-atom $vectors true $ok $vector
              (and $ok (if (== (get-type $vector) Tensor)
                (and (== (tensor:dtype $vector) f64)
                  (and (== (tensor:shape $vector) ((index-atom $profile 4))) (tensor:all-finite $vector))) false)))))
     (AiPythonEmbedding PythonDocumentQueryV1 $profile
       (map-atom (collapse (ai-math:positions 0 (size-atom $rows))) $i
         (let (AiPythonEmbeddingRow $source $kind $name $text) (index-atom $rows $i)
           (AiPythonEmbeddingRow $source $kind $name $text
             (ai-math:embedding-python-normalize (index-atom $vectors $i))))))
     (AiEmbeddingFault invalid-python-vectors)))
(= (ai-math:embedding-python-from-matrix $profile $rows $matrix)
   (if (and (== (get-type $matrix) Tensor)
            (== (tensor:shape $matrix) ((size-atom $rows) (index-atom $profile 4))))
     (let $width (index-atom $profile 4)
       (ai-math:embedding-python-build $profile $rows
         (map-atom (collapse (ai-math:positions 0 (size-atom $rows))) $i
           (tensor:view $matrix ($width) (1) (* $i $width)))))
     (AiEmbeddingFault python-matrix-shape)))
(= (ai-math:embedding-python-rank $context $goal-index $limit)
   (ai-math:embedding-python-rank $context $goal-index $limit (THM AXIOM)))
(= (ai-math:embedding-python-rank (AiPythonEmbedding PythonDocumentQueryV1 $profile $rows) $goal-index $limit $kinds)
   (case (filter-atom $rows $row (== (index-atom $row 1) $goal-index))
     ((($goal)
       (let* (($query (index-atom $goal 5)) ($width (index-atom $profile 4))
              ($eligible (filter-atom $rows $row
                (and (< (index-atom $row 1) $goal-index) (ai-math:contains $kinds (index-atom $row 2)))))
              ($scored (map-atom $eligible $row
                (let (tensor:present $score) (tensor:at
                    (tensor:matvec (tensor:reshape (index-atom $row 5) (1 $width)) $query sequential) (0))
                  ($score (index-atom $row 3))))))
         (map-atom (list:take $limit (list:reverse (sort-atom $scored))) $row (index-atom $row 1))))
      (() ())
      ($other (AiEmbeddingFault ambiguous-source-position)))))
(= (ai-math:reciprocal-rank-fuse $rankings $offset $limit)
   (if (and (ai-math:natural $offset) (ai-math:natural $limit))
     (let $scores (list:group-sums-number-blocks (map-atom $rankings $names
       (map-atom (collapse (ai-math:positions 0 (size-atom $names))) $i
         ((index-atom $names $i) (/ 1.0 (+ (+ $offset $i) 1.0))))))
       (ai-math:entry-names (list:take $limit (ai-math:sort-scores $scores))))
     (AiEmbeddingFault invalid-fusion-policy)))

; OpenAI-compatible responses are read through scalar metadata projections
; and the existing numeric JSON sink. Normal decoding never builds one atom
; per embedding coordinate. Explicit response indices restore request order.
(= (ai-math:embedding-openai-decode $profile $texts $body)
   (let* (((EmbeddingProfile $identity $model $protocol $dimension $recipe $url) $profile)
          ($count (size-atom $texts))
          ($indices (map-atom (collapse (ai-math:positions 0 $count)) $i
             (json:parse-at $body ("data" $i "index"))))
          ($reported (json:parse-at $body ("model")))
          ($extra (json:parse-at $body ("data" $count))))
     (if (and (== $protocol "OpenAIEmbeddingsV1")
          (and (or (== $reported JsonMissingV1) (== $reported $model))
            (and (== $extra JsonMissingV1)
              (and (if (== $count 0) (== (json:parse-at $body ("data")) (JsonArray ())) true)
               (and (foldl-atom $indices true $ok $i (and $ok (ai-math:natural $i)))
                   (== (sort-atom $indices) (collapse (ai-math:positions 0 $count))))))))
       (let* (($ordered (sort-atom (map-atom (collapse (ai-math:positions 0 $count)) $i ((index-atom $indices $i) $i))))
              ($vectors (map-atom $ordered $entry
                (tensor:from-json f64 ($dimension) $body ("data" (index-atom $entry 1) "embedding")))))
         (if (foldl-atom $vectors true $ok $vector
               (and $ok (if (== (get-type $vector) Tensor) (tensor:all-finite $vector) false)))
           (case (embedding:request $profile "document" $texts ())
             (((Embedding:Request $p $kind $n $key $request) (AiOpenAIEmbeddingBatch $profile $key $texts $vectors))
              ($other $other)))
           (AiEmbeddingFault numeric-response)))
       (AiEmbeddingFault incompatible-or-malformed-provider-response))))
(= (ai-math:embedding-openai-batch $client $profile $texts)
   (let* (((EmbeddingProfile $identity $model $protocol $dimension $recipe $url) $profile)
          ($admission (embedding:request $profile "document" $texts ()))
          ($configured (and (case $admission (((Embedding:Request $p $k $n $key $r) true) ($other false)))
           (and (== $protocol "OpenAIEmbeddingsV1")
             (and (== $model (ai-math:llm-config $client Model))
                  (== $url (ai-math:llm-config $client Endpoint)))))))
     (if $configured
       (case (ai-math:llm-reserve $client)
         (((AiLLM:Reserved $number)
           (let* (($start (system:monotonic-ns))
                  ($options (ai-math:llm-config $client Options))
                  ($endpoint (str:concat (if (str:ends-with $url "/") (str:byte-slice $url 0 (- (str:byte-length $url) 1)) $url) "/embeddings"))
                  ($response (ai-math:http-request (index-atom $client 2) "POST" $endpoint
                    ((http:header "Content-Type" "application/json")
                     (http:header "Authorization" (str:concat "Bearer " (ai-math:llm-config $client Secret))))
                    (json:stringify (JsonObject ((JsonPair "model" $model) (JsonPair "input" (JsonArray $texts)))))
                    (ai-math:option $options timeout-ms 120000) (ai-math:option $options max-bytes 8388608)))
                  ($decoded (case $response
                    (((AiHTTP:Response $status $body)
                      (if (ai-math:llm-credential-in $client $body) (AiEmbeddingFault credential-in-response)
                       (if (and (>= $status 200) (< $status 300))
                        (ai-math:embedding-openai-decode $profile $texts $body) (AiEmbeddingFault http-status $status)))
                       )
                     ($other (AiEmbeddingFault transport $other)))))
                  ($usage (case $response
                    (((AiHTTP:Response $s $body) (ai-math:llm-safe-usage (json:parse-at $body ("usage")))) ($other JsonNull))))
                  ($recorded (ai-math:llm-record-usage $client $number $usage (- (system:monotonic-ns) $start))))
             (AiOpenAIEmbeddingResult $decoded (AiLLM:Receipt $number $usage $recorded))))
          ($other $other))) (AiEmbeddingFault provider-profile-mismatch))))
(= (ai-math:embedding-openai-cache-put $cache (AiOpenAIEmbeddingBatch $profile $key $texts $vectors))
   (map-atom (collapse (ai-math:positions 0 (size-atom $texts))) $i
     (embedding:cache-put $cache (embedding:from-tensor $profile "document" ((index-atom $texts $i))
       (tensor:reshape (index-atom $vectors $i) (1 (index-atom $profile 4)))))))
(= (ai-math:embedding-python-cache-vector $cache $profile $text)
   (case (embedding:cache-get $cache (embedding:request $profile "document" ($text) ()))
     (((Embedding:Batch $same "document" $key $matrix)
       (if (== (get-type $matrix) Tensor)
         (if (and (== (tensor:shape $matrix) (1 (index-atom $profile 4)))
                  (and (== (tensor:dtype $matrix) f64) (tensor:all-finite $matrix)))
           (AiEmbeddingVector (tensor:reshape $matrix ((index-atom $profile 4))))
           (AiEmbeddingFault corrupt-cache-vector)) (AiEmbeddingFault corrupt-cache-vector)))
      ($other $other))))
(= (ai-math:embedding-python-prepare $client $profile $rows $cache $batch-size)
   (if (and (ai-math:embedding-python-rows-valid $rows) (and (ai-math:natural $batch-size) (> $batch-size 0)))
     (let* (($observed (map-atom $rows $row (ai-math:embedding-python-cache-vector $cache $profile (index-atom $row 4))))
            ($bad (filter-atom $observed $entry (case $entry
              ((Embedding:Missing false) ((AiEmbeddingVector $vector) false) ($other true)))))
            ($missing (filter-atom (collapse (ai-math:positions 0 (size-atom $rows))) $i
              (== (index-atom $observed $i) Embedding:Missing)))
            ($prepared (if (== $bad ())
              (ai-math:embedding-python-fetch-missing $client $profile
                (map-atom $missing $i (index-atom (index-atom $rows $i) 4)) $cache $batch-size) (car-atom $bad))))
       (case $prepared
         ((Embedding:Ready
           (ai-math:embedding-python-build $profile $rows (map-atom $rows $row
             (let (AiEmbeddingVector $vector) (ai-math:embedding-python-cache-vector $cache $profile (index-atom $row 4)) $vector))))
          ($other $other)))) (AiEmbeddingFault invalid-batch-size)))
(= (ai-math:embedding-python-fetch-missing $client $profile $texts $cache $batch-size)
   (if (== $texts ()) Embedding:Ready
     (case (ai-math:embedding-openai-batch $client $profile (list:take $batch-size $texts))
       (((AiOpenAIEmbeddingResult (AiOpenAIEmbeddingBatch $p $key $items $vectors) $receipt)
         (let $stored (ai-math:embedding-openai-cache-put $cache (AiOpenAIEmbeddingBatch $p $key $items $vectors))
           (if (foldl-atom (collapse (ai-math:positions 0 (size-atom $items))) true $ok $i
                 (and $ok (case (ai-math:embedding-python-cache-vector $cache $p (index-atom $items $i))
                   (((AiEmbeddingVector $actual) (== $actual (index-atom $vectors $i))) ($other false)))))
             (ai-math:embedding-python-fetch-missing $client $profile (list:drop $batch-size $texts) $cache $batch-size)
             (AiEmbeddingFault cache-publication))))
        ($other $other)))))
(= (ai-math:embedding-profile-json (EmbeddingProfile $id $model $protocol $dimension $recipe $url))
   (JsonObject ((JsonPair "identity" $id) (JsonPair "model" $model) (JsonPair "protocol" $protocol)
     (JsonPair "dimension" $dimension) (JsonPair "recipe" $recipe) (JsonPair "endpoint_sha256" (str:sha256 $url)))))
(= (ai-math:embedding-cache-save (Embedding:Cache $space) $profile $texts $path)
   (let $rows (map-atom (unique-atom $texts) $text
      (case (embedding:cache-get (Embedding:Cache $space) (embedding:request $profile "document" ($text) ()))
        (((Embedding:Batch $same $kind $key $matrix)
          (let $wire (tensor:encode $matrix)
            (if (== (get-type $wire) String)
              (JsonObject ((JsonPair "text" $text) (JsonPair "key" $key)
                (JsonPair "ctn1_escaped" (str:escape metta $wire))))
              (AiEmbeddingFault unsupported-cache-encoding))))
         ($other (AiEmbeddingFault incomplete-cache)))))
     (if (foldl-atom $rows true $ok $row (and $ok
           (case $row (((JsonObject $fields) true) ($other false)))))
       (ai-math:run-publish-file $path (json:stringify (JsonObject
         ((JsonPair "schema" "ai-math.embedding-cache.v1") (JsonPair "encoding" "CTN1/MeTTaEscapeV1")
          (JsonPair "profile" (ai-math:embedding-profile-json $profile))
          (JsonPair "rows" (JsonArray $rows)))))) (AiEmbeddingFault incomplete-cache))))
(= (ai-math:embedding-cache-load $profile $path)
   (let $document (json:parse (fs:read-text $path))
     (if (and (== (json:get $document "schema") "ai-math.embedding-cache.v1")
           (and (== (json:get $document "encoding") "CTN1/MeTTaEscapeV1")
              (== (json:get $document "profile") (ai-math:embedding-profile-json $profile))))
       (case (json:get $document "rows")
         (((JsonArray $rows)
           (let* (($cache (embedding:cache-new))
                  ($decoded (map-atom $rows $row
                    (let* (($text (json:get $row "text")) ($key (json:get $row "key"))
                           ($matrix (tensor:decode (str:unescape metta (json:get $row "ctn1_escaped"))))
                           ($batch (embedding:from-tensor $profile "document" ($text) $matrix)))
                      (case $batch
                        (((Embedding:Batch $p $kind $expected $vectors)
                          (if (== $key $expected) (embedding:cache-put $cache $batch)
                            (AiEmbeddingFault corrupt-cache-key)))
                         ($other (AiEmbeddingFault corrupt-cache-data)))))))
                  ($failed (filter-atom $decoded $row (case $row
                    (((AiEmbeddingFault $why) true) ((Embedding:Fault $why) true) ($other false))))))
             (if (== $failed ()) $cache (AiEmbeddingFault corrupt-cache-data))))
          ($other (AiEmbeddingFault corrupt-cache-data)))) (AiEmbeddingFault incompatible-cache))))
