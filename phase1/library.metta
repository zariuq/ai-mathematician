; A PeTTa port of ai-mathematician's phase1/library.py.
; Source: yenat/ai-mathematician, revision
; 5e73833790d43d066f72be1548be2ee0fcab192d.
; Import this file, then (ai-math:load-library "data/corpus.sexpr").
;
; A declaration is ordinary data:
; (Decl index kind name hash statement body symbols proof-dependencies features).
; Kind and typed term tags are symbols; names, hashes and features are strings.
; NoBody denotes a declaration without a body. The three sets are expressions
; of unique strings; their order is not significant. Declaration order is.
; Input is the typed export with quoted names/hashes and numeric indices.
; Reading uses MeTTa's inert reader and its normal string escapes, not the
; Python prototype's convention of dropping every string escape's backslash.

!(import! &self fs)
!(import! &self str)

(= (ai-math:logical-vocabulary)
   ("True" "False" "not" "and" "or" "iff" "ex" "eq" "neq"))

; The working dictionary is a local space with one entry per key. It is not
; another native collection type. Replacement is explicit, not add-atom-nodup.
(= (ai-math:get $space $key $default)
   (case (collapse (match $space (AiEntry $key $value) $value))
     ((() $default) (($value) $value))))

(= (ai-math:remove $space $key)
   (let $entries (collapse (match $space (AiEntry $key $value)
                                 (AiEntry $key $value)))
     (map-atom $entries $entry (remove-atom $space $entry))))

(= (ai-math:put $space $key $value)
   (let $removed (ai-math:remove $space $key)
     (add-atom $space (AiEntry $key $value))))

(= (ai-math:is-node $node)
   (if (== (get-metatype $node) Expression) (if (== $node ()) false true) false))

(= (ai-math:contains $items $item)
   (if (== (intersection-atom ($item) $items) ()) false true))

; Source positions, binder indices and explicit budgets share this carrier.
(= (ai-math:natural $value)
   (if (== (get-type $value) Number)
     (let $text (str:number->string $value)
       (and (> (str:byte-length $text) 0)
         (foldl-atom (str:codepoints $text) true $ok $cp
           (and $ok (ai-math:contains ("0" "1" "2" "3" "4" "5" "6" "7" "8" "9") $cp)))))
     false))

(= (ai-math:option $options $key $default)
   (if (== $options ()) $default
     (let (($name $value) $rest) (decons-atom $options)
       (if (== $name $key) $value (ai-math:option $rest $key $default)))))

; The exporter writes one form per line, interspersed with warnings.
; As in the Python reader, bad syntax is skipped, but a well-read declaration
; with the wrong shape is not silently accepted as a complete library.
(= (ai-math:read-line $line)
   (let $text (str:trim $line)
     (if (str:starts-with $text "(")
       (case (catch (parse-first $text))
         (((Error $reason $context) AiSkip)
          ($form (AiForm $form))))
       AiSkip)))

(= (ai-math:load-library $path)
   (ai-math:library-from-lines (fs:read-lines $path)))

(= (ai-math:library-from-text $text)
   (ai-math:library-from-lines (str:split "\n" $text)))

(= (ai-math:library-from-lines $lines)
   (case $lines
     (((Error $reason $context) $lines)
      ($items
       (let $context (new-space)
         (let $count
           (foldl-atom $items 0 $index $line
             (ai-math:read-next $context $index $line))
           (case $count
             (((Error $reason $where) $count)
              ($complete (ai-math:finish-all $context 0 $complete))))))))))

(= (ai-math:read-next $context $index $line)
   (case $index
     (((Error $reason $where) $index)
      ($next (case (ai-math:read-line $line)
               ((AiSkip $next)
                ((AiForm $form)
                 (case (ai-math:without-source-line $form)
                   (((Error $reason $where) (Error $reason $where))
                    ($record (ai-math:admit $context $next $record)))))))))))

; Both typed-export versions are accepted. The newer one appends a source
; line to each declaration, outside its term/proof. Strip only that field,
; at the declared arity; an arbitrary extra argument is not an annotation.
(= (ai-math:without-source-line $form)
   (case $form
     (((PARAM $n $h $a $ty $line)
       (ai-math:source-line $line (PARAM $n $h $a $ty) $form))
      ((AXIOM $n $h $a $ty $line)
       (ai-math:source-line $line (AXIOM $n $h $a $ty) $form))
      ((DEF $n $h $a $ty $body $line)
       (ai-math:source-line $line (DEF $n $h $a $ty $body) $form))
      ((PRIM $id $n $h $ty $line)
       (ai-math:source-line $line (PRIM $id $n $h $ty) $form))
      ((THM $n $h $ph $a $ty $line)
       (ai-math:source-line $line (THM $n $h $ph $a $ty) $form))
      ((PROOF $n $body $line)
       (ai-math:source-line $line (PROOF $n $body) $form))
      ($other $other))))

(= (ai-math:source-line $line $record $original)
   (if (== (get-type $line) Number)
     (if (and (>= $line 0) (== $line (floor-math $line))) $record
       (Error (AiMathMalformedDeclaration $original) ai-math:library-from-lines))
     (Error (AiMathMalformedDeclaration $original) ai-math:library-from-lines)))

(= (ai-math:finish-all $context $index $count)
   (if (== $index $count) ()
     (let $decl
       (ai-math:finish $context
         (match $context
           (AiDraft $index $kind $name $hash $stmt $body $syms $deps)
           (AiDraft $index $kind $name $hash $stmt $body $syms $deps)))
       (let $rest (ai-math:finish-all $context (+ $index 1) $count)
         (cons-atom $decl $rest)))))

(= (ai-math:add $context $index $kind $name $hash $stmt $body $syms $deps)
   (let $stored
     (add-atom $context (AiDraft $index $kind $name $hash $stmt $body $syms $deps))
     (let $named (ai-math:put $context (Hash $hash) $name)
       (+ $index 1))))

(= (ai-math:admit $context $index $form)
   (case $form
     (((PARAM $name $hash $ignored $ty)
       (ai-math:add $context $index PARAM $name $hash $ty NoBody
         (ai-math:collect $ty $context false) ()))
      ((AXIOM $name $hash $ignored $ty)
       (ai-math:add $context $index AXIOM $name $hash $ty NoBody
         (ai-math:collect $ty $context false) ()))
      ((DEF $name $hash $ignored $ty $term)
       (ai-math:add $context $index DEF $name $hash $ty $term
         (ai-math:collect $term $context false) ()))
      ((PRIM $id $name $hash $ty)
       (let $next (ai-math:add $context $index PRIM $name $hash $ty NoBody () ())
         (let $primitive (ai-math:put $context (Primitive $id) $name) $next)))
      ((THM $name $hash $proof-hash $ignored $ty)
       (let $saved
         (ai-math:put $context (Pending $name)
           (AiPending $hash $ty (ai-math:collect $ty $context false)))
         $index))
      ((PROOF $name $proof)
       (case (ai-math:get $context (Pending $name) AiMissing)
         ((AiMissing $index)
          ((AiPending $hash $ty $syms)
           (let $removed (ai-math:remove $context (Pending $name))
             (ai-math:add $context $index THM $name $hash $ty $proof $syms
               (ai-math:collect $proof $context true)))))))
      ($other
       (if (ai-math:is-node $other)
         (if (ai-math:contains (PARAM AXIOM DEF PRIM THM PROOF) (car-atom $other))
           (Error (AiMathMalformedDeclaration $other) ai-math:library-from-lines)
           $index)
         $index)))))

; Use an explicit work list instead of host recursion through a proof term.
(= (ai-math:collect $node $context $known-only)
   (unique-atom (ai-math:collect-walk ($node) $context $known-only ())))

(= (ai-math:collect-walk $work $context $known-only $out)
   (if (== $work ()) $out
     (let ($node $rest) (decons-atom $work)
       (if (ai-math:is-node $node)
         (case $node
           (((TMH $hash)
             (if $known-only (ai-math:collect-walk $rest $context $known-only $out)
               (ai-math:collect-name $rest $context $known-only $out
                 (ai-math:get $context (Hash $hash) ""))))
            ((PRIM $id)
             (if $known-only (ai-math:collect-walk $rest $context $known-only $out)
               (ai-math:collect-name $rest $context $known-only $out
                 (ai-math:get $context (Primitive $id) ""))))
            ((KNOWN $hash)
             (ai-math:collect-name $rest $context $known-only $out
               (ai-math:get $context (Hash $hash) "")))
            ($other (ai-math:collect-walk
                      (union-atom (cdr-atom $other) $rest) $context $known-only $out))))
         (ai-math:collect-walk $rest $context $known-only $out)))))

(= (ai-math:collect-name $rest $context $known-only $out $name)
   (ai-math:collect-walk $rest $context $known-only
     (if (== $name "") $out (cons-atom $name $out))))

(= (ai-math:head $node $context)
   (case $node
     (((AP $fn $arg) (ai-math:head $fn $context))
      ((TPAP $fn $ty) (ai-math:head $fn $context))
      ((TMH $hash) (ai-math:get $context (Hash $hash) "?"))
      ((DB $id) "_var")
      ($other (str:symbol->string (car-atom $other))))))

(= (ai-math:application $node $args)
   (case $node
     (((AP $fn $arg) (ai-math:application $fn (cons-atom $arg $args)))
      ($other (AiApplication $other $args)))))

(= (ai-math:edge-features $head $args $context)
   (map-atom $args $arg
     (str:concat (str:concat $head ">") (ai-math:head $arg $context))))

(= (ai-math:features-walk $work $context $out)
   (if (== $work ()) $out
     (let ($node $rest) (decons-atom $work)
       (if (ai-math:is-node $node)
         (case $node
           (((TMH $hash)
             (ai-math:features-walk $rest $context
               (cons-atom (ai-math:get $context (Hash $hash) "?") $out)))
            ((AP $fn $arg)
             (let (AiApplication $head $args) (ai-math:application $node ())
               (ai-math:features-walk (cons-atom $head (union-atom $args $rest))
                 $context (union-atom
                   (ai-math:edge-features (ai-math:head $head $context) $args $context)
                   $out))))
            ($other (ai-math:features-walk
                      (union-atom (cdr-atom $other) $rest) $context $out))))
         (ai-math:features-walk $rest $context $out)))))

(= (ai-math:conclusion $node $hyps)
   (case $node
     (((ALL $ty $body) (ai-math:conclusion $body $hyps))
      ((IMP $hyp $body) (ai-math:conclusion $body (cons-atom $hyp $hyps)))
      ($other (AiConclusion $other $hyps)))))

(= (ai-math:features $stmt $context)
   (let $symbols (ai-math:features-walk ($stmt) $context ())
     (let (AiConclusion $node $hyps) (ai-math:conclusion $stmt ())
       (let $hyp-features
         (map-atom $hyps $hyp (str:concat "hyp:" (ai-math:head $hyp $context)))
         (if (ai-math:is-node $node)
           (let $head (ai-math:head $node $context)
             (let $edges
               (case $node
                 (((AP $fn $arg)
                   (let (AiApplication $root $args) (ai-math:application $node ())
                     (ai-math:edge-features (str:concat "concl:" $head) $args $context)))
                  ($other ())))
               (unique-atom (union-atom $symbols
                 (cons-atom (str:concat "concl:" $head)
                   (union-atom $edges $hyp-features))))))
           (unique-atom (union-atom $symbols $hyp-features)))))))

; Features deliberately see the final name map, unlike symbols collected at
; admission time. A theorem's index is its PROOF position, not its THM line.
(= (ai-math:finish $context (AiDraft $index $kind $name $hash $stmt $body $syms $deps))
   (let $features (ai-math:features (if (== $kind DEF) $body $stmt) $context)
     (Decl $index $kind $name $hash $stmt $body $syms $deps $features)))

(= (ai-math:declaration-name (Decl $i $k $name $h $s $b $ss $ds $fs)) $name)
(= (ai-math:declaration-kind (Decl $i $kind $n $h $s $b $ss $ds $fs)) $kind)
(= (ai-math:declaration-dependencies (Decl $i $k $n $h $s $b $ss $deps $fs)) $deps)

(= (ai-math:library-summary $decls)
   (let $counts (new-space)
     (let $counted
       (map-atom $decls $decl
         (let $kind (ai-math:declaration-kind $decl)
           (ai-math:put $counts $kind (+ 1 (ai-math:get $counts $kind 0)))))
       (let $theorems (ai-math:get $counts THM 0)
         (let $citations
           (foldl-atom $decls 0 $total $decl
             (if (== (ai-math:declaration-kind $decl) THM)
               (+ $total (size-atom (ai-math:declaration-dependencies $decl))) $total))
           (LibrarySummary (size-atom $decls)
             (collapse (match $counts (AiEntry $kind $count) (Kind $kind $count)))
             (Theorems $theorems (FactsCited $citations)
               (MeanCitations (if (== $theorems 0) NoTheorems (/ $citations $theorems))))))))))

(= (ai-math:diagnostic $decl)
   (let (Decl $i $kind $name $h $s $b $syms $deps $features) $decl
     (DeclSymbols $kind $name (sort-atom $syms) (sort-atom $deps))))

(= (ai-math:library-diagnostics $decls)
   (foldl-atom ("andI" "Subq_ref" "set_ext") () $out $name
     (union-atom $out
       (map-atom
         (filter-atom $decls $decl (== (ai-math:declaration-name $decl) $name))
         $decl (ai-math:diagnostic $decl)))))
