; Induction advice over typed Megalodon terms, on PeTTa 1.0.6.
; Case formulas come from the actual earlier principle declaration, not a
; second implementation of its mathematics. Final Lean checking is separate.

(= (ai-math:ind-node $tag $arguments)
   (let $request (filter-atom $arguments $argument
          (case $argument (((AiInd:Request $reason $term) true) ($other false))))
     (if (== $request ())
       (AiInd:Syntax (cons-atom $tag (map-atom $arguments $argument (index-atom $argument 1))))
       (car-atom $request))))
(= (ai-math:ind-named $term $scope $path $env)
   (case $term
     (((DB $i)
       (if (and (ai-math:natural $i) (< $i (size-atom $env)))
         (AiInd:Syntax (VAR (index-atom $env (- (- (size-atom $env) $i) 1))))
         (AiInd:Request free-variable $term)))
      ((ALL $ty $body) (ai-math:ind-named-binder ALL $ty $body $scope $path $env))
      ((LAM $ty $body) (ai-math:ind-named-binder LAM $ty $body $scope $path $env))
      ((AP $f $a) (ai-math:ind-node AP
        ((ai-math:ind-named $f $scope (AiInd:Left $path) $env)
         (ai-math:ind-named $a $scope (AiInd:Right $path) $env))))
      ((IMP $a $b) (ai-math:ind-node IMP
        ((ai-math:ind-named $a $scope (AiInd:Left $path) $env)
         (ai-math:ind-named $b $scope (AiInd:Right $path) $env))))
      ((TPAP $f $ty) (ai-math:ind-node TPAP
        ((ai-math:ind-named $f $scope (AiInd:Left $path) $env) (AiInd:Syntax $ty))))
      ($other (AiInd:Syntax $other)))))
(= (ai-math:ind-named-binder $tag $ty $body $scope $path $env)
   (let $name (AiInd:Name $scope $path)
     (case (ai-math:ind-named $body $scope (AiInd:Left $path) (union-atom $env ($name)))
       (((AiInd:Syntax $value) (AiInd:Syntax ($tag $ty $value $name)))
        ($other $other)))))
(= (ai-math:ind-db $term $env)
   (case $term
     (((VAR $name)
       (let $found (ai-math:ind-variable $name (list:reverse $env) 0)
         (if (== $found AiInd:Free) (AiInd:Request free-variable $term)
           (AiInd:Syntax (DB $found)))))
      ((ALL $ty $body $name) (ai-math:ind-db-binder ALL $ty $body $name $env))
      ((LAM $ty $body $name) (ai-math:ind-db-binder LAM $ty $body $name $env))
      ((AP $f $a) (ai-math:ind-node AP ((ai-math:ind-db $f $env) (ai-math:ind-db $a $env))))
      ((IMP $a $b) (ai-math:ind-node IMP ((ai-math:ind-db $a $env) (ai-math:ind-db $b $env))))
      ((TPAP $f $ty) (ai-math:ind-node TPAP ((ai-math:ind-db $f $env) (AiInd:Syntax $ty))))
      ($other (AiInd:Syntax $other)))))
(= (ai-math:ind-db-binder $tag $ty $body $name $env)
   (ai-math:ind-node $tag ((AiInd:Syntax $ty) (ai-math:ind-db $body (union-atom $env ($name))))))
(= (ai-math:ind-variable $name $env $position)
   (if (== $env ()) AiInd:Free
     (let ($head $rest) (decons-atom $env)
       (if (== $head $name) $position (ai-math:ind-variable $name $rest (+ $position 1))))))

; Names identify source binder occurrences in disjoint goal/principle scopes.
; Substitution respects binder shadowing and retains existing beta redexes.
; Specialization contracts only the newly inserted motive applications.
(= (ai-math:ind-substitute $term $name $value)
   (case $term
     (((VAR $v) (if (== $v $name) $value $term))
      ((ALL $ty $body $v) (if (== $v $name) $term (ALL $ty (ai-math:ind-substitute $body $name $value) $v)))
      ((LAM $ty $body $v) (if (== $v $name) $term (LAM $ty (ai-math:ind-substitute $body $name $value) $v)))
      ((AP $f $a) (AP (ai-math:ind-substitute $f $name $value)
                      (ai-math:ind-substitute $a $name $value)))
      ((IMP $a $b) (IMP (ai-math:ind-substitute $a $name $value) (ai-math:ind-substitute $b $name $value)))
      ((TPAP $f $ty) (TPAP (ai-math:ind-substitute $f $name $value) $ty))
      ($other $other))))
(= (ai-math:ind-instantiate $term $name $motive)
   (case $term
     (((VAR $v) (if (== $v $name) $motive $term))
      ((ALL $ty $body $v)
       (if (== $v $name) $term (ALL $ty (ai-math:ind-instantiate $body $name $motive) $v)))
      ((LAM $ty $body $v)
       (if (== $v $name) $term (LAM $ty (ai-math:ind-instantiate $body $name $motive) $v)))
      ((AP $f $a)
       (let $argument (ai-math:ind-instantiate $a $name $motive)
         (if (== $f (VAR $name)) (ai-math:ind-apply $motive $argument)
           (AP (ai-math:ind-instantiate $f $name $motive) $argument))))
      ((IMP $a $b) (IMP (ai-math:ind-instantiate $a $name $motive) (ai-math:ind-instantiate $b $name $motive)))
      ((TPAP $f $ty) (TPAP (ai-math:ind-instantiate $f $name $motive) $ty))
      ($other $other))))
(= (ai-math:ind-apply $function $argument)
   (case $function
     (((LAM $ty $body $name) (ai-math:ind-substitute $body $name $argument))
      ($other (AP $function $argument)))))
(= (ai-math:ind-prefix $term $prefix)
   (case $term
     (((ALL $ty $body $name) (ai-math:ind-prefix $body (union-atom $prefix ((AiInd:Binder $ty $name)))))
      ((IMP $hyp $body) (ai-math:ind-prefix $body (union-atom $prefix ((AiInd:Hyp $hyp)))))
      ($other (AiInd:Prefix $prefix $term)))))
(= (ai-math:ind-principle $thf $name $cutoff)
   (case (ai-math:thf-lookup $thf Name $name)
     (((AiTHF:Binding $id (AiTHF:Fact $i $kind $n $stmt $ignored-body))
       (if (< $i $cutoff)
         (case (ai-math:ind-named $stmt (Principle $name) AiInd:Root ())
           (((AiInd:Syntax (ALL (AR (SET) (PROP)) $body $motive))
             (ai-math:ind-principle-cases $name $motive $body ()))
            ($other AiInd:NoPrinciple)))
         AiInd:NoPrinciple))
      ($other AiInd:NoPrinciple))))
(= (ai-math:ind-principle-cases $name $motive $term $cases)
   (case $term
     (((IMP $case $rest) (ai-math:ind-principle-cases $name $motive $rest (union-atom $cases ($case))))
      ((ALL (SET) (AP (VAR $p) (VAR $x)) $bound)
       (if (and (== $p $motive) (== $x $bound))
         (AiInd:Principle $name $motive $cases AiInd:NoGuard) AiInd:NoPrinciple))
      ((ALL (SET) (IMP (AP (TMH $hash) (VAR $x)) (AP (VAR $p) (VAR $y))) $bound)
       (if (and (== $p $motive) (and (== $x $bound) (== $y $bound)))
         (AiInd:Principle $name $motive $cases $hash) AiInd:NoPrinciple))
      ($other AiInd:NoPrinciple))))
(= (ai-math:ind-guard $prefix $hash $variable $position)
   (if (== $hash AiInd:NoGuard) AiInd:NoGuard
     (if (== $prefix ()) AiInd:MissingGuard
       (let ($head $rest) (decons-atom $prefix)
         (if (== $head (AiInd:Hyp (AP (TMH $hash) (VAR $variable)))) $position
           (ai-math:ind-guard $rest $hash $variable (+ $position 1)))))))
(= (ai-math:ind-motive $prefix $conclusion $variable $x $guard)
   (let (AiInd:Remaining $count $rest)
     (foldl-atom $prefix (AiInd:Remaining 0 ()) $state $item
       (let (AiInd:Remaining $position $out) $state
         (AiInd:Remaining (+ $position 1)
           (if (or (== $position $x) (== $position $guard)) $out (cons-atom $item $out)))))
     (LAM (SET)
       (foldl-atom $rest $conclusion $body $item
         (case $item
           (((AiInd:Binder $ty $name) (ALL $ty $body $name))
            ((AiInd:Hyp $hyp) (IMP $hyp $body))))) $variable)))
(= (ai-math:ind-splits-for $principle $prefix $conclusion)
   (case $principle
     (((AiInd:Principle $name $motive-name $cases $hash)
       (let (AiInd:Splits $count $out)
         (foldl-atom $prefix (AiInd:Splits 0 ()) $state $item
           (let (AiInd:Splits $position $rows) $state
             (AiInd:Splits (+ $position 1)
               (case $item
                 (((AiInd:Binder (SET) $variable)
                   (let $guard (ai-math:ind-guard $prefix $hash $variable 0)
                     (if (== $guard AiInd:MissingGuard) $rows
                       (let* (($motive (ai-math:ind-motive $prefix $conclusion $variable $position $guard))
                              ($terms (map-atom $cases $case
                                (ai-math:ind-db (ai-math:ind-instantiate $case $motive-name $motive) ()))))
                         (union-atom $rows
                           ((AiInd:Split $name (size-atom $prefix) $position $guard $terms)))))))
                  ($other $rows))))))
         $out))
      ($other ()))))
(= (ai-math:induction-splits $thf $index $statement)
   (case (ai-math:ind-named $statement Goal AiInd:Root ())
     (((AiInd:Syntax $named)
       (let (AiInd:Prefix $prefix $conclusion) (ai-math:ind-prefix $named ())
         (foldl-atom ("nat_ind" "nat_complete_ind" "ordinal_ind" "SNoLev_ind" "finite_ind" "In_ind")
           () $out $name
           (union-atom $out (ai-math:ind-splits-for (ai-math:ind-principle $thf $name $index) $prefix $conclusion)))))
      ($other $other))))

(= (ai-math:ind-intro-names $count)
   (ai-math:ind-intro-names-from 0 $count))
(= (ai-math:ind-intro-names-from $position $count)
   (if (== $position $count) ()
     (cons-atom (str:concat "i" (str:number->string $position))
       (ai-math:ind-intro-names-from (+ $position 1) $count))))
(= (ai-math:induction-prefix (AiInd:Split $name $count $x $guard $cases))
   (let* (($names (ai-math:ind-intro-names $count))
          ((AiInd:Remaining $length $others)
            (foldl-atom $names (AiInd:Remaining 0 ()) $state $variable
              (let (AiInd:Remaining $position $out) $state
                (AiInd:Remaining (+ $position 1)
                  (if (or (== $position $x) (== $position $guard)) $out (union-atom $out ($variable))))))))
     (str:join "\n" (union-atom ((str:concat "intro " (str:join " " $names)))
       (union-atom (if (== $others ()) () ((str:concat "revert " (str:join " " $others))))
         (union-atom (if (== $guard AiInd:NoGuard) () ((str:concat "revert " (index-atom $names $guard))))
           ((str:concat "revert " (index-atom $names $x))
            (str:concat "apply " (ai-math:lean-name $name)))))))))
