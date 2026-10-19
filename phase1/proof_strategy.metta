; Pure tactic proposals and checked-result classification shared by
; direct reconstruction and induction. Import after the ATP and ITP APIs.

; Candidate builders are pure: labels and tactic bodies are ordinary data.
; List order is significant here: it decides which accepted proposal wins.
(= (ai-math:lean-name $name) (str:concat "«" (str:concat $name "»")))
(= (ai-math:lean-names $names)
   (map-atom $names $name (ai-math:lean-name $name)))
(= (ai-math:prover-bridge)
   "b_True, b_False, b_not, b_and, b_or, b_iff, b_eq, b_neq, b_ex")
(= (ai-math:prover-big) "(splits := 24) (ematch := 12) (gen := 12)")
(= (ai-math:prover-haves $premises)
   (let (AiProver:Haves $count $parts)
     (foldl-atom $premises (AiProver:Haves 0 ()) $state $name
       (let (AiProver:Haves $i $parts) $state
         (AiProver:Haves (+ $i 1) (cons-atom
           (str:join "" ("have hp" (str:number->string $i) " := @" $name "\n")) $parts))))
     (str:join "" (list:reverse $parts))))
(= (ai-math:prover-unfold $definitions)
   (str:join ", " (cons-atom (ai-math:prover-bridge) $definitions)))
(= (ai-math:prover-goal-unfold $definitions)
   (if (== $definitions ()) ""
     (str:join "" ("try simp only [" (str:join ", " $definitions)
       "]\ntry intros\ntry simp only [" (ai-math:prover-bridge) "] at *\n"))))

(= (ai-math:candidate-tactics $premises $definitions)
   (ai-math:candidate-tactics $premises $definitions $definitions))
(= (ai-math:candidate-tactics $premises $definitions $goal-definitions)
   (let* (($p (ai-math:lean-names $premises))
          ($g (ai-math:lean-names $goal-definitions))
          ($h (ai-math:prover-haves $p)) ($b (ai-math:prover-bridge))
          ($u (ai-math:prover-unfold (ai-math:lean-names $definitions)))
          ($gu (ai-math:prover-goal-unfold $g)))
     (union-atom
       ((AiITP:Candidate "intro-grind" (str:join "" ("intros\ntry simp only [" $b "] at *\ngrind")))
        (AiITP:Candidate "unfold-grind" (str:join "" ("intros\ntry simp only [" $u "] at *\ngrind"))))
       (union-atom
         (if (== $p ()) ()
           (union-atom
             ((AiITP:Candidate "prem-grind" (str:join "" ("intros\n" $h "try simp only [" $b "] at *\ngrind")))
              (AiITP:Candidate "prem-unfold-grind" (str:join "" ("intros\n" $h "try simp only [" $u "] at *\ngrind")))
              (AiITP:Candidate "solve_by_elim" (str:join "" ("intros\nsolve_by_elim (maxDepth := 8) [" (str:join ", " $p) "]"))))
             (if (== $g ()) ()
               ((AiITP:Candidate "goal-unfold-grind" (str:join "" ("intros\n" $h "try simp only [" $b "] at *\n" $gu "grind")))
                (AiITP:Candidate "goal-unfold-sbe" (str:join "" ("intros\n" $gu "solve_by_elim (maxDepth := 10) [" (str:join ", " $p) "]")))))))
         ((AiITP:Candidate "ext-grind" (str:join "" ("intros\n" $h "try simp only [" $b "] at *\n"
           "refine (b_eq set _ _).mp (set_ext _ _ ?_ ?_)\n"
           "all_goals ((try simp only [Subq]); intros; (try simp only [" $b "] at *); grind)"))))))))

(= (ai-math:followup-tactics $premises $definitions $goal-definitions)
   (let* (($p (ai-math:lean-names $premises)) ($g (ai-math:lean-names $goal-definitions))
          ($h (ai-math:prover-haves $p)) ($b (ai-math:prover-bridge))
          ($u (ai-math:prover-unfold (ai-math:lean-names $definitions)))
          ($big (ai-math:prover-big)))
     (union-atom
       (if (== $p ()) ()
         ((AiITP:Candidate "grind-lemmas" (str:join "" ("intros\n(try simp only [" $b "] at *)\ngrind [" (str:join ", " $p) "]")))
          (AiITP:Candidate "grind-lemmas-unfold" (str:join "" ("intros\n(try simp only [" $u "] at *)\ngrind [" (str:join ", " $p) "]")))
          (AiITP:Candidate "prem-grind-big" (str:join "" ("intros\n" $h "(try simp only [" $b "] at *)\nall_goals grind " $big)))
          (AiITP:Candidate "prem-unfold-grind-big" (str:join "" ("intros\n" $h "(try simp only [" $u "] at *)\nall_goals grind " $big)))
          (AiITP:Candidate "simp_all-prem" (str:join "" ("intros\n" $h "simp_all [" $u "]")))
          (AiITP:Candidate "prem-grind-ag" (str:join "" ("intros\n" $h "(try simp only [" $b "] at *)\nall_goals grind")))
          (AiITP:Candidate "prem-unfold-grind-ag" (str:join "" ("intros\n" $h "(try simp only [" $u "] at *)\nall_goals grind")))))
       (union-atom
         ((AiITP:Candidate "unfold-grind-big" (str:join "" ("intros\n(try simp only [" $u "] at *)\nall_goals grind " $big)))
          (AiITP:Candidate "unfold-grind-ag" (str:join "" ("intros\n(try simp only [" $u "] at *)\nall_goals grind"))))
         (if (== $g ()) ()
           ((AiITP:Candidate "goal-unfold-grind-big" (str:join "" ("intros\n" $h "(try simp only [" $b "] at *)\n"
             "(try simp only [" (str:join ", " $g) "])\n(try intros)\n(try simp only [" $b "] at *)\nall_goals grind " $big)))))))))

(= (ai-math:apply-tactics $premises $definitions)
   (let* (($p (ai-math:lean-names $premises)) ($h (ai-math:prover-haves $p))
          ($b (ai-math:prover-bridge)) ($u (ai-math:prover-unfold (ai-math:lean-names $definitions))))
     (let (AiProver:Apply $count $rows)
       (foldl-atom $p (AiProver:Apply 0 ()) $state $name
         (let* (((AiProver:Apply $i $rows) $state)
                ($prefix (str:join "" ("intros\n" $h "(try simp only [" $b "] at *)\napply hp" (str:number->string $i) "\n"))))
           (AiProver:Apply (+ $i 1) (union-atom $rows
             (map-atom (("" $b) ("-unfold" $u)) $variant
               (let ($tag $unfold) $variant
                 (AiITP:Candidate (str:join "" ("apply" $tag "-" (str:number->string $i)))
                   (str:join "" ($prefix "all_goals ((try intros); (try simp only [" $unfold "] at *); grind)")))))))))
       $rows)))

(= (ai-math:duper-tactics $premises $definitions)
   (let* (($haves (ai-math:prover-haves (ai-math:lean-names $premises)))
          ($bridge (ai-math:prover-bridge))
          ($unfold (ai-math:prover-unfold (ai-math:lean-names $definitions))))
     ((AiITP:Candidate "duper" (str:join "" ("intros\n" $haves "(try simp only [" $bridge "] at *)\nduper [*]")))
      (AiITP:Candidate "duper-unfold" (str:join "" ("intros\n" $haves "(try simp only [" $unfold "] at *)\nduper [*]"))))))

(= (ai-math:prover-goal-defs $thf $goal)
   (sort-atom (filter-atom (ai-math:declaration-symbols $goal) $name
     (if (ai-math:contains (ai-math:logical-vocabulary) $name) false
       (case (ai-math:thf-lookup $thf Name $name)
         (((AiTHF:Binding $id (AiTHF:Fact $i DEF $n $s $b)) true) ($other false)))))))


(= (ai-math:prover-winner $attempts)
   (if (== $attempts ()) AiProver:NoWinner
     (let ($head $rest) (decons-atom $attempts)
       (case $head
         (((AiProver:Attempt $stage $ordinal $label $script (AiITP:Accepted $target $used $axioms))
           (AiProver:Proved $stage $ordinal $label $script $used $axioms))
          ($other (ai-math:prover-winner $rest)))))))

(= (ai-math:prover-outcome $attempts $stages)
   (let* (($faults (filter-atom $attempts $attempt
                    (case $attempt
                      (((AiProver:StageFault $stage (AiITP:Unfinished $n $r $d)) false)
                       ((AiProver:StageFault $stage $detail) true)
                       ((AiProver:Attempt $s $i $l $t (AiITP:Fault $n $r $d)) true) ($other false)))))
          ($unfinished (filter-atom $attempts $attempt
                        (case $attempt
                          (((AiProver:Attempt $s $i $l $t (AiITP:Unfinished $n $r $d)) true)
                           ((AiProver:StageFault $s (AiITP:Unfinished $n $r $d)) true) ($other false))))))
     (if (not (== $faults ())) (AiProver:Faulted $faults)
       (if (not (== $unfinished ())) (AiProver:Unfinished $unfinished)
         (AiProver:NotProved (AiProver:Coverage $stages))))))
