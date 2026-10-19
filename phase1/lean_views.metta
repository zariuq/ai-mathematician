; Vocabulary categories are presentation heuristics, not mathematical
; partitions. Every view includes its full named dependency closure.

(= (ai-math:lean-tiers) ("prop_logic" "set_theory" "nat_arith" "ordinals" "surreals"))
(= (ai-math:lean-classifiers)
   (map-atom
     (("surreals" "\\b(SNo\\w*|PNo\\w*|PSNo|eps_\\w*|SurrealRec\\w*|abs_SNo|minus_SNo|add_SNo|mul_SNo|div_SNo|recip_SNo|exp_SNo\\w*|real|rational|diadic\\w*|int|int_lin_comb|divides_int|gcd_reln|nonincrfinseq|Pi_SNo|tag)\\b")
      ("ordinals" "\\b(ordinal\\w*|TransSet|ZF_closed|\\w*_closed)\\b")
      ("nat_arith" "\\b(nat_p|nat_\\w*|\\w*_nat|omega|ordsucc\\w*|Pi_nat|primes|prime_nat|composite_nat|nat_pair|nat_primrec|NatRec\\w*)\\b")
      ("set_theory" "\\b(In|Subq|Empty|Union|Power|Repl|UnivOf|binunion|binintersect|setminus|Sing|UPair|Sep|famunion|ReplSep|Sigma|setsum|setprod|setexp|proj0|proj1|Inj0|Inj1|Unj|pair\\w*|equip|atleastp|inj|surj|bij|inv|finite|infinite|Eps_i\\w*|Descr\\w*|If_i\\w*|In_rec\\w*|In_ind|set_ext|Vo)\\b|:e|c=")
      ("prop_logic" "\\b(and\\w*|or\\w*|not\\w*|iff\\w*|True|False|ex|exactly1of\\w*|xm|dneg|prop_ext\\w*|pred_ext|demorgan|FalseE)\\b|/\\\\|\\\\/|<->|~")
      ("nat_arith" "\\b\\d+\\b"))
     $rule (let ($tier $text) $rule ($tier (re:prepare (re:pattern $text))))))
(= (ai-math:lean-classify $classifiers $text)
   (if (== $classifiers ()) "prop_logic"
     (let (($tier $pattern) $rest) (decons-atom $classifiers)
       (case (re:find $pattern $text)
         (((re:match $start $end $groups) $tier)
          (re:no-match (ai-math:lean-classify $rest $text))
          ($other (AiLean:Request category-interpretation $other)))))))
(= (ai-math:lean-closure $index $needed $work)
   (if (== $work ()) $needed
     (let ($name $rest) (decons-atom $work)
       (if (ai-math:get $needed $name false) (ai-math:lean-closure $index $needed $rest)
         (case (ai-math:get $index $name AiLean:Missing)
           (((AiLean:Entry $kind $n $text $deps)
             (let $marked (ai-math:put $needed $name true)
               (ai-math:lean-closure $index $needed (union-atom $deps $rest))))
            ($other (AiLean:Request missing-dependency $name))))))))
(= (ai-math:lean-view $entries $index $categories $tier)
   (let* (($own (map-atom (filter-atom $categories $row (== (index-atom $row 1) $tier))
                  $row (index-atom $row 0)))
          ($needed (ai-math:lean-closure $index (new-space) $own)))
     (case $needed
       (((AiLean:Request $why $detail) $needed)
        ($space (AiLean:View $tier (AiLean:Entries (filter-atom $entries $entry
                   (ai-math:get $space (index-atom $entry 2) false)))))))))
(= (ai-math:lean-views $export)
   (case $export
     (((AiLean:Entries $entries)
       (let* (($index (new-space))
              ($indexed (map-atom $entries $entry (ai-math:put $index (index-atom $entry 2) $entry)))
              ($classifiers (ai-math:lean-classifiers))
              ($categories (map-atom (filter-atom $entries $entry (== (index-atom $entry 1) THM)) $entry
                ((index-atom $entry 2) (ai-math:lean-classify $classifiers
                  (str:join " " ((index-atom $entry 2) (index-atom $entry 3)
                    (str:join " " (index-atom $entry 4))))))))
              ($invalid (filter-atom $categories $row (not (== (get-type (index-atom $row 1)) String)))))
         (if (== $invalid ())
           (AiLean:Views (map-atom (ai-math:lean-tiers) $tier
             (ai-math:lean-view $entries $index $categories $tier)))
           (AiLean:Request category-interpretation $invalid))))
      ($other $other))))
