import Bridge

/- A proof-producing closing tactic for untrusted sketches. It either
   closes the selected goal or fails; it never creates an admission. -/
syntax (name := aiMathAuto) "ai_math_auto" "["
  (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]" : tactic

macro_rules
  | `(tactic| ai_math_auto [$definitions,*]) =>
    `(tactic| first
      | (intros
         try simp only [Megalodon.b_True, Megalodon.b_False, Megalodon.b_not,
           Megalodon.b_and, Megalodon.b_or, Megalodon.b_iff, Megalodon.b_eq,
           Megalodon.b_neq, Megalodon.b_ex] at *
         grind
         done)
      | (intros
         try simp only [Megalodon.b_True, Megalodon.b_False, Megalodon.b_not,
           Megalodon.b_and, Megalodon.b_or, Megalodon.b_iff, Megalodon.b_eq,
           Megalodon.b_neq, Megalodon.b_ex, $definitions,*] at *
         grind
         done)
      | (intros
         solve_by_elim (maxDepth := 8)
         done))
