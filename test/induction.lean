
theorem rev_rev_idemp : List.reverse (List.reverse l) = l := by
  induction l  with
  | nil => sorry
  | cons x xs => sorry

variable {a : Prop}
theorem test_a (n : Nat) : ∀ (n:Nat), a -> a := by
  induction n with
  | zero => 
      intro
      intro
      assumption
  | succ _ =>
      intro
      intro
      assumption
      


