
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
      


variable {p : Prop}
variable {q : Prop}
variable {r : Prop}
theorem test_nest : ((p -> q) /\ (q -> r)) -> (p -> r) := by 
  intro ha
  cases ha with
  | intro hl hr => 
    intro hp
    apply hr
    apply hl
    assumption

theorem add0n : (Nat.add n Nat.zero) = n := by
  rewrite[Nat.add.eq_def]
  simp only



  
  
theorem test_demorgans : ¬(p ∧ q) -> ¬p ∨ ¬q := by grind
theorem test_taut2: ((¬a -> b) ∧ (¬a -> ¬b)) -> a := by grind

inductive mnat where
  | msuc : mnat -> mnat
  | mzero : mnat

theorem msuc_injective (x y : mnat) : ((mnat.msuc x) = (mnat.msuc y)) -> x = y := by 
  intro ha
  apply mnat.msuc.inj
  assumption

theorem msuc_injective_rev (x y : mnat) : x = y -> ((mnat.msuc x) = (mnat.msuc y)) := by 
  intro ha
  rewrite [ha]
  rfl








