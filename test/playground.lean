
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

def mnat_plus (m n : mnat) :=
  match m with
  | mnat.mzero => n
  | mnat.msuc m' => mnat.msuc (mnat_plus m' n)


theorem mnat_n_zero (x : mnat) : mnat_plus mnat.mzero x = x := by 
  simp [mnat_plus]

theorem mnat_zero_n (x : mnat) : mnat_plus x mnat.mzero = x := by 
  induction x 
  simp [mnat_plus]
  assumption
  simp [mnat_plus]
  

  /- (* plus y x = plus z x -> y = z *) -/
theorem mnat_cancel (x y z : Nat) : y + x = z + x -> y = z := by
  induction hx: x with
  | zero => 
    intro ha
    rewrite [Nat.add_zero] at ha
    rewrite [Nat.add_zero] at ha
    assumption

  | succ m' ih => 
    intro hp
    grind

