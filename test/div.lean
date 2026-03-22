
  /- def div_aux : nat -> nat -> nat -> option nat -/
  /-     | zero => λa. λb. none -/
  /-     | suc n => λa. λb. -/
  /-         COND (nat_le b (suc a)) -/
  /-              (option_match (div_aux n (sub a b) b) -/
  /-                 none -/
  /-                 (λr. some (suc r))) -/
  /-              (some zero) -/

variable { m n : Nat }

def div_fuel : Nat -> Nat -> Nat -> Option Nat :=
  λfuel => 
    match fuel with
    | .zero => λ_ _ => .none
    | .succ n => λa b => 
      if b <= (.succ a) 
      then 
        match (div_fuel n (a - b) b) with
        | .none => .none
        | .some r => .some (.succ r)
      else 
        .some .zero

  /- theorem fuel_irrel: -/
  /-   forall λn. forall λm. forall λa. forall λb. forall λx. -/
  /-       imp (eq (div_aux n a b) (some x)) -/
  /-           (eq (div_aux (plus n m) a b) (some x)) -/

theorem fuel_irrel (n m a b x : Nat) :  
  div_fuel n a b = some x -> div_fuel (n + m) a b = some x
  := by
    induction ih : n with
    | zero  => 
      intro h1
      sorry
    | succ n' => sorry

