open Heft
open Tactic

let () = print_endline "initializing theory bools"

let%def eqb (a : bool) (b : bool) : bool =
  if a then if b then true else false else if b then false else true

let%def andb (a : bool) (b : bool) : bool =
  if a then if b then true else false else if b then false else false

[@@@ocamlformat "disable"]
let%thm eq_true_intro (p : bool) = p ==> (p = true)
and proof =
  begin
    intros >> eq_true_elim >> assumption
  end [@quiet]

(* Just an alias that uses the lower level axiom *)
let%thm axiom_of_choice (p : 'a -> bool) =
  exists (fun (x : 'a) -> p x) ==> p (choose (fun (y : 'a) -> p y))

and proof =
  begin
    with_first (with_axioms exact)
  end
  [@quiet]


let%thm false_or_false = (false || false) = false

and proof =
  begin
    noop >> eq_false_elim >> neg_intro >> elim_disj_asm @>> assumption
  end
  [@quiet]
  [@simp]

let%thm refl_eq_true (x : 'a) = x = x = true

and proof =
  begin
    noop >> intros >> eq_true_elim >> refl
  end
  [@quiet]

let%thm true_or_false = (true || false) = true

and proof =
  begin
    noop >> eq_true_elim >> left >> truth
  end
  [@quiet]
  [@simp]


let%thm neg_eq_false (p : bool) = p = false = not p

and proof =
  begin
    noop >> intros
    >> with_rule (Derived.neg_def |> Result.get_ok) rewrite
    >> beta
    >> eq_iff @: [ "himp"; "heq" ]
    >> eq_false_elim
    >> with_rule (Derived.neg_def |> Result.get_ok) rewrite
    >> beta >> assumption >> rewrite_at "heq" >> intros >> false_elim
  end
  [@quiet]

let%thm demorgons_eq_false (p : bool) (q : bool) =
  (p || q) = false ==> ((not p) && not q)

and proof =
  begin
    noop >> intros @! "heq"
    >> rewrite_at "neg_eq_false" ~target:"heq"
    >> with_no_automation_trace Auto.ctauto_dfs
  end
  [@quiet]


let%thm bool_cases (p : bool) = 
    p = true || p = false
and proof = begin
    with_rule (Derived.bool_cases )exact
end
[@quiet]
