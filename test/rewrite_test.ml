open Heft
open Derived
open Rewrite
open Printing

let print_match_result r =
  match r with
  | None -> print_endline "None"
  | Some { term_sub; type_sub } ->
      if term_sub = [] && type_sub = [] then
        print_endline "Some { term_sub = []; type_sub = [] }"
      else begin
        if type_sub <> [] then begin
          print_endline "type_sub:";
          type_sub
          |> List.iter (fun (pat, target) ->
              Printf.printf "  %s -> %s\n"
                (pretty_print_hol_type pat)
                (pretty_print_hol_type target))
        end;
        if term_sub <> [] then begin
          print_endline "term_sub:";
          term_sub
          |> List.iter (fun (pat, target) ->
              Printf.printf "  %s -> %s\n"
                (pretty_print_hol_term pat)
                (pretty_print_hol_term target))
        end
      end

let%expect_test "match_term: variable matches any term of same type" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let p = make_var "P" bool_ty in
  let result = match_term x p in
  print_match_result result;
  [%expect {|
    term_sub:
      x -> P |}]

let%expect_test "match_term: variable matches complex term" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let p_and_q = make_conj p q in
  let result = match_term x p_and_q in
  print_match_result result;
  [%expect {|
    term_sub:
      x -> P ∧ Q |}]

let%expect_test "match_term: same variable must match same term" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let p = make_var "P" bool_ty in
  let pattern = make_conj x x in
  let target = make_conj p p in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    term_sub:
      x -> P |}]

let%expect_test "match_term: same variable different terms fails" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let pattern = make_conj x x in
  let target = make_conj p q in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {| None |}]

let%expect_test "match_term: different variables can match different terms" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let y = make_var "y" bool_ty in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let pattern = make_conj x y in
  let target = make_conj p q in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    term_sub:
      y -> Q
      x -> P |}]

let%expect_test "match_term: pattern var same name as target var" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let y = make_var "y" bool_ty in
  let target = make_conj x y in
  let result = match_term x target in
  print_match_result result;
  [%expect {|
    term_sub:
      x -> x ∧ y |}]

(* ===== Type Mismatch ===== *)

let%expect_test "match_term: variable type mismatch fails" =
  let () = reset () |> Result.get_ok in
  let _ = new_type "nat" 0 in
  let nat_ty = TyCon ("nat", []) in
  let x = make_var "x" nat_ty in
  let p = make_var "P" bool_ty in
  let result = match_term x p in
  print_match_result result;
  [%expect {| None |}]

(* ===== Constants ===== *)

let%expect_test "match_term: constant matches same constant" =
  let () = reset () |> Result.get_ok in
  let t = make_true () in
  let result = match_term t t in
  print_match_result result;
  [%expect {| Some { term_sub = []; type_sub = [] } |}]

let%expect_test "match_term: constant doesn't match different constant" =
  let () = reset () |> Result.get_ok in
  let t = make_true () in
  let f = make_false () in
  let result = match_term t f in
  print_match_result result;
  [%expect {| None |}]

(* ===== Application Structure ===== *)

let%expect_test "match_term: application matches structurally" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let p = make_var "P" bool_ty in
  let pattern = make_imp x x in
  let target = make_imp p p in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    term_sub:
      x -> P |}]

let%expect_test "match_term: nested application" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let y = make_var "y" bool_ty in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let pattern = make_imp (make_conj x y) x in
  let target = make_imp (make_conj p q) p in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    term_sub:
      y -> Q
      x -> P |}]

let%expect_test "match_term: structural mismatch fails" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let pattern = make_conj x x in
  let target = make_disj p q in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {| None |}]

let%expect_test "match_term: pattern is more specific than target fails" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let p = make_var "P" bool_ty in
  let pattern = make_conj x x in
  let target = p in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {| None |}]

(* ===== Lambda Matching ===== *)

let%expect_test "match_term: lambda matches with same binder type" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let y = make_var "y" bool_ty in
  let pattern = Lam (x, x) in
  let target = Lam (y, y) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {| Some { term_sub = []; type_sub = [] } |}]

let%expect_test "match_term: lambda with pattern variable in body" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let y = make_var "y" bool_ty in
  let z = make_var "z" bool_ty in
  let p = make_var "P" bool_ty in
  let pattern = Lam (x, make_conj x z) in
  let target = Lam (y, make_conj y p) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    term_sub:
      z -> P |}]

let%expect_test "match_term: lambda binder type mismatch fails" =
  let () = reset () |> Result.get_ok in
  let _ = new_type "nat" 0 in
  let nat_ty = TyCon ("nat", []) in
  let x = make_var "x" bool_ty in
  let y = make_var "y" nat_ty in
  let pattern = Lam (x, x) in
  let target = Lam (y, y) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {| None |}]

let%expect_test "match_term: bound variable must match exactly" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let y = make_var "y" bool_ty in
  let p = make_var "P" bool_ty in
  let pattern = Lam (x, x) in
  let target = Lam (y, p) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {| None |}]

let%expect_test "match_term: nested lambda" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let y = make_var "y" bool_ty in
  let a = make_var "a" bool_ty in
  let b = make_var "b" bool_ty in
  let pattern = Lam (x, Lam (y, make_conj x y)) in
  let target = Lam (a, Lam (b, make_conj a b)) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {| Some { term_sub = []; type_sub = [] } |}]

let%expect_test "match_term: lambda with free and bound vars" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let y = make_var "y" bool_ty in
  let z = make_var "z" bool_ty in
  let a = make_var "a" bool_ty in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  (* Pattern: λx. λy. x /\ y /\ z, free var z *)
  (* Target: λa. λb. a /\ b /\ (P /\ Q) *)
  let b = make_var "b" bool_ty in
  let pattern = Lam (x, Lam (y, make_conj (make_conj x y) z)) in
  let target = Lam (a, Lam (b, make_conj (make_conj a b) (make_conj p q))) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    term_sub:
      z -> P ∧ Q |}]

(* ===== Polymorphic Matching ===== *)

let%expect_test "match_term: polymorphic pattern variable" =
  let () = reset () |> Result.get_ok in
  let alpha = TyVar "a" in
  let x = make_var "x" alpha in
  let p = make_var "P" bool_ty in
  let result = match_term x p in
  print_match_result result;
  [%expect {|
    type_sub:
      a -> bool
    term_sub:
      x -> P |}]

let%expect_test
    "match_term: polymorphic equality fails when var matches different terms" =
  let () = reset () |> Result.get_ok in
  let alpha = TyVar "a" in
  let x = make_var "x" alpha in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let pattern = Result.get_ok (safe_make_eq x x) in
  let target = Result.get_ok (safe_make_eq p q) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {| None |}]

let%expect_test "match_term: polymorphic equality matching" =
  let () = reset () |> Result.get_ok in
  let alpha = TyVar "a" in
  let x = make_var "x" alpha in
  let p = make_var "P" bool_ty in
  let pattern = Result.get_ok (safe_make_eq x x) in
  let target = Result.get_ok (safe_make_eq p p) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    type_sub:
      a -> bool
    term_sub:
      x -> P |}]

let%expect_test "match_term: polymorphic with two type vars" =
  let () = reset () |> Result.get_ok in
  let alpha = TyVar "a" in
  let beta = TyVar "b" in
  let x = make_var "x" alpha in
  let y = make_var "y" beta in
  let p = make_var "P" bool_ty in
  let _ = new_type "nat" 0 in
  let nat_ty = TyCon ("nat", []) in
  let n = make_var "n" nat_ty in
  let result1 = match_term x p in
  let result2 = match_term y n in
  print_match_result result1;
  print_match_result result2;
  [%expect
    {|
    type_sub:
      a -> bool
    term_sub:
      x -> P
    type_sub:
      b -> nat
    term_sub:
      y -> n |}]

let%expect_test "match_term: polymorphic lambda" =
  let () = reset () |> Result.get_ok in
  let alpha = TyVar "a" in
  let x = make_var "x" alpha in
  let y = make_var "y" bool_ty in
  (* Pattern: λx:α. x (polymorphic identity) *)
  (* Target: λy:bool. y *)
  let pattern = Lam (x, x) in
  let target = Lam (y, y) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    type_sub:
      a -> bool |}]

let%expect_test "match_term: polymorphic constant" =
  let () = reset () |> Result.get_ok in
  let alpha = TyVar "a" in
  let x = make_var "x" alpha in
  let y = make_var "y" alpha in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  (* Pattern: x = y (polymorphic equality) *)
  (* Target: P = Q *)
  let pattern = Result.get_ok (safe_make_eq x y) in
  let target = Result.get_ok (safe_make_eq p q) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect
    {|
    type_sub:
      a -> bool
    term_sub:
      y -> Q
      x -> P |}]

(* ===== HOL Constructs ===== *)

let%expect_test "match_term: match against forall" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let y = make_var "y" bool_ty in
  let pat_var = make_var "body" bool_ty in
  let pattern = make_forall x pat_var in
  let target = make_forall y (make_imp y y) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    term_sub:
      body -> y ==> y |}]

let%expect_test "match_term: match forall body structurally" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let y = make_var "y" bool_ty in
  let z = make_var "z" bool_ty in
  let p = make_var "P" bool_ty in
  (* Pattern: ∀x. x ==> z *)
  (* Target: ∀y. y ==> P *)
  let pattern = make_forall x (make_imp x z) in
  let target = make_forall y (make_imp y p) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    term_sub:
      z -> P |}]

let%expect_test "match_term: equality pattern" =
  let () = reset () |> Result.get_ok in
  let l = make_var "l" bool_ty in
  let r = make_var "r" bool_ty in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let pattern = Result.get_ok (safe_make_eq l r) in
  let target = Result.get_ok (safe_make_eq p q) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    term_sub:
      r -> Q
      l -> P |}]

let%expect_test "match_term: negation pattern" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let pattern = make_neg x in
  let target = make_neg (make_conj p q) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    term_sub:
      x -> P ∧ Q |}]

(* ===== Realistic Rewrite Patterns ===== *)

let%expect_test "match_term: nat addition pattern" =
  let () = reset () |> Result.get_ok in
  let _ = new_type "nat" 0 in
  let nat_ty = TyCon ("nat", []) in
  let _ = new_constant "Zero" nat_ty in
  let _ =
    new_constant "plus" (make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty))
  in

  let zero = Const ("Zero", nat_ty) in
  let plus = Const ("plus", make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty)) in
  let n = make_var "n" nat_ty in
  let m = make_var "m" nat_ty in

  (* Pattern: plus Zero n (LHS of 0 + n = n) *)
  let pattern = App (App (plus, zero), n) in
  (* Target: plus Zero (plus Zero m) *)
  let target = App (App (plus, zero), App (App (plus, zero), m)) in

  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    term_sub:
      n -> plus Zero m |}]

let%expect_test "match_term: list append pattern" =
  let () = reset () |> Result.get_ok in
  let alpha = TyVar "a" in
  let list_ty = TyCon ("list", [ alpha ]) in
  let _ = new_type "list" 1 in
  let _ = new_constant "Nil" list_ty in
  let _ =
    new_constant "append" (make_fun_ty list_ty (make_fun_ty list_ty list_ty))
  in

  let nil = Const ("Nil", list_ty) in
  let append =
    Const ("append", make_fun_ty list_ty (make_fun_ty list_ty list_ty))
  in
  let xs = make_var "xs" list_ty in

  (* Pattern: append Nil xs (LHS of append Nil xs = xs) *)
  let pattern = App (App (append, nil), xs) in

  (* Target: append Nil (some list term) - using nil for simplicity *)
  let target = App (App (append, nil), nil) in

  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    type_sub:
      a -> a
    term_sub:
      xs -> Nil
    |}]

let%expect_test "match_term: list append with concrete type" =
  let () = reset () |> Result.get_ok in
  let _ = new_type "nat" 0 in
  let nat_ty = TyCon ("nat", []) in
  let alpha = TyVar "a" in
  let list_alpha = TyCon ("list", [ alpha ]) in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let _ = new_type "list" 1 in
  let _ = new_constant "Nil" list_alpha in
  let _ =
    new_constant "append"
      (make_fun_ty list_alpha (make_fun_ty list_alpha list_alpha))
  in

  (* Polymorphic pattern *)
  let nil_poly = Const ("Nil", list_alpha) in
  let append_poly =
    Const ("append", make_fun_ty list_alpha (make_fun_ty list_alpha list_alpha))
  in
  let xs = make_var "xs" list_alpha in
  let pattern = App (App (append_poly, nil_poly), xs) in

  (* Concrete target with nat list *)
  let nil_nat = Const ("Nil", list_nat) in
  let append_nat =
    Const ("append", make_fun_ty list_nat (make_fun_ty list_nat list_nat))
  in
  let target = App (App (append_nat, nil_nat), nil_nat) in

  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    type_sub:
      a -> nat
    term_sub:
      xs -> Nil |}]

(* ===== Edge Cases ===== *)

let%expect_test "match_term: empty pattern (just a var) against complex term" =
  let () = reset () |> Result.get_ok in
  let x = make_var "x" bool_ty in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let complex = make_imp (make_conj p q) (make_disj q r) in
  let result = match_term x complex in
  print_match_result result;
  [%expect {|
    term_sub:
      x -> P ∧ Q ==> Q ∨ R |}]

let%expect_test "match_term: deeply nested matching" =
  let () = reset () |> Result.get_ok in
  let a = make_var "a" bool_ty in
  let b = make_var "b" bool_ty in
  let c = make_var "c" bool_ty in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  (* Pattern: (a /\ b) ==> (b /\ c) *)
  (* Target: (P /\ Q) ==> (Q /\ R) *)
  (* Note: b must match Q in both places *)
  let pattern = make_imp (make_conj a b) (make_conj b c) in
  let target = make_imp (make_conj p q) (make_conj q r) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {|
    term_sub:
      c -> R
      b -> Q
      a -> P |}]

let%expect_test "match_term: deeply nested matching fails with inconsistency" =
  let () = reset () |> Result.get_ok in
  let a = make_var "a" bool_ty in
  let b = make_var "b" bool_ty in
  let c = make_var "c" bool_ty in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  (* Pattern: (a /\ b) ==> (b /\ c) *)
  (* Target: (P /\ Q) ==> (R /\ R) *)
  (* b would need to match both Q and R - fails *)
  let pattern = make_imp (make_conj a b) (make_conj b c) in
  let target = make_imp (make_conj p q) (make_conj r r) in
  let result = match_term pattern target in
  print_match_result result;
  [%expect {| None |}]

let%expect_test
    "match_term: type variable used multiple times must be consistent" =
  let () = reset () |> Result.get_ok in
  let alpha = TyVar "a" in
  let x = make_var "x" alpha in
  let p = make_var "P" bool_ty in
  let _ = new_type "nat" 0 in
  let result1 = match_term x p in
  print_match_result result1;
  (* Now if we tried to match y against n in the same env, it would fail *)
  (* because alpha is already bound to bool *)
  [%expect {|
    type_sub:
      a -> bool
    term_sub:
      x -> P |}]
