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

let%expect_test "matching subterms" =
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

(* ===== Rewriting Tests ===== *)

let print_thm_result r =
  match r with
  | Error e -> print_endline ("Error: " ^ Heft.show_kernel_error e)
  | Ok th -> print_endline (pretty_print_thm th)

let%expect_test "rewrite_once: rewrite at root" =
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

  (* Rule: plus Zero n = n (as axiom for testing) *)
  let lhs = App (App (plus, zero), n) in
  let rule = Result.get_ok (safe_make_eq lhs n) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: plus Zero Zero *)
  let target = App (App (plus, zero), zero) in

  let result = rewrite_once rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    plus Zero Zero = Zero
    |}]

let%expect_test "rewrite_once: rewrite in argument position" =
  let () = reset () |> Result.get_ok in
  let _ = new_type "nat" 0 in
  let nat_ty = TyCon ("nat", []) in
  let _ = new_constant "Zero" nat_ty in
  let _ = new_constant "Suc" (make_fun_ty nat_ty nat_ty) in
  let _ =
    new_constant "plus" (make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty))
  in

  let zero = Const ("Zero", nat_ty) in
  let suc = Const ("Suc", make_fun_ty nat_ty nat_ty) in
  let plus = Const ("plus", make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty)) in
  let n = make_var "n" nat_ty in

  (* Rule: plus Zero n = n *)
  let rule_lhs = App (App (plus, zero), n) in
  let rule = Result.get_ok (safe_make_eq rule_lhs n) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: Suc (plus Zero Zero) - rewrite should happen in argument *)
  let target = App (suc, App (App (plus, zero), zero)) in

  let result = rewrite_once rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    Suc (plus Zero Zero) = Suc Zero
    |}]

let%expect_test "rewrite_once: rewrite in nested argument" =
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

  (* Rule: plus Zero n = n *)
  let rule_lhs = App (App (plus, zero), n) in
  let rule = Result.get_ok (safe_make_eq rule_lhs n) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: plus (plus Zero Zero) m - rewrite should happen in first arg *)
  let target = App (App (plus, App (App (plus, zero), zero)), m) in

  let result = rewrite_once rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    plus (plus Zero Zero) m = plus Zero m
    |}]

let%expect_test "rewrite_once: no match returns error" =
  let () = reset () |> Result.get_ok in
  let _ = new_type "nat" 0 in
  let nat_ty = TyCon ("nat", []) in
  let _ = new_constant "Zero" nat_ty in
  let _ = new_constant "One" nat_ty in
  let _ =
    new_constant "plus" (make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty))
  in

  let zero = Const ("Zero", nat_ty) in
  let one = Const ("One", nat_ty) in
  let plus = Const ("plus", make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty)) in
  let n = make_var "n" nat_ty in

  (* Rule: plus Zero n = n *)
  let rule_lhs = App (App (plus, zero), n) in
  let rule = Result.get_ok (safe_make_eq rule_lhs n) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: plus One One - doesn't match *)
  let target = App (App (plus, one), one) in

  let result = rewrite_once rule_thm target in
  (match result with
  | Error `NoRewriteMatch -> print_endline "NoRewriteMatch"
  | _ -> print_endline "unexpected");
  [%expect {| NoRewriteMatch |}]

let%expect_test "rewrite_all: repeatedly rewrites" =
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

  (* Rule: plus Zero n = n *)
  let rule_lhs = App (App (plus, zero), n) in
  let rule = Result.get_ok (safe_make_eq rule_lhs n) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: plus Zero (plus Zero (plus Zero Zero)) *)
  let inner = App (App (plus, zero), zero) in
  let middle = App (App (plus, zero), inner) in
  let target = App (App (plus, zero), middle) in

  let result = rewrite_all rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    plus Zero (plus Zero (plus Zero Zero)) = Zero
    |}]

let%expect_test "rewrite_all: no rewrites returns reflexivity" =
  let () = reset () |> Result.get_ok in
  let _ = new_type "nat" 0 in
  let nat_ty = TyCon ("nat", []) in
  let _ = new_constant "Zero" nat_ty in
  let _ = new_constant "One" nat_ty in
  let _ =
    new_constant "plus" (make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty))
  in

  let zero = Const ("Zero", nat_ty) in
  let one = Const ("One", nat_ty) in
  let plus = Const ("plus", make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty)) in
  let n = make_var "n" nat_ty in

  (* Rule: plus Zero n = n *)
  let rule_lhs = App (App (plus, zero), n) in
  let rule = Result.get_ok (safe_make_eq rule_lhs n) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: One - no match, should return One = One *)
  let result = rewrite_all rule_thm one in
  print_thm_result result;
  [%expect {|
    ========================================
    One = One
    |}]

(* ===== Polymorphic List Rewriting Tests ===== *)

(* Helper to set up polymorphic list environment *)
let setup_list_env () =
  let () = reset () |> Result.get_ok in
  let _ = new_type "list" 1 in
  let alpha = TyVar "a" in
  let list_alpha = TyCon ("list", [ alpha ]) in
  (* Nil : list a *)
  let _ = new_constant "Nil" list_alpha in
  (* Cons : a -> list a -> list a *)
  let cons_ty = make_fun_ty alpha (make_fun_ty list_alpha list_alpha) in
  let _ = new_constant "Cons" cons_ty in
  (* append : list a -> list a -> list a *)
  let append_ty = make_fun_ty list_alpha (make_fun_ty list_alpha list_alpha) in
  let _ = new_constant "append" append_ty in
  (* rev : list a -> list a *)
  let rev_ty = make_fun_ty list_alpha list_alpha in
  let _ = new_constant "rev" rev_ty in
  (* map : (a -> b) -> list a -> list b *)
  let beta = TyVar "b" in
  let list_beta = TyCon ("list", [ beta ]) in
  let map_ty =
    make_fun_ty (make_fun_ty alpha beta) (make_fun_ty list_alpha list_beta)
  in
  let _ = new_constant "map" map_ty in
  ()

let%expect_test "rewrite_once: polymorphic append Nil xs = xs" =
  setup_list_env ();
  let alpha = TyVar "a" in
  let list_alpha = TyCon ("list", [ alpha ]) in
  let nil = Const ("Nil", list_alpha) in
  let append =
    Const ("append", make_fun_ty list_alpha (make_fun_ty list_alpha list_alpha))
  in
  let xs = make_var "xs" list_alpha in

  (* Rule: append Nil xs = xs *)
  let rule_lhs = App (App (append, nil), xs) in
  let rule = Result.get_ok (safe_make_eq rule_lhs xs) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: append Nil Nil (both at type a) *)
  let target = App (App (append, nil), nil) in

  let result = rewrite_once rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    append Nil Nil = Nil
    |}]

let%expect_test "rewrite_once: polymorphic rule applied to concrete type" =
  setup_list_env ();
  let _ = new_type "nat" 0 in
  let nat_ty = TyCon ("nat", []) in
  let _ = new_constant "Zero" nat_ty in

  let alpha = TyVar "a" in
  let list_alpha = TyCon ("list", [ alpha ]) in
  let list_nat = TyCon ("list", [ nat_ty ]) in

  (* Polymorphic rule constants *)
  let nil_poly = Const ("Nil", list_alpha) in
  let append_poly =
    Const ("append", make_fun_ty list_alpha (make_fun_ty list_alpha list_alpha))
  in
  let xs = make_var "xs" list_alpha in

  (* Rule: append Nil xs = xs (polymorphic) *)
  let rule_lhs = App (App (append_poly, nil_poly), xs) in
  let rule = Result.get_ok (safe_make_eq rule_lhs xs) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target at concrete type: append Nil [Zero] where [Zero] = Cons Zero Nil *)
  let nil_nat = Const ("Nil", list_nat) in
  let cons_nat =
    Const ("Cons", make_fun_ty nat_ty (make_fun_ty list_nat list_nat))
  in
  let zero = Const ("Zero", nat_ty) in
  let append_nat =
    Const ("append", make_fun_ty list_nat (make_fun_ty list_nat list_nat))
  in
  let list_with_zero = App (App (cons_nat, zero), nil_nat) in
  let target = App (App (append_nat, nil_nat), list_with_zero) in

  let result = rewrite_once rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    append Nil (Cons Zero Nil) = Cons Zero Nil
    |}]

let%expect_test "rewrite_once: nested list append" =
  setup_list_env ();
  let alpha = TyVar "a" in
  let list_alpha = TyCon ("list", [ alpha ]) in
  let nil = Const ("Nil", list_alpha) in
  let append =
    Const ("append", make_fun_ty list_alpha (make_fun_ty list_alpha list_alpha))
  in
  let xs = make_var "xs" list_alpha in
  let ys = make_var "ys" list_alpha in

  (* Rule: append Nil xs = xs *)
  let rule_lhs = App (App (append, nil), xs) in
  let rule = Result.get_ok (safe_make_eq rule_lhs xs) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: append (append Nil xs) ys - should rewrite inner append *)
  let inner = App (App (append, nil), xs) in
  let target = App (App (append, inner), ys) in

  let result = rewrite_once rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    append (append Nil xs) ys = append xs ys
    |}]

let%expect_test "rewrite_all: multiple append Nil rewrites" =
  setup_list_env ();
  let alpha = TyVar "a" in
  let list_alpha = TyCon ("list", [ alpha ]) in
  let nil = Const ("Nil", list_alpha) in
  let append =
    Const ("append", make_fun_ty list_alpha (make_fun_ty list_alpha list_alpha))
  in
  let xs = make_var "xs" list_alpha in

  (* Rule: append Nil xs = xs *)
  let rule_lhs = App (App (append, nil), xs) in
  let rule = Result.get_ok (safe_make_eq rule_lhs xs) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: append Nil (append Nil (append Nil Nil)) *)
  let inner = App (App (append, nil), nil) in
  let middle = App (App (append, nil), inner) in
  let target = App (App (append, nil), middle) in

  let result = rewrite_all rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    append Nil (append Nil (append Nil Nil)) = Nil
    |}]

let%expect_test "rewrite_once: rev (rev xs) = xs" =
  setup_list_env ();
  let alpha = TyVar "a" in
  let list_alpha = TyCon ("list", [ alpha ]) in
  let rev = Const ("rev", make_fun_ty list_alpha list_alpha) in
  let xs = make_var "xs" list_alpha in
  let ys = make_var "ys" list_alpha in

  (* Rule: rev (rev xs) = xs *)
  let rule_lhs = App (rev, App (rev, xs)) in
  let rule = Result.get_ok (safe_make_eq rule_lhs xs) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: rev (rev ys) *)
  let target = App (rev, App (rev, ys)) in

  let result = rewrite_once rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    rev (rev ys) = ys
    |}]

let%expect_test "rewrite_once: map id xs = xs" =
  setup_list_env ();
  let alpha = TyVar "a" in
  let list_alpha = TyCon ("list", [ alpha ]) in
  let map_ty =
    make_fun_ty (make_fun_ty alpha alpha) (make_fun_ty list_alpha list_alpha)
  in
  let map = Const ("map", map_ty) in
  let xs = make_var "xs" list_alpha in
  let x = make_var "x" alpha in
  let id = Lam (x, x) in

  (* Rule: map (λx. x) xs = xs *)
  let rule_lhs = App (App (map, id), xs) in
  let rule = Result.get_ok (safe_make_eq rule_lhs xs) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: map (λy. y) ys *)
  let ys = make_var "ys" list_alpha in
  let y = make_var "y" alpha in
  let id2 = Lam (y, y) in
  let target = App (App (map, id2), ys) in

  let result = rewrite_once rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    map (λx. x) ys = ys
    |}]

(* ===== Rewriting Under Lambdas ===== *)

let%expect_test "rewrite_once: rewrite under lambda" =
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
  let x = make_var "x" nat_ty in

  (* Rule: plus Zero n = n *)
  let rule_lhs = App (App (plus, zero), n) in
  let rule = Result.get_ok (safe_make_eq rule_lhs n) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: λx. plus Zero x - should rewrite body *)
  let target = Lam (x, App (App (plus, zero), x)) in

  let result = rewrite_once rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    (λx. plus Zero x) = (λx. x)
    |}]

let%expect_test "rewrite_once: rewrite deeply under nested lambdas" =
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
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in

  (* Rule: plus Zero n = n *)
  let rule_lhs = App (App (plus, zero), n) in
  let rule = Result.get_ok (safe_make_eq rule_lhs n) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: λx. λy. plus Zero (plus x y) *)
  let body = App (App (plus, zero), App (App (plus, x), y)) in
  let target = Lam (x, Lam (y, body)) in

  let result = rewrite_once rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    (λx. λy. plus Zero (plus x y)) = (λx. λy. plus x y)
    |}]

(* ===== Multiple Rules ===== *)

let%expect_test "rewrite_once_with_rules: tries rules in order" =
  let () = reset () |> Result.get_ok in
  let _ = new_type "nat" 0 in
  let nat_ty = TyCon ("nat", []) in
  let _ = new_constant "Zero" nat_ty in
  let _ = new_constant "Suc" (make_fun_ty nat_ty nat_ty) in
  let _ =
    new_constant "plus" (make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty))
  in

  let zero = Const ("Zero", nat_ty) in
  let suc = Const ("Suc", make_fun_ty nat_ty nat_ty) in
  let plus = Const ("plus", make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty)) in
  let n = make_var "n" nat_ty in
  let m = make_var "m" nat_ty in

  (* Rule 1: plus Zero n = n *)
  let rule1_lhs = App (App (plus, zero), n) in
  let rule1 = Result.get_ok (safe_make_eq rule1_lhs n) in
  let rule1_thm = Result.get_ok (new_axiom rule1) in

  (* Rule 2: plus (Suc m) n = Suc (plus m n) *)
  let rule2_lhs = App (App (plus, App (suc, m)), n) in
  let rule2_rhs = App (suc, App (App (plus, m), n)) in
  let rule2 = Result.get_ok (safe_make_eq rule2_lhs rule2_rhs) in
  let rule2_thm = Result.get_ok (new_axiom rule2) in

  (* Target: plus (Suc Zero) Zero - should match rule 2 *)
  let target = App (App (plus, App (suc, zero)), zero) in

  let result = rewrite_once_with_rules [ rule1_thm; rule2_thm ] target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    plus (Suc Zero) Zero = Suc (plus Zero Zero)
    |}]

let%expect_test "rewrite_all_with_rules: full nat addition" =
  let () = reset () |> Result.get_ok in
  let _ = new_type "nat" 0 in
  let nat_ty = TyCon ("nat", []) in
  let _ = new_constant "Zero" nat_ty in
  let _ = new_constant "Suc" (make_fun_ty nat_ty nat_ty) in
  let _ =
    new_constant "plus" (make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty))
  in

  let zero = Const ("Zero", nat_ty) in
  let suc = Const ("Suc", make_fun_ty nat_ty nat_ty) in
  let plus = Const ("plus", make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty)) in
  let n = make_var "n" nat_ty in
  let m = make_var "m" nat_ty in

  (* Rule 1: plus Zero n = n *)
  let rule1_lhs = App (App (plus, zero), n) in
  let rule1 = Result.get_ok (safe_make_eq rule1_lhs n) in
  let rule1_thm = Result.get_ok (new_axiom rule1) in

  (* Rule 2: plus (Suc m) n = Suc (plus m n) *)
  let rule2_lhs = App (App (plus, App (suc, m)), n) in
  let rule2_rhs = App (suc, App (App (plus, m), n)) in
  let rule2 = Result.get_ok (safe_make_eq rule2_lhs rule2_rhs) in
  let rule2_thm = Result.get_ok (new_axiom rule2) in

  (* Target: plus (Suc (Suc Zero)) (Suc Zero) = 2 + 1 = 3 *)
  let one = App (suc, zero) in
  let two = App (suc, one) in
  let target = App (App (plus, two), one) in

  let result = rewrite_all_with_rules [ rule1_thm; rule2_thm ] target in
  print_thm_result result;
  (* Should get: Suc (Suc (Suc Zero)) = 3 *)
  [%expect
    {|
    ========================================
    plus (Suc (Suc Zero)) (Suc Zero) = Suc (Suc (Suc Zero))
    |}]

(* ===== Boolean Rewrites ===== *)

let%expect_test "rewrite_once: P /\\ T = P" =
  let () = reset () |> Result.get_ok in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let t = make_true () in

  (* Rule: P /\ T = P *)
  let rule_lhs = make_conj p t in
  let rule = Result.get_ok (safe_make_eq rule_lhs p) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: Q /\ T *)
  let target = make_conj q t in

  let result = rewrite_once rule_thm target in
  print_thm_result result;
  [%expect {|
    ========================================
    Q ∧ T = Q
    |}]

let%expect_test "rewrite_once: P \\/ F = P" =
  let () = reset () |> Result.get_ok in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let f = make_false () in

  (* Rule: P \/ F = P *)
  let rule_lhs = make_disj p f in
  let rule = Result.get_ok (safe_make_eq rule_lhs p) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: (Q /\ Q) \/ F *)
  let target = make_disj (make_conj q q) f in

  let result = rewrite_once rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    Q ∧ Q ∨ F = Q ∧ Q
    |}]

let%expect_test "rewrite_all: simplify boolean expression" =
  let () = reset () |> Result.get_ok in
  let p = make_var "P" bool_ty in
  let t = make_true () in
  let f = make_false () in

  (* Rule 1: P /\ T = P *)
  let rule1_lhs = make_conj p t in
  let rule1 = Result.get_ok (safe_make_eq rule1_lhs p) in
  let rule1_thm = Result.get_ok (new_axiom rule1) in

  (* Rule 2: P \/ F = P *)
  let rule2_lhs = make_disj p f in
  let rule2 = Result.get_ok (safe_make_eq rule2_lhs p) in
  let rule2_thm = Result.get_ok (new_axiom rule2) in

  let q = make_var "Q" bool_ty in
  (* Target: ((Q /\ T) \/ F) /\ T *)
  let target = make_conj (make_disj (make_conj q t) f) t in

  let result = rewrite_all_with_rules [ rule1_thm; rule2_thm ] target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    Q ∧ T ∨ F ∧ T = Q
    |}]

(* ===== Edge Cases ===== *)

let%expect_test "rewrite_once: same variable used multiple times in pattern" =
  let () = reset () |> Result.get_ok in
  let _ = new_type "nat" 0 in
  let nat_ty = TyCon ("nat", []) in
  let _ = new_constant "double" (make_fun_ty nat_ty nat_ty) in
  let _ =
    new_constant "plus" (make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty))
  in

  let double = Const ("double", make_fun_ty nat_ty nat_ty) in
  let plus = Const ("plus", make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty)) in
  let n = make_var "n" nat_ty in
  let m = make_var "m" nat_ty in

  (* Rule: plus n n = double n (variable n appears twice in LHS) *)
  let rule_lhs = App (App (plus, n), n) in
  let rule_rhs = App (double, n) in
  let rule = Result.get_ok (safe_make_eq rule_lhs rule_rhs) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: plus m m - should match *)
  let target = App (App (plus, m), m) in

  let result = rewrite_once rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    plus m m = double m
    |}]

let%expect_test "rewrite_once: same variable different args doesn't match" =
  let () = reset () |> Result.get_ok in
  let _ = new_type "nat" 0 in
  let nat_ty = TyCon ("nat", []) in
  let _ = new_constant "Zero" nat_ty in
  let _ = new_constant "One" nat_ty in
  let _ = new_constant "double" (make_fun_ty nat_ty nat_ty) in
  let _ =
    new_constant "plus" (make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty))
  in

  let double = Const ("double", make_fun_ty nat_ty nat_ty) in
  let plus = Const ("plus", make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty)) in
  let zero = Const ("Zero", nat_ty) in
  let one = Const ("One", nat_ty) in
  let n = make_var "n" nat_ty in

  (* Rule: plus n n = double n *)
  let rule_lhs = App (App (plus, n), n) in
  let rule_rhs = App (double, n) in
  let rule = Result.get_ok (safe_make_eq rule_lhs rule_rhs) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: plus Zero One - should NOT match (different args) *)
  let target = App (App (plus, zero), one) in

  let result = rewrite_once rule_thm target in
  (match result with
  | Error `NoRewriteMatch -> print_endline "NoRewriteMatch (correct)"
  | Ok _ -> print_endline "unexpected match"
  | Error e -> print_endline ("unexpected error: " ^ Heft.show_kernel_error e));
  [%expect {| NoRewriteMatch (correct) |}]

let%expect_test "rewrite_once: rewrite in function position of application" =
  let () = reset () |> Result.get_ok in
  let _ = new_type "nat" 0 in
  let nat_ty = TyCon ("nat", []) in
  let _ = new_constant "Zero" nat_ty in
  let _ = new_constant "f" (make_fun_ty nat_ty nat_ty) in
  let _ = new_constant "g" (make_fun_ty nat_ty nat_ty) in

  let f = Const ("f", make_fun_ty nat_ty nat_ty) in
  let g = Const ("g", make_fun_ty nat_ty nat_ty) in
  let zero = Const ("Zero", nat_ty) in

  (* Rule: f = g *)
  let rule = Result.get_ok (safe_make_eq f g) in
  let rule_thm = Result.get_ok (new_axiom rule) in

  (* Target: f Zero - should rewrite f to g *)
  let target = App (f, zero) in

  let result = rewrite_once rule_thm target in
  print_thm_result result;
  [%expect
    {|
    ========================================
    f Zero = g Zero
    |}]
