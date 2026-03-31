open Heft
open Kernel
open Derived
open Tactic
open Theories

let%expect_test "template" =
  let prg =
    {|
    variable a : nat
    theorem theorem_name:
        forall λa. T
  |}
  in

  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = intros_tac >> truth_tac in
  run_proof ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀a. T

    Proof Complete!
    with fuel: 5
    |}]

let%expect_test "rewrite induction" =
  let open NatTheory in
  let x = make_var "x" nat_ty in
  let x_plus_zero = make_plus x zero |> Result.get_ok in
  let goal = ([], make_forall x (Result.get_ok (safe_make_eq x_plus_zero x))) in
  let proof = induct_tac >> simp_tac >> gen_tac >> intro_tac >> simp_tac in
  run_proof ~name:"plus_x_zero" goal proof;

  [%expect
    {|
    ========================================
    ∀x. plus x zero = x

    Proof Complete!
    with fuel: 53
    |}]

let%expect_test "basic nat" =
  let open NatTheory in
  let make_plus' a b = make_plus a b |> Result.get_ok in
  let two_plus_3 = make_plus' n2 n3 in
  let goal = ([], Result.get_ok (safe_make_eq two_plus_3 n5)) in
  run_proof goal simp_tac;

  [%expect
    {|
    ========================================
    plus (suc (suc zero)) (suc (suc (suc zero))) = suc (suc (suc (suc (suc zero))))

    Proof Complete!
    with fuel: 29
    |}]

let%expect_test "plus assoc" =
  let open NatTheory in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let z = make_var "z" nat_ty in
  let make_plus' a b = make_plus a b |> Result.get_ok in
  let plus_xy = make_plus' x y in
  let plus_yz = make_plus' y z in
  let plus_xy_z = make_plus' plus_xy z in
  let plus_x_yz = make_plus' x plus_yz in
  let goal =
    ( [],
      Derived.make_foralls [ x; y; z ]
        (Result.get_ok (safe_make_eq plus_x_yz plus_xy_z)) )
  in
  let proof =
    with_term x induct_tac >> intros_tac >> simp_tac >> intros_tac >> simp_tac
  in
  run_proof ~name:"plus_assoc" goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀y. ∀z. plus x (plus y z) = plus (plus x y) z

    Proof Complete!
    with fuel: 88
    |}]

let%expect_test "suc injective" =
  let open NatTheory in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let suc_x = App (suc, x) in
  let suc_y = App (suc, y) in
  (* Suc x = Suc y -> x = y *)
  let goal =
    ( [],
      Derived.make_foralls [ x; y ]
        (make_imp
           (Result.get_ok (safe_make_eq suc_x suc_y))
           (Result.get_ok (safe_make_eq x y))) )
  in
  let proof =
    intros_tac
    >> (apply_thm_tac |> with_rules nat_def.injective)
    >> assumption_tac
  in
  run_proof ~name:"plus_inj" goal proof;

  [%expect
    {|
    ========================================
    ∀x. ∀y. suc x = suc y ==> x = y

    Proof Complete!
    with fuel: 13
    |}]

(* Lemma needed for commutativity: plus x (Suc y) = Suc (plus x y) *)
let%expect_test "plus suc lemma" =
  let open NatTheory in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let suc_y = App (suc, y) in
  let plus_x_suc_y = Result.get_ok (make_plus x suc_y) in
  let plus_x_y = Result.get_ok (make_plus x y) in
  let suc_plus_x_y = App (suc, plus_x_y) in
  (* plus x (Suc y) = Suc (plus x y) *)
  let goal =
    ( [],
      Derived.make_foralls [ x; y ]
        (Result.get_ok (safe_make_eq plus_x_suc_y suc_plus_x_y)) )
  in
  let proof = induct_tac >> gen_tac >> simp_tac >> intros_tac >> simp_tac in
  run_proof ~name:"plus_suc" goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀y. plus x (suc y) = suc (plus x y)

    Proof Complete!
    with fuel: 69
    |}]

let%expect_test "suc injective rev" =
  let open NatTheory in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let suc_x = App (suc, x) in
  let suc_y = App (suc, y) in
  (* x = y -> Suc x =  Suc y *)
  let goal =
    ( [],
      Derived.make_foralls [ x; y ]
        (make_imp
           (Result.get_ok (safe_make_eq x y))
           (Result.get_ok (safe_make_eq suc_x suc_y))) )
  in
  let proof = intros_tac >> (rewrite_tac |> with_assumptions) >> refl_tac in
  run_proof ~name:"plus_inj_rev" goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀y. x = y ==> suc x = suc y

    Proof Complete!
    with fuel: 13
    |}]

(* Commutativity: plus x y = plus y x *)
let%expect_test "plus comm" =
  let open NatTheory in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let plus_x_y = Result.get_ok (make_plus x y) in
  let plus_y_x = Result.get_ok (make_plus y x) in
  (* plus x y = plus y x *)
  let goal =
    ( [],
      Derived.make_foralls [ x; y ]
        (Result.get_ok (safe_make_eq plus_x_y plus_y_x)) )
  in
  let proof =
    induct_tac >> gen_tac >> simp_tac
    >> with_first (with_proven [ "plus_x_zero" ] rewrite_tac)
    >> refl_tac >> intros_tac >> simp_tac >> sym_tac
    >> with_first (with_proven [ "plus_suc" ] apply_thm_tac)
  in
  run_proof ~name:"plus_comm" goal proof;

  [%expect
    {|
    ========================================
    ∀x. ∀y. plus x y = plus y x

    Proof Complete!
    with fuel: 73
    |}]

let%expect_test "cancellation" =
  let open NatTheory in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let z = make_var "z" nat_ty in
  let plus_x_y = Result.get_ok (make_plus x y) in
  let plus_x_z = Result.get_ok (make_plus x z) in
  let p_eq = Result.get_ok (safe_make_eq plus_x_y plus_x_z) in
  let y_eq_z = Result.get_ok (safe_make_eq y z) in
  (* plus x y = plus x z -> y = z *)
  let goal = ([], Derived.make_foralls [ x; y ] (make_imp p_eq y_eq_z)) in
  let proof =
    induct_tac >> simp_tac >> intros_tac >> assumption_tac >> intros_tac
    >> with_first (with_assumptions apply_thm_asm_tac)
    >> assumption_tac
  in
  run_proof goal proof;
  [%expect
    {|
    ∀n0. (∀y. plus n0 y = plus n0 z ==> y = z) ==> ∀y. plus (suc n0) y = plus (suc n0) z ==> y = z
    ========================================
    ∀x. ∀y. plus x y = plus x z ==> y = z

    Proof Complete!
    with fuel: 54
    |}]

let%expect_test "cancellation rev" =
  let open NatTheory in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let z = make_var "z" nat_ty in
  let plus_y_x = Result.get_ok (make_plus y x) in
  let plus_z_x = Result.get_ok (make_plus z x) in
  let p_eq = Result.get_ok (safe_make_eq plus_y_x plus_z_x) in
  let y_eq_z = Result.get_ok (safe_make_eq y z) in
  let goal = ([], Derived.make_foralls [ x; y ] (make_imp p_eq y_eq_z)) in
  let proof =
    induct_tac >> gen_tac
    >> with_proven [ "plus_x_zero" ] simp_tac
    >> intros_tac >> assumption_tac >> intros_tac
    >> with_proven [ "plus_suc" ] rewrite_asm_tac
    >> with_proven [ "plus_suc" ] rewrite_asm_tac
    >> with_proven [ "plus_inj" ] apply_thm_asm_tac
    >> with_first (with_assumptions apply_thm_tac)
    >> assumption_tac
  in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    ∀x. ∀y. plus y x = plus z x ==> y = z

    Proof Complete!
    with fuel: 61
    |}]

let%expect_test "length Nil = Zero" =
  let open NatTheory in
  let open ListTheory in
  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in
  let nil_nat = type_inst [ (a, nat_ty) ] nil |> Result.get_ok in

  let length_nil = App (length_const, nil_nat) in
  let goal = ([], Result.get_ok (safe_make_eq length_nil zero)) in
  let proof = simp_tac in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    length nil = zero

    Proof Complete!
    with fuel: 12
    |}]

let%expect_test "length (Cons Zero Nil) = Suc Zero" =
  let open NatTheory in
  let open ListTheory in
  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in
  let nil_nat = type_inst [ (a, nat_ty) ] nil |> Result.get_ok in
  let cons_nat = type_inst [ (a, nat_ty) ] cons |> Result.get_ok in

  (* Cons Zero Nil *)
  let cons_zero_nil = App (App (cons_nat, zero), nil_nat) in
  let length_cons = App (length_const, cons_zero_nil) in
  let goal = ([], Result.get_ok (safe_make_eq length_cons n1)) in
  let proof = simp_tac in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    length (cons zero nil) = suc zero

    Proof Complete!
    with fuel: 17
    |}]

let%expect_test "length_cons" =
  let open NatTheory in
  let open ListTheory in
  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in
  let cons_nat = type_inst [ (a, nat_ty) ] cons |> Result.get_ok in

  let x = make_var "x" nat_ty in
  let xs = make_var "xs" (TyCon ("list", [ nat_ty ])) in

  (* length (Cons x xs) *)
  let cons_x_xs = App (App (cons_nat, x), xs) in
  let length_cons_x_xs = App (length_const, cons_x_xs) in

  (* Suc (length xs) *)
  let length_xs = App (length_const, xs) in
  let suc_length_xs = App (suc, length_xs) in

  (* ∀x. ∀xs. length (Cons x xs) = Suc (length xs) *)
  let goal =
    ( [],
      Derived.make_foralls [ x; xs ]
        (Result.get_ok (safe_make_eq length_cons_x_xs suc_length_xs)) )
  in
  let proof = intros_tac >> simp_tac in
  run_proof ~name:"length_cons" ~simp:true goal proof;

  [%expect
    {|
    ========================================
    ∀x. ∀xs. length (cons x xs) = suc (length xs)

    Proof Complete!
    with fuel: 18
    |}]

(* xs = Nil ==> length xs = Zero *)
let%expect_test "nil_implies_length_zero" =
  let open NatTheory in
  let open ListTheory in
  let length_const = make_const "length" [] |> Result.get_ok in

  let xs = make_var "xs" (TyCon ("list", [ a ])) in

  (* xs = Nil *)
  let xs_eq_nil = Result.get_ok (safe_make_eq xs nil) in

  (* length xs = Zero *)
  let length_xs = App (length_const, xs) in
  let length_eq_zero = Result.get_ok (safe_make_eq length_xs zero) in

  (* ∀xs. xs = Nil ==> length xs = Zero *)
  let goal = ([], make_forall xs (make_imp xs_eq_nil length_eq_zero)) in
  let proof = intros_tac >> simp_tac ~with_asms:true in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    ∀xs. xs = nil ==> length xs = zero

    Proof Complete!
    with fuel: 22
    |}]

(* length xs = Zero ==> xs = Nil *)
let%expect_test "length_zero_implies_nil" =
  let open NatTheory in
  let open ListTheory in
  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in
  let nil_nat = type_inst [ (a, nat_ty) ] nil |> Result.get_ok in

  let xs = make_var "xs" (TyCon ("list", [ nat_ty ])) in

  (* length xs = Zero *)
  let length_xs = App (length_const, xs) in
  let length_eq_zero = Result.get_ok (safe_make_eq length_xs zero) in

  (* xs = Nil *)
  let xs_eq_nil = Result.get_ok (safe_make_eq xs nil_nat) in

  (* ∀xs. length xs = Zero ==> xs = Nil *)
  let goal = ([], make_forall xs (make_imp length_eq_zero xs_eq_nil)) in
  let proof =
    induct_tac >> intros_tac >> refl_tac >> intros_tac
    >> with_first (with_assumptions apply_thm_asm_tac)
    >> assumption_tac
  in
  run_proof goal proof;
  [%expect
    {|
    ∀n0. ∀n1. (length n1 = zero ==> n1 = nil) ==> length (cons n0 n1) = zero ==> cons n0 n1 = nil
    ========================================
    ∀x. length x = zero ==> x = nil

    Proof Complete!
    with fuel: 27
    |}]

let%expect_test "append nil xs = xs" =
  let open ListTheory in
  let append_const = make_const "append" [] |> Result.get_ok in

  (* append Nil Nil = Nil *)
  let xs = make_var "xs" list_a in
  let append_nil = App (append_const, nil) in
  let append_nil_xs = App (append_nil, xs) in
  let goal =
    ([], make_forall xs @@ Result.get_ok (safe_make_eq append_nil_xs xs))
  in
  let proof = intros_tac >> simp_tac in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    ∀xs. append nil xs = xs

    Proof Complete!
    with fuel: 23
    |}]

let%expect_test "append (Cons x xs) ys = Cons x (append xs ys)" =
  let open ListTheory in
  let append_const = make_const "append" [] |> Result.get_ok in

  (* append (Cons x xs) ys = Cons x (append xs ys) *)
  let x = make_var "x" a in
  let xs = make_var "xs" list_a in
  let ys = make_var "ys" list_a in

  (* LHS: append (Cons x xs) ys *)
  let cons_x_xs = App (App (cons, x), xs) in
  let append_cons = App (append_const, cons_x_xs) in
  let lhs = App (append_cons, ys) in

  (* RHS: Cons x (append xs ys) *)
  let append_xs = App (append_const, xs) in
  let append_xs_ys = App (append_xs, ys) in
  let rhs = App (App (cons, x), append_xs_ys) in

  let goal =
    ([], make_foralls [ x; xs; ys ] @@ Result.get_ok (safe_make_eq lhs rhs))
  in
  let proof = intros_tac >> simp_tac in
  run_proof ~name:"append_cons" goal proof;

  [%expect
    {|
    ========================================
    ∀x. ∀xs. ∀ys. append (cons x xs) ys = cons x (append xs ys)

    Proof Complete!
    with fuel: 27
    |}]

let%expect_test "append xs nil = xs" =
  let open ListTheory in
  let append_const = make_const "append" [] |> Result.get_ok in

  (* need a lemma *)
  let xs = make_var "xs" list_a in
  let append_xs = App (append_const, xs) in
  let append_nil_xs = App (append_xs, nil) in
  let proof =
    induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "append_cons" ] rewrite_tac
    >> with_proven [ "append_cons" ] simp_tac
  in
  let goal =
    ([], make_forall xs @@ Result.get_ok (safe_make_eq append_nil_xs xs))
  in
  run_proof ~name:"append_xs_nil" goal proof;

  [%expect
    {|
    ========================================
    ∀x. append x nil = x

    Proof Complete!
    with fuel: 51
    |}]

let%expect_test "append (append xs ys) zs = append xs (append ys zs)" =
  let open ListTheory in
  let append_const = make_const "append" [] |> Result.get_ok in

  let xs = make_var "xs" list_a in
  let ys = make_var "ys" list_a in
  let zs = make_var "zs" list_a in

  (* LHS: append (append xs ys) zs *)
  let append_xs_ys = App (App (append_const, xs), ys) in
  let lhs = App (App (append_const, append_xs_ys), zs) in

  (* RHS: append xs (append ys zs) *)
  let append_ys_zs = App (App (append_const, ys), zs) in
  let rhs = App (App (append_const, xs), append_ys_zs) in

  let proof = induct_tac >>= [ auto_dfs_tac; auto_dfs_tac ] in
  let goal =
    ([], make_foralls [ xs; ys; zs ] @@ Result.get_ok (safe_make_eq lhs rhs))
  in
  run_proof ~name:"append_assoc" goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      gen_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      gen_tac >>
      intro_tac >>
      rewrite_tac >>
      gen_tac >>
      gen_tac >>
      refl_tac
    ========================================
    ∀x. ∀ys. ∀zs. append (append x ys) zs = append x (append ys zs)

    Proof Complete!
    with fuel: 161
    |}]

let%expect_test "length (append xs ys) = plus (length xs) (length ys)" =
  let open NatTheory in
  let open ListTheory in
  let append_const = make_const "append" [ (a, nat_ty) ] |> Result.get_ok in
  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in

  let xs = make_var "xs" (TyCon ("list", [ nat_ty ])) in
  let ys = make_var "ys" (TyCon ("list", [ nat_ty ])) in

  (* LHS: length (append xs ys) *)
  let append_xs_ys = App (App (append_const, xs), ys) in
  let lhs = App (length_const, append_xs_ys) in

  (* RHS: plus (length xs) (length ys) *)
  let length_xs = App (length_const, xs) in
  let length_ys = App (length_const, ys) in
  let rhs = Result.get_ok (make_plus length_xs length_ys) in

  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  let goal =
    ([], make_foralls [ xs; ys ] @@ Result.get_ok (safe_make_eq lhs rhs))
  in
  run_proof ~name:"append_length" goal proof;

  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      gen_tac >>
      gen_tac >>
      intro_tac >>
      rewrite_tac >>
      gen_tac >>
      refl_tac
    ========================================
    ∀x. ∀ys. length (append x ys) = plus (length x) (length ys)

    Proof Complete!
    with fuel: 146
    |}]

let%expect_test "length (reverse xs) = length xs" =
  let open NatTheory in
  let open ListTheory in
  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in
  let reverse_const = make_const "reverse" [ (a, nat_ty) ] |> Result.get_ok in

  let xs = make_var "xs" (TyCon ("list", [ nat_ty ])) in

  (* LHS: length (reverse xs) *)
  let reverse_xs = App (reverse_const, xs) in
  let lhs = App (length_const, reverse_xs) in

  (* RHS: length xs *)
  let rhs = App (length_const, xs) in

  let proof =
    induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "append_length" ] simp_tac
    >> with_first (with_proven [ "plus_comm" ] rewrite_tac)
    >> simp_tac
  in
  let goal = ([], make_forall xs @@ Result.get_ok (safe_make_eq lhs rhs)) in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    ∀x. length (reverse x) = length x

    Proof Complete!
    with fuel: 104
    |}]

let%expect_test "reverse (append xs ys) = append (reverse ys) (reverse xs)" =
  let open NatTheory in
  let open ListTheory in
  let append_const = make_const "append" [ (a, nat_ty) ] |> Result.get_ok in
  let reverse_const = make_const "reverse" [ (a, nat_ty) ] |> Result.get_ok in

  let xs = make_var "xs" (TyCon ("list", [ nat_ty ])) in
  let ys = make_var "ys" (TyCon ("list", [ nat_ty ])) in

  (* LHS: reverse (append xs ys) *)
  let append_xs_ys = App (App (append_const, xs), ys) in
  let lhs = App (reverse_const, append_xs_ys) in

  (* RHS: append (reverse ys) (reverse xs) *)
  let reverse_xs = App (reverse_const, xs) in
  let reverse_ys = App (reverse_const, ys) in
  let rhs = App (App (append_const, reverse_ys), reverse_xs) in

  let proof =
    induct_tac >> intros_tac
    >> with_proven [ "append_xs_nil" ] simp_tac
    >> intros_tac >> simp_tac
    >> with_first (with_proven [ "append_assoc" ] apply_thm_tac)
  in
  let goal =
    ([], make_foralls [ xs; ys ] @@ Result.get_ok (safe_make_eq lhs rhs))
  in
  run_proof ~name:"append_reverse" goal proof;

  [%expect
    {|
    ========================================
    ∀x. ∀ys. reverse (append x ys) = append (reverse ys) (reverse x)

    Proof Complete!
    with fuel: 90
    |}]

let%expect_test "reverse (reverse xs) = xs" =
  let open NatTheory in
  let open ListTheory in
  let reverse_const = make_const "reverse" [ (a, nat_ty) ] |> Result.get_ok in

  let xs = make_var "xs" (TyCon ("list", [ nat_ty ])) in

  (* LHS: reverse (reverse xs) *)
  let reverse_xs = App (reverse_const, xs) in
  let lhs = App (reverse_const, reverse_xs) in

  (* RHS: xs *)
  let rhs = xs in

  let proof =
    induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "append_reverse" ] simp_tac
  in
  let goal = ([], make_forall xs @@ Result.get_ok (safe_make_eq lhs rhs)) in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    ∀x. reverse (reverse x) = x

    Proof Complete!
    with fuel: 93
    |}]

let%expect_test "test defining with elab" =
  let prg =
    {|
    vartype a
    variable x y : a
    theorem fst_snd_eq: imp (eq x y) (eq (fst (pair x y)) (snd (pair x y)))

  |}
  in
  let proof = intros_tac >> simp_tac in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    x = y ==> fst (pair x y) = snd (pair x y)

    Proof Complete!
    with fuel: 25
    |}]

let%expect_test "test minus" =
  let prg =
    {|
    theorem three_minus_one_is_two : eq
        (pred (suc (suc (suc zero))) )
        (suc (suc zero))
  |}
  in
  let proof = simp_tac in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    pred (suc (suc (suc zero))) = suc (suc zero)

    Proof Complete!
    with fuel: 12
    |}]

let%expect_test "test minus 2" =
  let prg =
    {|
    theorem sub_add_elim: eq
        (minus
            (suc (suc (suc (suc zero))))
            (suc (suc (suc zero))))
        (suc zero)
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof goal simp_tac;

  [%expect
    {|
    ========================================
    minus (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = suc zero

    Proof Complete!
    with fuel: 66
    |}]

let%expect_test "n - 0 = n" =
  let prg =
    {|
    variable n : nat
    theorem minus_zero:
            (forall λn.
                (eq
                    (minus n zero)
                    (n)
                ))

  |}
  in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof ~name:"minus_zero" goal proof;

  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      refl_tac
    ========================================
    ∀x. minus x zero = x

    Proof Complete!
    with fuel: 122
    |}]

(* n - (suc m) = (n - m) - 1 *)
let%expect_test "minus suc right" =
  let prg =
    {|
    variable n m : nat
    theorem minus_suc_right:
            (forall λn.
                (forall λm.
                    (eq
                        (minus n (suc m))
                        (pred (minus n m))
                    )))

  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> with_proven [ "minus_zero" ] auto_dfs_tac >> auto_dfs_tac
  in
  run_proof ~name:"minus_suc_right" goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      gen_tac >>
      refl_tac
    ========================================
    ∀x. ∀m. minus x (suc m) = pred (minus x m)

    Proof Complete!
    with fuel: 178
    |}]

(* (suc n) - (suc m) = n - m *)
let%expect_test "minus suc suc" =
  let prg =
    {|
    variable n m : nat
    theorem minus_suc_suc:
            (forall λn.
                (forall λm.
                    (eq
                        (minus (suc n) (suc m))
                        (minus n m)
                    )))

  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    gen_tac >> induct_tac
    >> with_proven [ "minus_zero" ] simp_tac
    >> intros_tac
    >> with_proven [ "minus_suc_right" ] rewrite_tac
    >> with_assumptions rewrite_tac
    >> with_proven [ "minus_suc_right" ] rewrite_tac
    >> refl_tac
  in

  run_proof ~name:"minus_suc_suc" goal proof;
  [%expect
    {|
    ========================================
    ∀n. ∀x. minus (suc n) (suc x) = minus n x

    Proof Complete!
    with fuel: 81
    |}]

let%expect_test "n - n = z" =
  let prg =
    {|
    variable n : nat
    theorem minus_zero:
            (forall λn.
                (eq
                    (minus n n)
                    (zero)
                ))

  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "minus_suc_suc" ] simp_tac
    >> simp_asm_tac ~with_asms:false
  in
  run_proof ~name:"minus_self" goal proof;

  [%expect
    {|
    ========================================
    ∀x. minus x x = zero

    Proof Complete!
    with fuel: 103
    |}]

let%expect_test "x - n + n = x" =
  let prg =
    {|
    variable x n : nat
    theorem four_min_three_is_one:
        forall (λx.
            (forall λn.
                (eq
                    (minus (plus x n) n)
                    (x)
                )))

  |}
  in

  let proof =
    gen_tac >> induct_tac
    >> with_proven [ "plus_x_zero"; "minus_zero" ] simp_tac
    >> intros_tac
    >> with_proven [ "plus_suc" ] rewrite_tac
    >> with_proven [ "minus_suc_suc" ] rewrite_tac
    >> assumption_tac
  in

  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀x'. minus (plus x x') x' = x

    Proof Complete!
    with fuel: 42
    |}]

let%expect_test "pred twice" =
  let prg =
    {|
    theorem four_min_three_is_one:
        eq 
            (twice pred (suc (suc zero)))
            (zero)
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof goal simp_tac;

  [%expect
    {|
    ========================================
    twice pred (suc (suc zero)) = zero

    Proof Complete!
    with fuel: 29
    |}]

let%expect_test "flip f" =
  let prg =
    {|
    vartype a b c
    variable f : a -> b -> c

    variable x : a
    variable y : b


    theorem flip_f:
        forall (λf.
        eq 
            (flip f y x)
            (f x y))
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = gen_tac >> simp_tac in
  run_proof ~name:"flip_f" goal proof;

  [%expect
    {|
    ========================================
    ∀f. flip f y x = f x y

    Proof Complete!
    with fuel: 20
    |}]

let%expect_test "bool distinct" =
  let prg = {|
    theorem bool_distinct : neg (eq T F)
    
  |} in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let t = true_def |> Result.get_ok in
  let proof =
    neg_intro_tac
    >> with_assumptions (with_flip_rules rewrite_tac)
    >> with_rule t rewrite_tac >> refl_tac
  in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    ¬T = F

    Proof Complete!
    with fuel: 15
    |}]

let%expect_test "cond true" =
  let prg =
    {|
    vartype a
    variable t1 t2 : a
    theorem cond_true : eq (COND T t1 t2) t1
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_rule (cond_def |> Result.get_ok) rewrite_tac
    >> beta_tac
    >> with_rule t_eq_t rewrite_tac
    >> with_rule t_eq_f rewrite_tac
    >> with_rule f_imp_eq rewrite_tac
    >> with_rule conj_t_eq rewrite_tac
    >> with_rule t_imp_eq rewrite_tac
    >> with_rule select_eq rewrite_tac
    >> refl_tac
  in
  run_proof ~notrace:true goal proof;

  [%expect
    {|
    ========================================
    COND T t1 t2 = t1

    Proof Complete!
    with fuel: 37
    |}]

let%expect_test "cond false" =
  let prg =
    {|
    vartype a
    variable t1 t2 : a
    theorem cond_false : eq (COND F t1 t2) t2
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_rule (cond_def |> Result.get_ok) rewrite_tac
    >> beta_tac
    >> with_rule f_eq_t rewrite_tac
    >> with_rule f_eq_f rewrite_tac
    >> with_rule f_imp_eq rewrite_tac
    >> with_rule t_conj_eq rewrite_tac
    >> with_rule t_imp_eq rewrite_tac
    >> with_rule select_eq rewrite_tac
    >> refl_tac
  in
  run_proof ~notrace:true goal proof;

  [%expect
    {|
    ========================================
    COND F t1 t2 = t2

    Proof Complete!
    with fuel: 37
    |}]

let%expect_test "le nat test" =
  let prg = {|
    theorem nat_test: eq (nat_le (zero) (suc zero)) T 
  |} in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = simp_tac in
  run_proof ~notrace:true goal proof;

  [%expect
    {|
    ========================================
    nat_le zero (suc zero) = T

    Proof Complete!
    with fuel: 19
    |}]

let%expect_test "le nat test2" =
  let prg =
    {|
    theorem nat_test2: eq (nat_le (suc (suc (suc zero))) (suc zero)) F
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = simp_tac in
  run_proof ~notrace:true goal proof;

  [%expect
    {|
    ========================================
    nat_le (suc (suc (suc zero))) (suc zero) = F

    Proof Complete!
    with fuel: 58
    |}]

(* insert 3 into [] = [3] *)
let%expect_test "insert into nil" =
  let prg =
    {|
    theorem insert_nil : eq (insert nil (suc (suc (suc zero)))) (cons (suc (suc (suc zero))) nil)
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = simp_tac in
  run_proof ~notrace:true goal proof;

  [%expect
    {|
    ========================================
    insert nil (suc (suc (suc zero))) = cons (suc (suc (suc zero))) nil

    Proof Complete!
    with fuel: 19
    |}]

(* insert 2 into [1] = [1, 2] *)
let%expect_test "insert into singleton" =
  let prg =
    {|
    theorem insert_sorted : eq
      (insert (cons (suc zero) nil) (suc (suc zero)))
      (cons (suc zero) (cons (suc (suc zero)) nil))
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = simp_tac in
  run_proof ~notrace:true goal proof;

  [%expect
    {|
    ========================================
    insert (cons (suc zero) nil) (suc (suc zero)) = cons (suc zero) (cons (suc (suc zero)) nil)

    Proof Complete!
    with fuel: 51
    |}]

let%expect_test "test sub" =
  let prg =
    {|
    theorem sub_add_elim: eq
        (sub
            (suc (suc (suc (suc zero))))
            (suc (suc (suc zero))))
        (suc zero)
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof goal simp_tac;

  [%expect
    {|
    ========================================
    sub (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = suc zero

    Proof Complete!
    with fuel: 87
    |}]

let%expect_test "minus zero left" =
  let prg =
    {|
    variable n : nat
    theorem minus_zero_left:
        forall λn.
            eq (minus zero n) zero
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> simp_tac >> intros_tac
    >> simp_asm_tac ~with_asms:false
    >> simp_tac ~with_asms:false
    >> with_assumptions rewrite_tac
    >> simp_tac
  in
  run_proof ~name:"minus_zero_left" goal proof;

  [%expect
    {|
    ========================================
    ∀x. minus zero x = zero

    Proof Complete!
    with fuel: 127
    |}]

let%expect_test "sub eq minus" =
  let prg =
    {|
    variable m n : nat
    theorem sub_eq_minus:
        forall λm.
        forall λn.
            eq (sub m n) (minus m n)
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac
    >>= [
          with_proven [ "minus_zero_left" ] simp_tac >>> gen_tac >>> refl_tac;
          gen_tac >> intro_tac >> induct_tac
          >>= [
                with_proven [ "minus_zero" ] simp_tac;
                intros_tac
                >> with_proven [ "minus_suc_suc" ] rewrite_tac
                >> simp_tac;
              ];
        ]
  in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    ∀x. ∀n. sub x n = minus x n

    Proof Complete!
    with fuel: 162
    |}]

(* isort [] = [] *)
let%expect_test "isort nil" =
  let prg = {|
    theorem isort_nil : eq (isort nil) nil
  |} in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof goal simp_tac;
  [%expect
    {|
    ========================================
    isort nil = nil

    Proof Complete!
    with fuel: 12
    |}]

(* isort [3,1,2] = [1,2,3] *)
let%expect_test "isort [3,1,2] = [1,2,3]" =
  let prg =
    {|
    theorem isort_test : eq
      (isort (cons (suc (suc (suc zero))) (cons (suc zero) (cons (suc (suc zero)) nil))))
      (cons (suc zero) (cons (suc (suc zero)) (cons (suc (suc (suc zero))) nil)))
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof goal simp_tac;
  [%expect
    {|
    ========================================
    isort (cons (suc (suc (suc zero))) (cons (suc zero) (cons (suc (suc zero)) nil))) = cons (suc zero) (cons (suc (suc zero)) (cons (suc (suc (suc zero))) nil))

    Proof Complete!
    with fuel: 186
    |}]

let%expect_test "bool eq" =
  let prg = {|
    theorem bool_eq: eq (eqb T F) F
    
  |} in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = simp_tac in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    eqb T F = F

    Proof Complete!
    with fuel: 36
    |}]

let%expect_test "bool cases tac" =
  let b = make_var "b" bool_ty in
  let b_eq_t = Result.get_ok (safe_make_eq b (make_true ())) in
  let b_eq_f = Result.get_ok (safe_make_eq b (make_false ())) in
  let goal = ([], make_forall b (make_disj b_eq_t b_eq_f)) in
  let proof = cases_tac >>= [ left_tac >> refl_tac; right_tac >> refl_tac ] in
  run_proof ~name:"bool_cases_test" goal proof;
  [%expect
    {|
    ========================================
    ∀b. b = T ∨ b = F

    Proof Complete!
    with fuel: 22
    |}]

let%expect_test "nat_le_flip" =
  let prg =
    {|
    variable m n : nat
    theorem nat_le_flip:
        forall λm. forall λn.
            imp (eq (nat_le m n) F)
                (eq (nat_le n m) T)
    |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac
    >>= [
          gen_tac >> intro_tac
          >> simp_asm_tac ~with_asms:false
          >> sym_asm_tac >> eq_true_elim_asm_tac >> false_elim_tac;
          gen_tac >> intro_tac >> induct_tac >> (intro_tac >> simp_tac)
          >> (intros_tac
             >> simp_asm_tac ~with_asms:false
             >> simp_tac
             >> with_assumptions (with_first (apply_thm_tac >> assumption_tac))
             );
        ]
  in
  run_proof ~name:"nat_le_flip" goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀n. nat_le x n = F ==> nat_le n x = T

    Proof Complete!
    with fuel: 151
    |}]

let%expect_test "sort correct lemma" =
  let prg =
    {|
    variable n0 n0' n : nat
    variable n1 : list nat

    variable n : nat
    variable l : list nat

    theorem insert_sorted:
        forall λl. forall λn.
            imp (sorted l)
                (sorted (insert l n))

    term le : nat_le n0' n
    term n0 : n0
    term n1 : n1
    term n : n
    |}
  in
  let le = Elaborator.term_from_string prg "le" in
  let n1 = Elaborator.term_from_string prg "n1" in
  let n0 = Elaborator.term_from_string prg "n0" in
  let n = Elaborator.term_from_string prg "n" in

  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >>> (intros_tac >> simp_tac)
    >>= [
          conj_tac >>> truth_tac;
          cond_tac >>> (simp_tac >> conj_tac)
          >>= [
                with_arbitrary_term n1 induct_tac
                >>> (intros_tac >> simp_tac)
                >>= [
                      with_arbitrary_term le cases_tac
                      >>> simp_tac
                      >>= [
                            simp_asm_tac >> elim_conj_asm_tac >> assumption_tac;
                            truth_tac;
                          ];
                    ];
                spec_asm_tac n >> apply_asm_tac >> simp_asm_tac
                >> elim_conj_asm_tac >> with_first assumption_tac;
                with_proven [ "nat_le_flip" ] apply_thm_asm_tac >> simp_tac;
                conj_tac
                >>= [
                      with_arbitrary_term n1 induct_tac
                      >>> (intros_tac >> simp_tac)
                      >>= [
                            simp_asm_tac >> elim_conj_asm_tac >> assumption_tac;
                          ];
                      spec_asm_tac n0 >> simp_asm_tac >> elim_conj_asm_tac
                      >> with_first assumption_tac;
                    ];
              ];
        ]
  in

  run_proof ~name:"sort_correct_lemma" goal proof;

  [%expect
    {|
    ========================================
    ∀x. ∀n. sorted x ==> sorted (insert x n)

    Proof Complete!
    with fuel: 553
    |}]

let%expect_test "sort correct" =
  let prg =
    {|
    variable l : list nat
    theorem sort_correct: 
        forall λl.
             sorted (isort l)
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> simp_tac >> intros_tac >> simp_tac
    >> with_proven [ "sort_correct_lemma" ] apply_thm_tac
    >> assumption_tac
  in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    ∀x. sorted (isort x)

    Proof Complete!
    with fuel: 52
    |}]

let%expect_test "option not none" =
  let prg =
    {|

  vartype a
  variable x a0 : a
  variable o : option a
  theorem option_not_none:
    forall λo.
        imp (neg (eq o none))
            (exists λx. eq o (some x))
  term o : o
  term a0 : a0
  |}
  in
  let o = Elaborator.term_from_string prg "o" in
  let a0 = Elaborator.term_from_string prg "a0" in

  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    intros_tac
    >> with_arbitrary_term o destruct_tac
    >> elim_disj_asm_tac >> neg_elim_tac >> elim_exists_asm_tac
    >> with_arbitrary_term a0 exists_tac
    >> assumption_tac
  in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    ∀o. ¬o = none ==> ∃x. o = some x

    Proof Complete!
    with fuel: 30
    |}]

let%expect_test "div fuel irrel" =
  let prg =
    {|
  variable n m a b x n0 a0: nat

  theorem div_fuel_irrel:
    forall λn. forall λm. forall λa. forall λb. forall λx.
        imp (eq (div_aux n a b) (some x))
            (eq (div_aux (plus n m) a b) (some x))

  term lt : nat_lt a b 
  term div1 : div_aux n0 (sub a b) b
  term subab : sub a b
  term a0 : a0
  term m : m
  term b : b

  |}
  in
  let lt = Elaborator.term_from_string prg "lt" in
  let div1 = Elaborator.term_from_string prg "div1" in
  let subab = Elaborator.term_from_string prg "subab" in
  let a0 = Elaborator.term_from_string prg "a0" in
  let m = Elaborator.term_from_string prg "m" in
  let b = Elaborator.term_from_string prg "b" in

  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> intros_tac >> simp_asm_tac
    >> with_rule (List.hd OptionTheory.option_def.distinct) rewrite_asm_tac
    >> false_elim_tac >> intros_tac
    >> with_first (with_definition [ "plus" ] rewrite_tac)
    >> beta_tac >> simp_tac >> simp_asm_tac
    >> with_arbitrary_term lt cases_tac
    >> simp_tac >> simp_asm_tac
    >> with_arbitrary_term div1 destruct_tac
    >> elim_disj_asm_tac >> simp_asm_tac
    >> with_first
       @@ with_rule (List.hd OptionTheory.option_def.distinct) rewrite_asm_tac
    >> false_elim_tac >> elim_exists_asm_tac >> simp_asm_tac >> spec_asm_tac m
    >> spec_asm_tac subab >> spec_asm_tac b >> spec_asm_tac a0
    >> with_first mp_asm_tac
    >> with_assumptions rewrite_tac
    >> simp_tac >> simp_tac
    >> with_nth_term 1 (with_assumptions rewrite_asm_tac)
    >> simp_asm_tac >> simp_asm_tac
  in
  run_proof ~name:"div_fuel_irrel" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀m. ∀a. ∀b. ∀x'. div_aux x a b = some x' ==> div_aux (plus x m) a b = some x'

    Proof Complete!
    with fuel: 292
    |}]

let%expect_test "lt_zero_suc" =
  let prg =
    {|
    variable b x n0 : nat
    theorem lt_zero_suc :
        forall λb.
            imp (nat_lt zero b)
                (exists λx. eq b (suc x))
    term n0 : n0
  |}
  in

  let n0 = Elaborator.term_from_string prg "n0" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> intros_tac >> simp_asm_tac >> false_elim_tac >> intros_tac
    >> with_arbitrary_term n0 exists_tac
    >> refl_tac
  in
  run_proof ~simp:true ~name:"lt_zero_suc" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. nat_lt zero x ==> ∃x'. x = suc x'

    Proof Complete!
    with fuel: 58
    |}]

let%expect_test "suc_lt_zero" =
  let prg =
    {|
  variable b x : nat
  theorem suc_lt_zero :
    forall λx. forall λb.
        imp (eq b (suc x))
            (nat_lt zero b)
  |}
  in

  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"suc_lt_zero" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      gen_tac >>
      intro_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac
    ========================================
    ∀x. ∀b. b = suc x ==> nat_lt zero b

    Proof Complete!
    with fuel: 160
    |}]

let%expect_test "lt_zero_suc" =
  let prg =
    {|
    variable a : nat
    theorem lt_zero_false :
        forall λa. eq (nat_lt a zero) F

  |}
  in

  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"lt_zero_false" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      refl_tac
    ========================================
    ∀x. nat_lt x zero = F

    Proof Complete!
    with fuel: 97
    |}]

let%expect_test "lt_add_suc_r" =
  let prg =
    {|
    variable a b : nat
    theorem lt_add_suc_r:
        forall λa. forall λb. nat_lt a (plus a (suc b))
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~name:"lt_add_suc_r" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      assumption_tac
    ========================================
    ∀x. ∀b. nat_lt x (plus x (suc b))

    Proof Complete!
    with fuel: 154
    |}]

let%expect_test "add_lt_cancel_l" =
  let prg =
    {|
    variable a b c : nat
    theorem add_lt_cancel_l:
        forall λa. forall λb. forall λc.
            eq (nat_lt (plus a b) (plus a c)) (nat_lt b c)
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~name:"add_lt_cancel_l" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      gen_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      rewrite_tac >>
      gen_tac >>
      gen_tac >>
      refl_tac
    ========================================
    ∀x. ∀b. ∀c. nat_lt (plus x b) (plus x c) = nat_lt b c

    Proof Complete!
    with fuel: 164
    |}]

let%expect_test "add_le_cancel_l" =
  let prg =
    {|
    variable a b c : nat
    theorem add_le_cancel_l:
        forall λa. forall λb. forall λc.
            eq (nat_le (plus a b) (plus a c)) (nat_le b c)
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~name:"add_le_cancel_l" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      gen_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      rewrite_tac >>
      gen_tac >>
      gen_tac >>
      refl_tac
    ========================================
    ∀x. ∀b. ∀c. nat_le (plus x b) (plus x c) = nat_le b c

    Proof Complete!
    with fuel: 164
    |}]

(* ===== Group 1: Basic computation rules ===== *)

let%expect_test "sub_zero_r" =
  let prg =
    {|
    variable a : nat
    theorem sub_zero_r:
        forall λa. eq (sub a zero) a
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"sub_zero_r" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      beta_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      refl_tac
    ========================================
    ∀x. sub x zero = x

    Proof Complete!
    with fuel: 85
    |}]

let%expect_test "sub_suc_suc" =
  let prg =
    {|
    variable a b : nat
    theorem sub_suc_suc:
        forall λa. forall λb. eq (sub (suc a) (suc b)) (sub a b)
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"sub_suc_suc" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      gen_tac >>
      refl_tac
    ========================================
    ∀x. ∀b. sub (suc x) (suc b) = sub x b

    Proof Complete!
    with fuel: 153
    |}]

let%expect_test "sub_zero_l" =
  let prg =
    {|
    variable a : nat
    theorem sub_zero_l:
        forall λa. eq (sub zero a) zero
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"sub_zero_l" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      refl_tac
    ========================================
    ∀x. sub zero x = zero

    Proof Complete!
    with fuel: 71
    |}]

let%expect_test "lt_zero_suc" =
  let prg =
    {|
    variable a : nat
    theorem lt_zero_suc:
        forall λa. eq (nat_lt zero (suc a)) T
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"lt_zero_suc" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      refl_tac
    ========================================
    ∀x. nat_lt zero (suc x) = T

    Proof Complete!
    with fuel: 107
    |}]

let%expect_test "lt_suc_suc" =
  let prg =
    {|
    variable a b : nat
    theorem lt_suc_suc:
        forall λa. forall λb. eq (nat_lt (suc a) (suc b)) (nat_lt a b)
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"lt_suc_suc" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      gen_tac >>
      refl_tac
    ========================================
    ∀x. ∀b. nat_lt (suc x) (suc b) = nat_lt x b

    Proof Complete!
    with fuel: 153
    |}]

let%expect_test "le_zero_eq" =
  let prg =
    {|
    variable a : nat
    theorem le_zero_eq:
        forall λa. imp (nat_le a zero) (eq a zero)
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"le_zero_eq" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      beta_tac >>
      intro_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      intro_tac >>
      false_elim_tac
    ========================================
    ∀x. nat_le x zero ==> x = zero

    Proof Complete!
    with fuel: 127
    |}]

let%expect_test "le_zero_l" =
  let prg =
    {|
    variable a : nat
    theorem le_zero_l:
        forall λa. eq (nat_le zero a) T
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"le_zero_l" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      beta_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      refl_tac
    ========================================
    ∀x. nat_le zero x = T

    Proof Complete!
    with fuel: 78
    |}]

let%expect_test "le_suc_suc" =
  let prg =
    {|
    variable a b : nat
    theorem le_suc_suc:
        forall λa. forall λb. eq (nat_le (suc a) (suc b)) (nat_le a b)
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"le_suc_suc" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      gen_tac >>
      refl_tac
    ========================================
    ∀x. ∀b. nat_le (suc x) (suc b) = nat_le x b

    Proof Complete!
    with fuel: 153
    |}]

let%expect_test "le_zero_r" =
  let prg =
    {|
    variable a : nat
    theorem le_zero_r:
        forall λa. eq (nat_le (suc a) zero) F
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"le_zero_r" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      refl_tac
    ========================================
    ∀x. nat_le (suc x) zero = F

    Proof Complete!
    with fuel: 117
    |}]

(* ===== Group 2: Reflexivity and basic identity ===== *)

let%expect_test "lt_irrefl" =
  let prg =
    {|
    variable a : nat
    theorem lt_irrefl:
        forall λa. eq (nat_lt a a) F
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"lt_irrefl" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      gen_tac >>
      intro_tac >>
      rewrite_tac >>
      refl_tac
    ========================================
    ∀x. nat_lt x x = F

    Proof Complete!
    with fuel: 64
    |}]

let%expect_test "le_refl" =
  let prg =
    {|
    variable a : nat
    theorem le_refl:
        forall λa. eq (nat_le a a) T
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"le_refl" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      gen_tac >>
      intro_tac >>
      rewrite_tac >>
      refl_tac
    ========================================
    ∀x. nat_le x x = T

    Proof Complete!
    with fuel: 64
    |}]

let%expect_test "sub_self" =
  let prg =
    {|
    variable a : nat
    theorem sub_self:
        forall λa. eq (sub a a) zero
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"sub_self" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      gen_tac >>
      intro_tac >>
      rewrite_tac >>
      refl_tac
    ========================================
    ∀x. sub x x = zero

    Proof Complete!
    with fuel: 64
    |}]

let%expect_test "add_zero_l" =
  let prg =
    {|
    variable a : nat
    theorem add_zero_l:
        forall λa. eq (plus zero a) a
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"add_zero_l" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      beta_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      refl_tac
    ========================================
    ∀x. plus zero x = x

    Proof Complete!
    with fuel: 78
    |}]

let%expect_test "add_suc_l" =
  let prg =
    {|
    variable a b : nat
    theorem add_suc_l:
        forall λa. forall λb. eq (plus (suc a) b) (suc (plus a b))
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"add_suc_l" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      gen_tac >>
      refl_tac
    ========================================
    ∀x. ∀b. plus (suc x) b = suc (plus x b)

    Proof Complete!
    with fuel: 124
    |}]

(* ===== Group 3: Successor relationships ===== *)

let%expect_test "lt_suc_self" =
  let prg =
    {|
    variable a : nat
    theorem lt_suc_self:
        forall λa. eq (nat_lt a (suc a)) T
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"lt_suc_self" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      gen_tac >>
      intro_tac >>
      rewrite_tac >>
      refl_tac
    ========================================
    ∀x. nat_lt x (suc x) = T

    Proof Complete!
    with fuel: 64
    |}]

let%expect_test "le_suc_self" =
  let prg =
    {|
    variable a : nat
    theorem le_suc_self:
        forall λa. eq (nat_le a (suc a)) T
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~simp:true ~name:"le_suc_self" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      gen_tac >>
      intro_tac >>
      rewrite_tac >>
      refl_tac
    ========================================
    ∀x. nat_le x (suc x) = T

    Proof Complete!
    with fuel: 64
    |}]

let%expect_test "lt_suc_le" =
  let prg =
    {|
    variable a b : nat
    theorem lt_suc_le:
        forall λa. forall λb. eq (nat_lt a (suc b)) (nat_le a b)
    term b : b
  |}
  in
  let b = Elaborator.term_from_string prg "b" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> auto_dfs_tac >> intros_tac >> simp_tac
    >> with_arbitrary_term b destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> elim_exists_asm_tac >> simp_tac
  in
  run_proof ~simp:true ~name:"lt_suc_le" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      gen_tac >>
      refl_tac
    ========================================
    ∀x. ∀b. nat_lt x (suc b) = nat_le x b

    Proof Complete!
    with fuel: 155
    |}]

let%expect_test "le_lt_suc" =
  let prg =
    {|
    variable a b : nat
    theorem le_lt_suc:
        forall λa. forall λb. eq (nat_le a b) (nat_lt a (suc b))
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~name:"le_lt_suc" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      gen_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac >>
      gen_tac >>
      refl_tac
    ========================================
    ∀x. ∀b. nat_le x b = nat_lt x (suc b)

    Proof Complete!
    with fuel: 117
    |}]

(* (* ===== Group 4: Connection between lt and le ===== *) *)
let%expect_test "not_lt_is_le" =
  let prg =
    {|
    variable a b : nat
    theorem not_lt_is_le:
        forall λa. forall λb. eq (eq (nat_lt a b) F) (nat_le b a)
    term b : b
  |}
  in
  let b = Elaborator.term_from_string prg "b" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> induct_tac >> simp_tac >> eq_true_elim_tac >> refl_tac
    >> intros_tac >> simp_tac >> eq_false_elim_tac >> neg_intro_tac
    >> sym_asm_tac
    >> with_first (with_assumptions rewrite_tac)
    >> truth_tac >> intros_tac >> simp_tac
    >> with_arbitrary_term b destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> eq_true_elim_tac >> refl_tac
    >> elim_exists_asm_tac >> simp_tac
  in
  run_proof ~simp:true ~name:"not_lt_is_le" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_lt x b = F = nat_le b x

    Proof Complete!
    with fuel: 196
    |}]

let%expect_test "equality simp rules" =
  let prg =
    {|
    vartype a
    vartype b 
    variable x y : a
    variable f : a -> b
    variable P : bool

    theorem eq_true_false : eq (eq T F) F
    theorem eq_false_false : eq (eq F F) T
    theorem eq_true_true : eq (eq T T) T
    theorem eq_false_true : eq (eq F T) F
    theorem neg_false_true : eq (neg F) T
    theorem neg_true_false : eq (neg T) F
    theorem eq_cong : 
        forall λf. forall λx. forall λy.
            imp (eq x y) (eq (f x) (f y))
  |}
  in
  let prove_it ?(simp = true) name proof =
    let goal = Elaborator.named_goal_from_string prg name |> Result.get_ok in
    run_proof ~simp ~name ~notrace:true goal proof
  in
  prove_it "eq_true_false"
    (eq_false_elim_tac >> neg_intro_tac
    >> with_assumptions @@ with_flip_rules rewrite_tac
    >> truth_tac);
  prove_it "eq_false_false" (eq_true_elim_tac >> refl_tac);
  prove_it "eq_true_true" (eq_true_elim_tac >> refl_tac);
  prove_it "eq_false_true" (eq_false_elim_tac >> neg_intro_tac >> simp_tac);
  prove_it "neg_false_true" (eq_true_elim_tac >> neg_intro_tac >> false_elim_tac);
  prove_it "neg_true_false"
    (eq_false_elim_tac
    >> with_arbitrary_term t assert_tac
    >> truth_tac >> neg_intro_tac >> neg_elim_tac);
  prove_it ~simp:false "eq_cong" (intros_tac >> simp_tac);

  [%expect
    {|
    ========================================
    T = F = F

    Proof Complete!
    with fuel: 12
    ========================================
    F = F = T

    Proof Complete!
    with fuel: 3
    ========================================
    T = T = T

    Proof Complete!
    with fuel: 3
    ========================================
    F = T = F

    Proof Complete!
    with fuel: 19
    ========================================
    ¬F = T

    Proof Complete!
    with fuel: 7
    ========================================
    ¬T = F

    Proof Complete!
    with fuel: 15
    ========================================
    ∀f. ∀x. ∀y. x = y ==> f x = f y

    Proof Complete!
    with fuel: 21
    |}]

let%expect_test "not_le_is_lt" =
  let prg =
    {|
    variable a b n0 : nat
    theorem not_le_is_lt:
        forall λa. forall λb. eq (eq (nat_le a b) F) (nat_lt b a)

    term b : b
    term n0 : n0
  |}
  in
  let b = Elaborator.term_from_string prg "b" in
  let n0 = Elaborator.term_from_string prg "n0" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> intros_tac >> simp_tac >> intros_tac >> simp_tac
    >> with_arbitrary_term b destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> elim_exists_asm_tac >> simp_tac
    >> with_arbitrary_term n0 destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> elim_exists_asm_tac >> simp_tac
  in
  run_proof ~name:"not_le_is_lt" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le x b = F = nat_lt b x

    Proof Complete!
    with fuel: 257
    |}]

let%expect_test "lt_implies_le" =
  let prg =
    {|
    variable a b a0 : nat
    theorem lt_implies_le:
        forall λa. forall λb. imp (nat_lt a b) (nat_le a b)

    term b : b
    term a0 : a0
  |}
  in
  let b = Elaborator.term_from_string prg "b" in
  let a0 = Elaborator.term_from_string prg "a0" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> auto_dfs_tac >> intros_tac >> simp_tac
    >> with_arbitrary_term b destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> simp_asm_tac >> elim_exists_asm_tac
    >> simp_tac >> simp_asm_tac >> spec_asm_tac a0 >> mp_asm_tac
    >> assumption_tac
  in
  run_proof ~name:"lt_implies_le" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      gen_tac >>
      intro_tac
    ========================================
    ∀x. ∀b. nat_lt x b ==> nat_le x b

    Proof Complete!
    with fuel: 230
    |}]

(* (* ===== Group 5: Transitivity ===== *) *)

let assumption_reasoning_tac =
  try_
    (with_no_automation_trace
       (with_best_first
          (pick_tac
             [
               simp_tac; simp_asm_tac; false_elim_tac; assumption_tac; truth_tac;
             ])))

let%expect_test "lt_trans" =
  let prg =
    {|
    variable a b c n0' n0'' : nat
    theorem lt_trans:
        forall λa. forall λb. forall λc.
            imp (nat_lt a b) (imp (nat_lt b c) (nat_lt a c))
    term a : a
    term b : b
    term c : c
    term n0' : n0'
    term n0'' : n0''
  |}
  in
  let a = Elaborator.term_from_string prg "a" in
  let b = Elaborator.term_from_string prg "b" in
  let c = Elaborator.term_from_string prg "c" in
  let n0' = Elaborator.term_from_string prg "n0'" in
  let n0'' = Elaborator.term_from_string prg "n0''" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_arbitrary_term a induct_tac
    >>> intros_tac
    >>> with_arbitrary_term b induct_tac
    >>> intros_tac
    >>> with_arbitrary_term c induct_tac
    >>> intros_tac
    >>> try_ assumption_reasoning_tac
    (* all subgoals are trivial except the last one *)
    >>= [
          with_repeat
            (with_first (with_proven [ "lt_suc_suc" ] rewrite_asm_tac))
          >> spec_asm_tac n0' >> spec_asm_tac n0''
          >> with_proven [ "lt_suc_suc" ] rewrite_tac
          >> with_repeat mp_asm_tac >> assumption_tac;
        ]
  in
  run_proof ~name:"lt_trans" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀b. ∀c. nat_lt x b ==> nat_lt b c ==> nat_lt x c

    Proof Complete!
    with fuel: 914
    |}]

let%expect_test "le_trans" =
  let prg =
    {|
    variable a b c n0' n0'' : nat
    theorem le_trans:
        forall λa. forall λb. forall λc.
            imp (nat_le a b) (imp (nat_le b c) (nat_le a c))

    term a : a
    term b : b
    term c : c
    term n0' : n0'
    term n0'' : n0''
  |}
  in
  let a = Elaborator.term_from_string prg "a" in
  let b = Elaborator.term_from_string prg "b" in
  let c = Elaborator.term_from_string prg "c" in
  let n0' = Elaborator.term_from_string prg "n0'" in
  let n0'' = Elaborator.term_from_string prg "n0''" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_arbitrary_term a induct_tac
    >>> intros_tac
    >>> with_arbitrary_term b induct_tac
    >>> intros_tac
    >>> with_arbitrary_term c induct_tac
    >>> intros_tac
    >>> try_ assumption_reasoning_tac
    (* all subgoals are trivial except the last one *)
    >>= [
          with_repeat
            (with_first (with_proven [ "le_suc_suc" ] rewrite_asm_tac))
          >> spec_asm_tac n0' >> spec_asm_tac n0''
          >> with_proven [ "le_suc_suc" ] rewrite_tac
          >> with_repeat mp_asm_tac >> assumption_tac;
        ]
  in
  run_proof ~name:"le_trans" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀b. ∀c. nat_le x b ==> nat_le b c ==> nat_le x c

    Proof Complete!
    with fuel: 663
    |}]

let%expect_test "le_lt_trans" =
  let prg =
    {|
    variable a b c n0' n0'' : nat
    theorem le_lt_trans:
        forall λa. forall λb. forall λc.
            imp (nat_le a b) (imp (nat_lt b c) (nat_lt a c))

    term a : a
    term b : b
    term c : c
    term n0' : n0'
    term n0'' : n0''
  |}
  in
  let a = Elaborator.term_from_string prg "a" in
  let b = Elaborator.term_from_string prg "b" in
  let c = Elaborator.term_from_string prg "c" in
  let n0' = Elaborator.term_from_string prg "n0'" in
  let n0'' = Elaborator.term_from_string prg "n0''" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_arbitrary_term a induct_tac
    >>> intros_tac
    >>> with_arbitrary_term b induct_tac
    >>> intros_tac
    >>> with_arbitrary_term c induct_tac
    >>> intros_tac
    >>> try_ assumption_reasoning_tac
    (* all subgoals are trivial except the last one *)
    >>= [
          with_repeat
            (with_first
               (with_proven [ "le_suc_suc"; "lt_suc_suc" ] rewrite_asm_tac))
          >> spec_asm_tac n0' >> spec_asm_tac n0''
          >> with_proven [ "lt_suc_suc" ] rewrite_tac
          >> with_repeat mp_asm_tac >> assumption_tac;
        ]
  in
  run_proof ~name:"le_lt_trans" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀b. ∀c. nat_le x b ==> nat_lt b c ==> nat_lt x c

    Proof Complete!
    with fuel: 900
    |}]

let%expect_test "lt_le_trans" =
  let prg =
    {|
    variable a b c n0' n0'' : nat
    theorem lt_le_trans:
        forall λa. forall λb. forall λc.
            imp (nat_lt a b) (imp (nat_le b c) (nat_lt a c))

    term a : a
    term b : b
    term c : c
    term n0' : n0'
    term n0'' : n0''
  |}
  in
  let a = Elaborator.term_from_string prg "a" in
  let b = Elaborator.term_from_string prg "b" in
  let c = Elaborator.term_from_string prg "c" in
  let n0' = Elaborator.term_from_string prg "n0'" in
  let n0'' = Elaborator.term_from_string prg "n0''" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_arbitrary_term a induct_tac
    >>> intros_tac
    >>> with_arbitrary_term b induct_tac
    >>> intros_tac
    >>> with_arbitrary_term c induct_tac
    >>> intros_tac
    >>> try_ assumption_reasoning_tac
    (* all subgoals are trivial except the last one *)
    >>= [
          with_proven [ "lt_suc_suc" ] rewrite_tac
          >> with_repeat
               (with_first
                  (with_proven [ "lt_suc_suc"; "le_suc_suc" ] rewrite_asm_tac))
          >> spec_asm_tac n0' >> spec_asm_tac n0'' >> with_repeat mp_asm_tac
          >> assumption_tac;
        ]
  in

  run_proof ~name:"lt_le_trans" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀b. ∀c. nat_lt x b ==> nat_le b c ==> nat_lt x c

    Proof Complete!
    with fuel: 870
    |}]

let%expect_test "le_antisym" =
  let prg =
    {|
    variable a b n0': nat
    theorem le_antisym:
        forall λa. forall λb.
            imp (nat_le a b) (imp (nat_le b a) (eq a b))
    term a : a 
    term b : b
    term n0' : n0'
  |}
  in
  let a = Elaborator.term_from_string prg "a" in
  let b = Elaborator.term_from_string prg "b" in
  let n0' = Elaborator.term_from_string prg "n0'" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_arbitrary_term a induct_tac
    >>> intros_tac
    >>> with_arbitrary_term b induct_tac
    >>> intros_tac
    >>> try_ assumption_reasoning_tac
    >> with_proven [ "eq_cong" ] apply_thm_tac
    >> with_repeat (with_first (with_proven [ "le_suc_suc" ] rewrite_asm_tac))
    >> spec_asm_tac n0' >> with_repeat mp_asm_tac >> assumption_tac
  in
  run_proof ~name:"le_antisym" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le x b ==> nat_le b x ==> x = b

    Proof Complete!
    with fuel: 243
    |}]

(* (* ===== Group 6: Subtraction properties ===== *) *)

let%expect_test "le_weaken_suc" =
  let prg =
    {|
    variable a b n0' : nat
    theorem le_weaken_suc :
        forall λa. forall λb.
            imp (nat_le a b) (nat_le a (suc b))
    term a : a
    term b : b
    term n0' : n0'
  |}
  in
  let a = Elaborator.term_from_string prg "a" in
  let b = Elaborator.term_from_string prg "b" in
  let n0' = Elaborator.term_from_string prg "n0'" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_arbitrary_term a induct_tac
    >>> intros_tac
    >>> with_arbitrary_term b induct_tac
    >>> try_ intros_tac
    >>> try_ assumption_reasoning_tac
    >> with_proven [ "le_suc_suc" ] rewrite_tac
    >> spec_asm_tac n0'
    >> with_repeat (with_first (with_proven [ "le_suc_suc" ] rewrite_asm_tac))
    >> with_first mp_asm_tac >> assume_tac
  in
  run_proof ~name:"le_weaken_suc" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le x b ==> nat_le x (suc b)

    Proof Complete!
    with fuel: 334
    |}]

let%expect_test "lt_weaken_suc" =
  let prg =
    {|
    variable a b n0' : nat
    theorem lt_weaken_suc :
        forall λa. forall λb.
            imp (nat_lt a b) (nat_lt a (suc b))
    term a : a
    term b : b
    term n0' : n0'
  |}
  in
  let a = Elaborator.term_from_string prg "a" in
  let b = Elaborator.term_from_string prg "b" in
  let n0' = Elaborator.term_from_string prg "n0'" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_arbitrary_term a induct_tac
    >>> intros_tac
    >>> with_arbitrary_term b induct_tac
    >>> try_ intros_tac
    >>> try_ assumption_reasoning_tac
    >> with_proven [ "lt_suc_suc" ] rewrite_tac
    >> spec_asm_tac n0'
    >> with_repeat (with_first (with_proven [ "lt_suc_suc" ] rewrite_asm_tac))
    >> with_first mp_asm_tac >> assume_tac
  in
  run_proof ~name:"lt_weaken_suc" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_lt x b ==> nat_lt x (suc b)

    Proof Complete!
    with fuel: 412
    |}]

let%expect_test "sub_le" =
  let prg =
    {|
    variable a b c n0' : nat
    theorem sub_le:
        forall λa. forall λb. nat_le (sub a b) a
    term b : b
    term a : a
    term n0' : n0'
  |}
  in
  let a = Elaborator.term_from_string prg "a" in
  let b = Elaborator.term_from_string prg "b" in
  let n0' = Elaborator.term_from_string prg "n0'" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_arbitrary_term a induct_tac
    >>> intros_tac
    >>> with_arbitrary_term b induct_tac
    >>> try_ intros_tac
    >>> try_ assumption_reasoning_tac
    >> with_proven [ "sub_suc_suc" ] rewrite_tac
    >> spec_asm_tac n0'
    >> with_proven [ "le_weaken_suc" ] apply_thm_tac
    >> assumption_tac
  in
  run_proof ~name:"sub_le" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le (sub x b) x

    Proof Complete!
    with fuel: 266
    |}]

let%expect_test "sub_lt" =
  let prg =
    {|
    variable a b a0 n0 : nat
    theorem sub_lt:
        forall λb. forall λa.
            imp (nat_lt zero b)
                (imp (nat_le b a)
                    (nat_lt (sub a b) a))
    term a : a
    term b : b
    term a0 : a0
    term n0 : n0
  |}
  in
  let a = Elaborator.term_from_string prg "a" in
  let b = Elaborator.term_from_string prg "b" in
  let a0 = Elaborator.term_from_string prg "a0" in
  let n0 = Elaborator.term_from_string prg "n0" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_arbitrary_term b induct_tac
    >>> intros_tac >> assumption_reasoning_tac
    >> with_arbitrary_term a destruct_tac
    >> elim_disj_asm_tac >> simp_asm_tac >> simp_tac
    >> with_first assumption_tac >> elim_exists_asm_tac
    >> with_first (with_assumptions rewrite_tac)
    >> with_first (with_assumptions rewrite_tac)
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_proven [ "sub_suc_suc" ] rewrite_tac
    >> with_first (with_proven [ "le_suc_suc" ] rewrite_asm_tac)
    >> with_arbitrary_term n0 destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> elim_exists_asm_tac
    >> with_proven [ "lt_weaken_suc" ] apply_thm_tac
    >> spec_asm_tac a0 >> simp_asm_tac >> simp_tac >> with_repeat mp_asm_tac
    >> assumption_tac
  in
  run_proof ~name:"sub_lt" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀a. nat_lt zero x ==> nat_le x a ==> nat_lt (sub a x) a

    Proof Complete!
    with fuel: 434
    |}]

let%expect_test "sub_add_cancel" =
  let prg =
    {|
    variable a b n0' : nat
    theorem sub_add_cancel:
        forall λa. forall λb.
            imp (nat_le b a)
                (eq (plus (sub a b) b) a)
    term a : a
    term b : b
    term n0' : n0'
  |}
  in
  let a = Elaborator.term_from_string prg "a" in
  let b = Elaborator.term_from_string prg "b" in
  let n0' = Elaborator.term_from_string prg "n0'" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_arbitrary_term a induct_tac
    >>> intros_tac
    >>> with_arbitrary_term b induct_tac
    >>> try_ intros_tac
    >>> try_ assumption_reasoning_tac
    >>= [
          simp_tac
          >> with_proven [ "eq_cong" ] apply_thm_tac
          >> with_proven [ "plus_x_zero" ] rewrite_tac
          >> refl_tac;
          simp_asm_tac >> simp_tac
          >> with_proven [ "plus_suc" ] rewrite_tac
          >> with_proven [ "eq_cong" ] apply_thm_tac
          >> spec_asm_tac n0' >> mp_asm_tac >> assumption_tac;
        ]
  in
  run_proof ~name:"sub_add_cancel" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le b x ==> plus (sub x b) b = x

    Proof Complete!
    with fuel: 507
    |}]

(* (* ===== Group 8: Ordering and addition ===== *) *)

let%expect_test "le_add_r" =
  let prg =
    {|
    variable a b : nat
    theorem le_add_r:
        forall λa. forall λb. nat_le a (plus a b)
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  run_proof ~name:"le_add_r" ~notrace:true goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      gen_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      gen_tac >>
      intro_tac >>
      assumption_tac
    ========================================
    ∀x. ∀b. nat_le x (plus x b)

    Proof Complete!
    with fuel: 116
    |}]

(* (* ===== Group 9: Totality ===== *) *)

let%expect_test "lt_total" =
  let prg =
    {|
    variable a b n0' : nat
    theorem lt_total:
        forall λa. forall λb.
            \/ (nat_lt a b) (nat_le b a)
    term a : a
    term b : b
    term n0' : n0'
  |}
  in
  let a = Elaborator.term_from_string prg "a" in
  let b = Elaborator.term_from_string prg "b" in
  let n0' = Elaborator.term_from_string prg "n0'" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_arbitrary_term a induct_tac
    >>> intros_tac
    >>> with_arbitrary_term b induct_tac
    >>> try_ intros_tac
    >>= [
          right_tac >> simp_tac;
          left_tac >> simp_tac;
          right_tac >> simp_tac;
          spec_asm_tac n0' >> elim_disj_asm_tac >> left_tac
          >> with_proven [ "lt_suc_suc" ] rewrite_tac
          >> assumption_tac >> right_tac
          >> with_proven [ "le_suc_suc" ] rewrite_tac
          >> assumption_tac;
        ]
  in
  run_proof ~name:"lt_total" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_lt x b ∨ nat_le b x

    Proof Complete!
    with fuel: 159
    |}]

let%expect_test "le_total" =
  let prg =
    {|

    variable a b n0' : nat
    theorem le_total:
        forall λa. forall λb.
            \/ (nat_le a b) (nat_le b a)

    term a : a
    term b : b
    term n0' : n0'
  |}
  in
  let a = Elaborator.term_from_string prg "a" in
  let b = Elaborator.term_from_string prg "b" in
  let n0' = Elaborator.term_from_string prg "n0'" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_arbitrary_term a induct_tac
    >>> intros_tac
    >>> with_arbitrary_term b induct_tac
    >>> try_ intros_tac
    >>= [
          right_tac >> simp_tac;
          left_tac >> simp_tac;
          right_tac >> simp_tac;
          spec_asm_tac n0' >> elim_disj_asm_tac >> left_tac
          >> with_proven [ "le_suc_suc" ] rewrite_tac
          >> assumption_tac >> right_tac
          >> with_proven [ "le_suc_suc" ] rewrite_tac
          >> assumption_tac;
        ]
  in
  run_proof ~name:"le_total" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le x b ∨ nat_le b x

    Proof Complete!
    with fuel: 154
    |}]

let%expect_test "div fuel sufficient" =
  let prg =
    {|
    variable a b x n n0 : nat

    variable n a b x x' : nat
    theorem div_fuel_sufficient :
        forall λn.
            forall λa.
                forall λb.
                    imp (nat_lt zero b)
                        (imp (nat_lt a n)
                            (exists λx.
                                (eq (div_aux n a b) (some x))))
    term a : a
    term b : b
    term x : suc x
    term sucx' : suc x'
    term subab : sub a b

    term l1: nat_lt (sub a b) a
    term l2: nat_lt (sub a b) n0
  |}
  in

  let b = Elaborator.term_from_string prg "b" in
  let sucx' = Elaborator.term_from_string prg "sucx'" in
  let l1 = Elaborator.term_from_string prg "l1" in
  let l2 = Elaborator.term_from_string prg "l2" in
  let subab = Elaborator.term_from_string prg "subab" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> intros_tac >> simp_asm_tac >> false_elim_tac >> intros_tac
    >> simp_tac >> cond_tac >> simp_tac
    >> with_arbitrary_term NatTheory.n0 exists_tac
    >> refl_tac >> simp_tac
    >> with_first (with_proven [ "lt_suc_le" ] rewrite_asm_tac)
    >> with_first (with_proven [ "not_lt_is_le" ] rewrite_asm_tac)
    >> (with_arbitrary_term l1 assert_tac
       >> with_proven [ "sub_lt" ] apply_thm_tac
       >> with_first assumption_tac >> with_first assumption_tac)
    >> (with_arbitrary_term l2 assert_tac
       >> with_proven [ "lt_le_trans" ] apply_thm_tac
       >> with_first assumption_tac >> with_first assumption_tac)
    >> spec_asm_tac subab >> spec_asm_tac b >> with_repeat mp_asm_tac
    >> elim_exists_asm_tac >> simp_tac
    >> with_arbitrary_term sucx' exists_tac
    >> simp_tac
  in
  run_proof ~name:"div_fuel_sufficient" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀a. ∀b. nat_lt zero b ==> nat_lt a x ==> ∃x'. div_aux x a b = some x'

    Proof Complete!
    with fuel: 216
    |}]

let%expect_test "div unfold" =
  let prg =
    {|
  variable a b r x x' : nat

  theorem div_unfold:
    forall λa. forall λb.
        imp (nat_lt zero b)
            (eq (div a b)
                (COND (nat_lt a b)
                      zero
                      (suc (div (sub a b) b))))


    term l1: nat_lt (sub a b) a
    term l2 : exists (λx'. eq (div_aux a (sub a b) b) (some x'))
    term l3 : exists (λx. eq (div_aux (suc (sub a b)) (sub a b) b) (some x))
    term l4 : eq (div_aux (plus (suc (sub a b)) (sub a (suc (sub a b)))) (sub a b) b) (some x)
    term arith : eq (plus (sub a (suc (sub a b))) (suc (sub a b))) a
  |}
  in

  let l1 = Elaborator.term_from_string prg "l1" in
  let l2 = Elaborator.term_from_string prg "l2" in
  let l3 = Elaborator.term_from_string prg "l3" in
  let l4 = Elaborator.term_from_string prg "l4" in
  let arith = Elaborator.term_from_string prg "arith" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    intros_tac
    >> with_definition [ "div" ] rewrite_tac
    >> beta_tac
    >> with_first (with_definition [ "div_aux" ] rewrite_tac)
    >> beta_tac >> with_nth_choice 1 cond_tac >> simp_tac
    >> with_repeat @@ with_assumptions rewrite_tac
    >> with_repeat @@ with_proven [ "cond_false" ] rewrite_tac
    >> with_first (with_proven [ "not_lt_is_le" ] rewrite_asm_tac)
    >> with_arbitrary_term l1 assert_tac
    >> with_proven [ "sub_lt" ] apply_thm_tac
    >> with_first assumption_tac >> with_first assumption_tac
    >> with_arbitrary_term l2 assert_tac
    >> with_proven [ "div_fuel_sufficient" ] apply_thm_tac
    >> with_first assumption_tac >> with_first assumption_tac
    >> elim_exists_asm_tac
    >> with_first (with_assumptions rewrite_tac)
    >> with_first (with_definition [ "option_match" ] rewrite_tac)
    >> beta_tac
    >> with_first (with_definition [ "option_match" ] rewrite_tac)
    >> beta_tac
    >> with_arbitrary_term l3 assert_tac
    >> with_proven [ "div_fuel_sufficient" ] apply_thm_tac
    >> with_first assumption_tac
    >> with_proven [ "lt_suc_self" ] rewrite_tac
    >> truth_tac >> elim_exists_asm_tac
    >> with_arbitrary_term l4 assert_tac
    >> with_proven [ "div_fuel_irrel" ] apply_thm_tac
    >> with_first assumption_tac
    >> with_arbitrary_term arith assert_tac
    >> with_proven [ "sub_add_cancel" ] apply_thm_tac
    >> with_proven [ "le_lt_suc" ] rewrite_tac
    >> with_proven [ "lt_suc_suc" ] rewrite_tac
    >> with_first assumption_tac
    >> with_nth_choice 0 @@ with_proven [ "plus_comm" ] rewrite_asm_tac
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_rule
         (OptionTheory.option_def.injective |> List.hd)
         apply_thm_asm_tac
    >> with_nth_term 3 (with_assumptions rewrite_asm_tac)
    >> with_definition [ "div" ] rewrite_tac
    >> beta_tac
    >> with_assumptions rewrite_tac
    >> simp_tac
  in
  run_proof ~name:"div_unfold" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀a. ∀b. nat_lt zero b ==> div a b = COND (nat_lt a b) zero (suc (div (sub a b) b))

    Proof Complete!
    with fuel: 261
    |}]

let%expect_test "merge test" =
  let prg =
    {|
    variable xs ys : list nat

    theorem merge_test:
        eq 
            (merge_aux (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                (cons (suc (suc zero)) (cons (suc (suc (suc (suc zero)))) nil))
                (cons (suc zero) (cons (suc (suc zero)) (cons (suc (suc (suc zero))) nil))))

            (some (cons (suc zero) (cons (suc (suc zero)) (cons (suc (suc zero)) (cons (suc (suc (suc zero))) (cons (suc (suc (suc (suc zero)))) nil))))))
  |}
  in

  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let compute =
    try_
      (with_repeat
         (with_first
            (with_definition
               [ "list_match"; "nat_lt"; "nat_match"; "option_match" ]
               rewrite_tac)))
    >> try_ (with_repeat beta_tac)
    >> try_
         (with_repeat
            (with_first (with_proven [ "cond_false"; "cond_true" ] rewrite_tac)))
    >> try_ (with_repeat beta_tac)
    >> try_ (with_first (with_definition [ "merge_aux" ] rewrite_tac))
    >> try_ (with_repeat beta_tac)
    >> try_ refl_tac
  in
  let proof = with_repeat compute in
  run_proof ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    merge_aux (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (cons (suc (suc zero)) (cons (suc (suc (suc (suc zero)))) nil)) (cons (suc zero) (cons (suc (suc zero)) (cons (suc (suc (suc zero))) nil))) = some (cons (suc zero) (cons (suc (suc zero)) (cons (suc (suc zero)) (cons (suc (suc (suc zero))) (cons (suc (suc (suc (suc zero)))) nil)))))

    Proof Complete!
    with fuel: 828
    |}]

let%expect_test "merge fuel irrel" =
  let prg =
    {|
      variable fuel additional n0 a0' a0  : nat
      variable xs ys x a1 a1' a0'' wit: list nat
      variable m : option (list nat)

      theorem div_fuel_irrel:
        forall λfuel. forall λadditional. 
            forall λxs. forall λys. forall λx.
            imp (eq (merge_aux fuel xs ys) (some x))
                (eq (merge_aux (plus fuel additional) xs ys) (some x))
      term fuel : fuel
      term xs : xs 
      term ys : ys 
      term m: merge_aux n0 a1 (cons a0' a1')
      term n : (merge_aux n0 (cons a0 a1) a1')
      term consa : cons a0' a1'
      term consa2 : cons a0 a1
      term a0'' : a0''
      term a1 : a1
      term a1' : a1'
      term additional : additional
      term wit : wit
  |}
  in

  (* let rw_def r = with_first (with_definition [r] rewrite_tac) >> try_ (with_repeat beta_tac) in *)
  (* let rw_thm r = with_first (with_proven [r] rewrite_tac) in *)
  let fuel = Elaborator.term_from_string prg "fuel" in
  let a0'' = Elaborator.term_from_string prg "a0''" in
  let additional = Elaborator.term_from_string prg "additional" in
  let a1 = Elaborator.term_from_string prg "a1" in
  let a1' = Elaborator.term_from_string prg "a1'" in
  let consa = Elaborator.term_from_string prg "consa" in
  let consa2 = Elaborator.term_from_string prg "consa2" in
  let m = Elaborator.term_from_string prg "m" in
  let n = Elaborator.term_from_string prg "n" in
  let xs = Elaborator.term_from_string prg "xs" in
  let ys = Elaborator.term_from_string prg "ys" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let rw_asm =
    with_first (with_assumptions rewrite_tac)
    >> with_first (with_assumptions rewrite_asm_tac)
  in
  let proof =
    with_arbitrary_term fuel induct_tac
    >> intros_tac >> simp_asm_tac
    >> with_rules OptionTheory.option_def.distinct rewrite_asm_tac
    >> false_elim_tac >> intros_tac
    >> with_arbitrary_term xs destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> simp_asm_tac >> elim_exists_asm_tac
    >> elim_exists_asm_tac
    >> with_proven [ "add_suc_l" ] rewrite_tac
    >> rw_asm
    >> with_arbitrary_term ys destruct_tac
    >> elim_disj_asm_tac
    >> with_first (with_definition [ "merge_aux" ] rewrite_tac)
    >> beta_tac
    >> with_first (with_definition [ "merge_aux" ] rewrite_asm_tac)
    >> beta_tac >> simp_tac >> beta_asm_tac
    >> with_first (with_assumptions rewrite_asm_tac)
    >> simp_asm_tac >> elim_exists_asm_tac >> elim_exists_asm_tac >> rw_asm
    >> with_first (with_definition [ "merge_aux" ] rewrite_tac)
    >> beta_tac
    >> with_first (with_definition [ "merge_aux" ] rewrite_asm_tac)
    >> beta_asm_tac >> simp_tac >> simp_asm_tac >> cond_tac >> rw_asm
    >> with_proven [ "cond_true" ] rewrite_tac
    >> with_proven [ "cond_true" ] rewrite_asm_tac
    >> with_arbitrary_term m destruct_tac
    >> elim_disj_asm_tac >> simp_asm_tac
    >> with_first (with_rules OptionTheory.option_def.distinct rewrite_asm_tac)
    >> false_elim_tac >> elim_exists_asm_tac >> simp_asm_tac
    >> spec_asm_tac additional >> spec_asm_tac a1 >> spec_asm_tac consa
    >> spec_asm_tac a0'' >> with_repeat mp_asm_tac >> simp_tac >> simp_tac
    >> with_first (with_assumptions rewrite_asm_tac)
    >> simp_asm_tac
    >> with_arbitrary_term n destruct_tac
    >> elim_disj_asm_tac >> simp_asm_tac
    >> with_first (with_rules OptionTheory.option_def.distinct rewrite_asm_tac)
    >> false_elim_tac >> elim_exists_asm_tac >> simp_asm_tac
    >> spec_asm_tac additional >> spec_asm_tac consa2 >> spec_asm_tac a1'
    >> spec_asm_tac a0'' >> with_repeat mp_asm_tac >> simp_tac
  in
  run_proof ~name:"merge_fuel_irrel" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀additional. ∀xs. ∀ys. ∀x. merge_aux x xs ys = some x ==> merge_aux (plus x additional) xs ys = some x

    Proof Complete!
    with fuel: 640
    |}]

let%expect_test "merge fuel sufficient" =
  let prg =
    {|
    variable fuel a0 a0': nat
    variable xs ys x a1 a1' x' : list nat
    
    theorem merge_fuel_sufficient :
        forall λfuel.
            forall λxs. forall λys.
                        imp (nat_lt (plus (length xs) (length ys)) fuel)
                            (exists λx.
                                (eq (merge_aux fuel xs ys) (some x)))
    term xs : xs
    term ys : ys
    term consa01 :  (cons a0 a1) 
    term consa01' :  (cons a0' a1') 
    term a1 : a1
    term a1' : a1'
    term x : x
    term wit : (cons a0 x')
    term wit2 :  (cons a0' x')

  |}
  in

  let xs = Elaborator.term_from_string prg "xs" in
  let ys = Elaborator.term_from_string prg "ys" in
  let wit = Elaborator.term_from_string prg "wit" in
  let wit2 = Elaborator.term_from_string prg "wit2" in
  let a1 = Elaborator.term_from_string prg "a1" in
  let a1' = Elaborator.term_from_string prg "a1'" in
  let consa01 = Elaborator.term_from_string prg "consa01" in
  let consa01' = Elaborator.term_from_string prg "consa01'" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> intros_tac >> simp_asm_tac >> false_elim_tac >> intros_tac
    >> simp_tac
    >> with_arbitrary_term xs destruct_tac
    >> elim_disj_asm_tac >> simp_tac
    >> with_arbitrary_term ys exists_tac
    >> refl_tac
    >> with_repeat elim_exists_asm_tac
    >> simp_tac
    >> with_arbitrary_term ys destruct_tac
    >> elim_disj_asm_tac >> simp_tac
    >> with_arbitrary_term consa01 exists_tac
    >> refl_tac
    >> with_repeat elim_exists_asm_tac
    >> simp_tac >> cond_tac >> simp_tac
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_proven [ "length_cons" ] rewrite_asm_tac
    >> with_proven [ "add_suc_l" ] rewrite_asm_tac
    >> with_proven [ "lt_suc_suc" ] rewrite_asm_tac
    >> spec_asm_tac a1 >> spec_asm_tac consa01' >> mp_asm_tac
    >> elim_exists_asm_tac >> simp_tac
    >> with_arbitrary_term wit exists_tac
    >> refl_tac >> simp_tac
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_proven [ "plus_comm" ] rewrite_asm_tac
    >> with_proven [ "length_cons" ] rewrite_asm_tac
    >> with_proven [ "add_suc_l" ] rewrite_asm_tac
    >> with_proven [ "plus_comm" ] rewrite_asm_tac
    >> with_proven [ "lt_suc_suc" ] rewrite_asm_tac
    >> spec_asm_tac consa01 >> spec_asm_tac a1' >> mp_asm_tac
    >> elim_exists_asm_tac >> simp_tac
    >> with_arbitrary_term wit2 exists_tac
    >> refl_tac
  in
  run_proof ~name:"merge_fuel_sufficient" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀xs. ∀ys. nat_lt (plus (length xs) (length ys)) x ==> ∃x. merge_aux x xs ys = some x

    Proof Complete!
    with fuel: 404
    |}]

(*
what we want
    def merge : list nat -> list nat -> list nat
        | nil => λys. ys
        | cons h t =>
            list_match ys
                (cons h t)
                (λy'. λys'. 
                    COND (nat_lt h 'y)
                        (cons h (merge t (cons y' ys')))
                        (cons 'y (merge (cons h t) ys')))

 *)
let%expect_test "merge unfolding lemma" =
  let prg =
    {|
  variable fuel : nat
  variable h y' a0 a0' : nat
  variable xs ys x t ys' a1 a1' witness : list nat

  theorem merge_unfold:
    forall λxs. forall λys.
            (eq (merge xs ys)
                (list_match xs
                    (ys)
                    (λh. λt. 
                        (list_match ys
                            (cons h t)
                            (λy'. λys'.
                                COND (nat_lt h y')
                                    (cons h (merge t (cons y' ys')))
                                    (cons y' (merge (cons h t) ys')))))))
    term xs : xs
    term ys : ys
    term suf : exists (λx. eq  (merge_aux (suc (plus (length a1') (suc (length a1)))) a1' (cons a0 a1)) (some x))
    term suf2 : exists (λx. eq  (merge_aux (suc (plus (length a1') (suc (length a1)))) (cons a0' a1') a1) (some x))

    |}
  in

  let xs = Elaborator.term_from_string prg "xs" in
  let suf = Elaborator.term_from_string prg "suf" in
  let suf2 = Elaborator.term_from_string prg "suf2" in
  let ys = Elaborator.term_from_string prg "ys" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    intros_tac
    >> with_arbitrary_term xs destruct_tac
    >> with_arbitrary_term ys destruct_tac
    >> with_repeat elim_disj_asm_tac
    >> simp_tac
    >> with_repeat elim_exists_asm_tac
    >> simp_tac
    >> with_repeat elim_exists_asm_tac
    >> simp_tac
    >> with_repeat elim_exists_asm_tac
    >> with_definition [ "merge" ] rewrite_tac
    >> beta_tac
    >> with_first (with_definition [ "merge_aux" ] rewrite_tac)
    >> with_repeat (with_first (with_assumptions rewrite_tac))
    >> simp_tac ~exclude:[ "merge"; "merge_aux" ]
    >> cond_tac
    >> simp_tac ~exclude:[ "merge"; "merge_aux" ]
    >> with_arbitrary_term suf assert_tac
    >> with_proven [ "merge_fuel_sufficient" ] apply_thm_tac
    >> simp_tac >> elim_exists_asm_tac
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac ~exclude:[ "merge"; "merge_aux" ]
    >> with_definition [ "merge" ] rewrite_tac
    >> beta_tac
    >> with_proven [ "length_cons" ] rewrite_tac
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac
    >> simp_tac ~exclude:[ "merge"; "merge_aux" ]
    >> with_arbitrary_term suf2 assert_tac
    >> with_proven [ "merge_fuel_sufficient" ] apply_thm_tac
    >> simp_tac
    >> with_proven [ "plus_suc" ] rewrite_tac
    >> simp_tac >> elim_exists_asm_tac
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac ~exclude:[ "merge"; "merge_aux" ]
    >> with_definition [ "merge" ] rewrite_tac
    >> beta_tac
    >> with_proven [ "length_cons" ] rewrite_tac
    >> with_first (with_proven [ "plus_suc" ] rewrite_asm_tac)
    >> with_first (with_proven [ "plus_comm" ] rewrite_tac)
    >> with_first (with_proven [ "plus_suc" ] rewrite_tac)
    >> with_first (with_proven [ "plus_comm" ] rewrite_tac)
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac
  in
  run_proof ~name:"merge_unfold" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀xs. ∀ys. merge xs ys = list_match xs ys (λh. λt. list_match ys (cons h t) (λy'. λys'. COND (nat_lt h y') (cons h (merge t (cons y' ys'))) (cons y' (merge (cons h t) ys'))))

    Proof Complete!
    with fuel: 1197
    |}]

(* sort [3,1,2] = [1,2,3] *)
let%expect_test "merge sort [3,1,2] = [1,2,3]" =
  let prg =
    {|
    theorem isort_test : eq
      (merge_sort_aux (suc (suc (suc (suc (suc ( suc (suc (suc zero)))))))) (cons (suc (suc (suc zero))) (cons (suc zero) (cons (suc (suc zero)) nil))))
      (some (cons (suc zero) (cons (suc (suc zero)) (cons (suc (suc (suc zero))) nil))))
  |}
  in

  let rw_def r =
    with_first (with_definition [ r ] rewrite_tac)
    >> try_ (with_repeat beta_tac)
  in
  let rw_thm r =
    with_first (with_proven [ r ] rewrite_tac) >> try_ (with_repeat beta_tac)
  in
  let exclude =
    [
      "merge_sort_aux";
      "merge";
      "merge_aux";
      "div";
      "div_aux";
      "merge_unfold";
      "div_unfold";
    ]
  in
  let proof =
    rw_def "merge_sort_aux" >> simp_tac ~exclude
    >> with_repeat @@ rw_def "div"
    >> with_repeat @@ rw_def "div_aux"
    >> simp_tac ~exclude >> rw_def "merge_sort_aux" >> simp_tac ~exclude
    >> rw_def "merge_sort_aux" >> simp_tac ~exclude
    >> with_repeat @@ rw_def "div"
    >> with_repeat @@ rw_def "div_aux"
    >> simp_tac ~exclude >> rw_def "merge_sort_aux" >> simp_tac ~exclude
    >> rw_def "merge_sort_aux" >> simp_tac ~exclude >> rw_thm "merge_unfold"
    >> simp_tac ~exclude >> rw_thm "merge_unfold" >> simp_tac ~exclude
    >> rw_thm "merge_unfold" >> simp_tac ~exclude >> rw_thm "merge_unfold"
    >> simp_tac ~exclude >> rw_thm "merge_unfold" >> simp_tac ~exclude
    >> rw_thm "merge_unfold" >> simp_tac ~exclude
  in

  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof ~pretty:true ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    merge_sort_aux 8 [3, 1, 2] = some [1, 2, 3]

    Proof Complete!
    with fuel: 1371
    |}]

let%expect_test "length take" =
  let prg =
    {|
    variable n : nat
    variable xs n1 : list nat

    theorem length_take :
        forall λn. forall λxs.
            eq (length (take n xs)) (COND (nat_lt n (length xs)) n (length xs))

    theorem length_drop :
    forall λn. forall λxs.
        eq (length (drop n xs)) (sub (length xs) n)

    term n : n
    term xs : xs
    term n1 : n1
  |}
  in

  let n = Elaborator.term_from_string prg "n" in
  let n1 = Elaborator.term_from_string prg "n1" in
  let xs = Elaborator.term_from_string prg "xs" in
  let gtake =
    Elaborator.named_goal_from_string prg "length_take" |> Result.get_ok
  in
  let gdrop =
    Elaborator.named_goal_from_string prg "length_drop" |> Result.get_ok
  in
  let proof =
    with_arbitrary_term n induct_tac
    >>> try_ intros_tac
    >>> with_arbitrary_term xs induct_tac
    >>> try_ intros_tac
    >>> try_ assumption_reasoning_tac
    >> with_repeat
         (with_first (with_definition [ "take"; "length" ] rewrite_tac))
    >> beta_tac
    >> with_repeat (with_first (with_definition [ "list_match" ] rewrite_tac))
    >> beta_tac
    >> with_first (with_definition [ "length" ] rewrite_tac)
    >> spec_asm_tac n1
    >> with_assumptions rewrite_tac
    >> with_first (with_proven [ "lt_suc_suc" ] rewrite_tac)
    >> cond_tac >> simp_tac >> simp_tac
  in
  run_proof ~name:"length_take" ~notrace:true gtake proof;
  run_proof ~name:"length_drop" ~notrace:true gdrop proof;
  [%expect
    {|
    ========================================
    ∀x. ∀xs. length (take x xs) = COND (nat_lt x (length xs)) x (length xs)

    Proof Complete!
    with fuel: 571
    ========================================
    ∀x. ∀xs. length (drop x xs) = sub (length xs) x

    Proof Complete!
    with fuel: 241
    |}]

let%expect_test "div pos and lt" =
  let prg =
    {|

    variable n m k n0 a0 n0' : nat

    theorem div_pos :
        forall λn.
            imp (nat_lt (suc zero) n)
                (nat_lt zero (div n (suc (suc zero))))

    theorem div_le : 
        forall λn.
        forall λk.
            forall λm.
            imp (nat_lt zero m) 
                (imp
                    (nat_le k n)
                    (nat_le (div k m) n)
                )

    theorem div_lt :
        forall λn.
            imp (nat_lt (suc zero) n)
                (nat_lt (div n (suc (suc zero))) n)
    term n : n
    term m : m
    term n0 : n0
    term a0 : a0
    term n0' : n0'

    term ltkm : nat_lt k m
    term subkm : sub k m
    term subkmlen0 : nat_le (sub k m) n0
    term subltkmk : nat_lt (sub k m) k
    term subltkm_sucn0: nat_lt (sub k m) (suc n0)

    term div_unfld : (eq (div (suc n0) (suc (suc zero)))
                        (COND (nat_lt (suc n0) (suc (suc zero)))
                              zero
                              (suc (div (sub (suc n0) (suc (suc zero))) (suc (suc zero))))))

    term div_unfld2 : (eq (div (suc (suc a0)) (suc (suc zero)))
                        (COND (nat_lt (suc (suc a0)) (suc (suc zero)))
                              zero
                              (suc (div (sub (suc (suc a0)) (suc (suc zero))) (suc (suc zero))))))

    term div_unfld3 : (eq (div k m)
                        (COND (nat_lt k m)
                              zero
                              (suc (div (sub k m) m))))


  |}
  in

  let n = Elaborator.term_from_string prg "n" in
  let m = Elaborator.term_from_string prg "m" in
  let ltkm = Elaborator.term_from_string prg "ltkm" in
  let subkm = Elaborator.term_from_string prg "subkm" in
  let subkmlen0 = Elaborator.term_from_string prg "subkmlen0" in
  let subltkmk = Elaborator.term_from_string prg "subltkmk" in
  let subltkm_sucn0 = Elaborator.term_from_string prg "subltkm_sucn0" in

  let n0 = Elaborator.term_from_string prg "n0" in
  let a0 = Elaborator.term_from_string prg "a0" in
  let div_unfld = Elaborator.term_from_string prg "div_unfld" in
  let div_unfld2 = Elaborator.term_from_string prg "div_unfld2" in
  let div_unfld3 = Elaborator.term_from_string prg "div_unfld3" in
  let gpos = Elaborator.named_goal_from_string prg "div_pos" |> Result.get_ok in
  let gle = Elaborator.named_goal_from_string prg "div_le" |> Result.get_ok in
  let glt = Elaborator.named_goal_from_string prg "div_lt" |> Result.get_ok in

  let proof =
    with_arbitrary_term n induct_tac
    >>> intros_tac
    >>> try_ assumption_reasoning_tac
    >> with_arbitrary_term div_unfld assert_tac
    >> with_first (with_proven [ "div_unfold" ] apply_thm_tac)
    >> simp_tac
    >> with_assumptions rewrite_tac
    >> cond_tac >> simp_asm_tac
    >> with_first eq_true_elim_asm_tac
    >> with_first (with_proven [ "le_zero_eq" ] apply_thm_asm_tac)
    >> simp_asm_tac >> false_elim_tac
    >> with_assumptions rewrite_tac
    >> with_proven [ "cond_false" ] rewrite_tac
    >> simp_tac ~exclude:[ "div" ]
  in
  run_proof ~name:"div_pos" ~notrace:true gpos proof;

  let proof =
    with_arbitrary_term n induct_tac
    >> intros_tac
    >> with_first (with_proven [ "le_zero_eq" ] apply_thm_asm_tac)
    >> simp_tac
    >> with_arbitrary_term m destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> elim_exists_asm_tac >> simp_tac
    >> intros_tac
    >> with_arbitrary_term ltkm cases_tac
    >> with_arbitrary_term div_unfld3 assert_tac
    >> with_first (with_proven [ "div_unfold" ] apply_thm_tac)
    >> with_first assumption_tac
    >> with_first (with_assumptions rewrite_tac)
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac
    >> with_arbitrary_term div_unfld3 assert_tac
    >> with_first (with_proven [ "div_unfold" ] apply_thm_tac)
    >> with_first assumption_tac
    >> with_first (with_assumptions rewrite_tac)
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac ~exclude:[ "div"; "div_unfold" ]
    >> with_arbitrary_term subkmlen0 assert_tac
    >> with_first (with_proven [ "not_lt_is_le" ] rewrite_asm_tac)
    >> with_arbitrary_term subltkmk assert_tac
    >> with_proven [ "sub_lt" ] apply_thm_tac
    >> with_first assumption_tac >> with_first assumption_tac
    >> with_arbitrary_term subltkm_sucn0 assert_tac
    >> with_proven [ "lt_le_trans" ] apply_thm_tac
    >> with_first assumption_tac >> with_first assumption_tac
    >> with_first
         (with_proven [ "lt_suc_le" ]
            (with_info_trace (with_flip_rules rewrite_tac)))
    >> with_first assumption_tac >> spec_asm_tac subkm >> spec_asm_tac m
    >> with_repeat mp_asm_tac >> with_first assumption_tac
  in
  run_proof ~name:"div_le" ~notrace:true gle proof;

  let proof =
    with_arbitrary_term n induct_tac
    >> intros_tac >> assumption_reasoning_tac >> intros_tac
    >> with_arbitrary_term n0 destruct_tac
    >> elim_disj_asm_tac >> simp_tac
    >> with_repeat elim_exists_asm_tac
    >> with_repeat (with_assumptions (with_first rewrite_tac))
    >> with_repeat (with_assumptions (with_first rewrite_asm_tac))
    >> with_arbitrary_term div_unfld2 assert_tac
    >> with_first (with_proven [ "div_unfold" ] apply_thm_tac)
    >> simp_tac
    >> with_arbitrary_term a0 destruct_tac
    >> elim_disj_asm_tac >> simp_tac
    >> with_repeat elim_exists_asm_tac
    >> with_repeat (with_first (with_assumptions rewrite_asm_tac))
    >> with_repeat (with_first (with_proven [ "lt_suc_suc" ] rewrite_asm_tac))
    >> with_first
         (with_nth_term 0 (with_definition [ "nat_lt" ] rewrite_asm_tac))
    >> beta_asm_tac
    >> with_first
         (with_nth_term 0 (with_definition [ "nat_match" ] rewrite_asm_tac))
    >> try_ beta_asm_tac
    >> with_first
         (with_nth_term 0 (with_proven [ "cond_false" ] rewrite_asm_tac))
    >> try_ beta_asm_tac
    >> with_first (with_assumptions rewrite_tac)
    >> with_first (with_assumptions rewrite_tac)
    >> with_proven [ "lt_suc_suc" ] rewrite_tac
    >> simp_tac ~exclude:[ "nat_lt"; "div" ]
    >> with_repeat (with_assumptions (with_flip_rules (with_first rewrite_tac)))
    >> with_proven [ "div_le" ] apply_thm_tac
    >> simp_tac >> simp_tac
  in
  run_proof ~pretty:true ~name:"div_lt" ~notrace:true glt proof;
  [%expect
    {|
    ========================================
    ∀x. nat_lt (suc zero) x ==> nat_lt zero (div x (suc (suc zero)))

    Proof Complete!
    with fuel: 764
    ========================================
    ∀x. ∀k. ∀m. nat_lt zero m ==> nat_le k x ==> nat_le (div k m) x

    Proof Complete!
    with fuel: 346
    ========================================
    ∀x. nat_lt 1 x ==> nat_lt (div x 2) x

    Proof Complete!
    with fuel: 564
    |}]

let%expect_test "template" =
  let prg =
    {|
    variable P : bool

    theorem p_true_intro : forall λP. imp P (eq P T)
  |}
  in

  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = intros_tac >> eq_true_elim_tac >> assumption_tac in
  run_proof ~name:"eq_true_intro" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀P. P ==> P = T

    Proof Complete!
    with fuel: 8
    |}]

let%expect_test "merge sort sufficient" =
  let prg =
    {|
    variable fuel n0 : nat
    variable xs x x' x'' : list nat

    theorem merge_sort_fuel_sufficient:
        forall λfuel.
            forall λxs.
                imp (nat_lt (length xs) fuel)
                    (exists λx.
                        (eq (merge_sort_aux fuel xs) (some x)))

    term xs : xs
    term left :  (take (div (length xs) (suc (suc zero))) xs)
    term right : (drop (div (length xs) (suc (suc zero))) xs)

    term right_oblig : nat_lt (length (drop (div (length xs) (suc (suc zero))) xs)) n0
    term left_oblig :  nat_lt (length (take (div (length xs) (suc (suc zero))) xs)) n0

    term sub1 : nat_lt (sub (length xs) (div (length xs) (suc (suc zero)))) (length xs)
    term wit :  merge x' x''
  |}
  in

  let xs = Elaborator.term_from_string prg "xs" in
  let wit = Elaborator.term_from_string prg "wit" in
  let sub1 = Elaborator.term_from_string prg "sub1" in
  let left = Elaborator.term_from_string prg "left" in
  let right = Elaborator.term_from_string prg "right" in
  let left_oblig = Elaborator.term_from_string prg "left_oblig" in
  let right_oblig = Elaborator.term_from_string prg "right_oblig" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> intros_tac >> simp_asm_tac >> false_elim_tac >> intros_tac
    >> with_first (with_definition [ "merge_sort_aux" ] rewrite_tac)
    >> beta_tac >> cond_tac
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac ~exclude:[ "merge_sort_aux"; "take"; "drop"; "div"; "merge" ]
    >> with_arbitrary_term xs exists_tac
    >> refl_tac
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac ~exclude:[ "merge_sort_aux"; "take"; "drop"; "div"; "merge" ]
    >> spec_asm_tac left >> spec_asm_tac right
    >> (with_arbitrary_term left_oblig assert_tac
       >> with_first (with_proven [ "not_le_is_lt" ] rewrite_asm_tac)
       >> with_first (with_proven [ "div_lt" ] apply_thm_asm_tac)
       >> with_proven [ "length_take" ] rewrite_tac
       >> with_nth_term 0 (with_proven [ "eq_true_intro" ] apply_thm_asm_tac)
       >> with_assumptions rewrite_tac
       >> simp_tac ~exclude:[ "div" ]
       >> with_first (with_proven [ "lt_suc_le" ] rewrite_asm_tac)
       >> with_first (with_proven [ "lt_le_trans" ] apply_thm_tac)
       >> with_first (with_assumptions rewrite_tac)
       >> truth_tac >> with_first assumption_tac)
    >> (with_arbitrary_term right_oblig assert_tac
       >> with_first (with_proven [ "not_le_is_lt" ] rewrite_asm_tac)
       >> with_first (with_proven [ "div_pos" ] apply_thm_asm_tac)
       >> with_proven [ "length_drop" ] rewrite_tac
       >> with_arbitrary_term sub1 assert_tac
       >> with_first (with_proven [ "sub_lt" ] apply_thm_tac)
       >> with_first assumption_tac
       >> with_proven [ "div_le" ] apply_thm_tac
       >> simp_tac >> simp_tac
       >> with_first (with_proven [ "lt_suc_le" ] rewrite_asm_tac)
       >> with_first (with_proven [ "lt_le_trans" ] apply_thm_tac)
       >> with_first assumption_tac >> with_first assumption_tac
       >> with_repeat (with_first mp_asm_tac)
       >> with_repeat elim_exists_asm_tac
       >> simp_tac ~exclude:[ "div"; "merge" ]
       >> with_arbitrary_term wit exists_tac
       >> refl_tac)
  in
  run_proof ~name:"merge_sort_fuel_sufficient" ~pretty:true ~notrace:true goal
    proof;
  [%expect
    {|
    ========================================
    ∀x. ∀xs. nat_lt (length xs) x ==> ∃x. merge_sort_aux x xs = some x

    Proof Complete!
    with fuel: 300
    |}]
