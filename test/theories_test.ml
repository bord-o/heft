open Heft
open Kernel
open Derived
open Tactic
open Theories

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
    with fuel: 71
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
    with fuel: 53
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
    with fuel: 60
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
  run_proof goal proof;

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
    with fuel: 151
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
    with fuel: 138
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
    with fuel: 103
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
    with fuel: 89
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
    with fuel: 119
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
    with fuel: 172
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
    with fuel: 102
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
    with fuel: 126
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
    with fuel: 161
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
    with fuel: 150
    |}]

let%expect_test "sort correct lemma" =
  let prg =
    {|
    variable n : nat
    variable l : list nat
    theorem insert_sorted:
        forall λl. forall λn.
            imp (sorted l)
                (sorted (insert l n))
    |}
  in
  let le =
    Elaborator.term_from_string
      {|
      variable n0' n : nat
      term le : nat_le n0' n
      |}
      "le"
  in
  let n1 =
    Elaborator.term_from_string
      {|
      variable n1 : list nat
      term n1 : n1
      |}
      "n1"
  in
  let n0 =
    Elaborator.term_from_string
      {|
      variable n0 : nat
      term n0 : n0
      |}
      "n0"
  in

  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac  >>= [

        intros_tac >> simp_tac >> auto_dfs_tac ;
        intros_tac >> simp_tac >> cond_tac
        >> with_assumptions rewrite_tac
        >> simp_tac >> conj_tac
        >> with_arbitrary_term n1 destruct_tac
        >> induct_tac >> intros_tac >> simp_tac >> truth_tac >> intros_tac
        >> simp_tac >> with_repeat mp_asm_tac
        >> with_arbitrary_term le cases_tac
        >> simp_tac >> simp_asm_tac >> elim_conj_asm_tac >> assumption_tac
        >> simp_tac >> truth_tac
        >> spec_asm_tac (make_var "n" NatTheory.nat_ty)
        >> apply_asm_tac >> simp_asm_tac >> elim_conj_asm_tac
        >> with_first assumption_tac >> simp_tac >> conj_tac
        >> with_proven [ "nat_le_flip" ] apply_thm_asm_tac
        >> simp_tac >> truth_tac >> conj_tac
        >> with_arbitrary_term n1 destruct_tac
        >> induct_tac >> intros_tac >> simp_tac >> truth_tac >> intros_tac
        >> simp_tac >> with_repeat mp_asm_tac >> simp_asm_tac >> elim_conj_asm_tac
        >> assumption_tac >> spec_asm_tac n0 >> simp_asm_tac >> elim_conj_asm_tac
        >> with_first assumption_tac
    ]
  in

  run_proof ~notrace:true ~name:"sort_correct_lemma" goal proof;

  [%expect
    {|
    Proof:
      conj_tac
    ∀n0. ∀n1. (∀n. sorted n1 ==> sorted (insert n1 n)) ==> ∀n. sorted (cons n0 n1) ==> sorted (insert (cons n0 n1) n)
    ========================================
    ∀x. ∀n. sorted x ==> sorted (insert x n)

    Proof Complete!
    with fuel: 621
    |}]

(* let%expect_test "sort correct lemma" = *)
(*   let prg = *)
(*     {| *)
(*   variable n : nat *)
(*   variable l : list nat *)
(*   theorem insert_sorted: *)
(*       forall λl. forall λn. *)
(*           imp (eq (sorted l) T) *)
(*               (eq (sorted (insert l n)) T) *)
(*   |} *)
(*   in *)
(*   let goal = ([], List.hd (Elaborator.goals_from_string prg)) in *)
(*   let proof = *)
(*     induct_tac >> induct_tac >> auto_dfs_tac >> auto_dfs_tac >> intros_tac *)
(*     >> simp_asm_tac ~with_asms:false *)
(*     >> simp_tac *)
(*   in *)
(*   run_proof ~name:"sort_correct_lemma" goal proof; *)
(**)
(*   [%expect {| *)
(*     |}] *)

(* let%expect_test "sort correct" = *)
(*   let prg = *)
(*     {| *)
(*     variable l : list nat *)
(*     theorem sort_correct:  *)
(*         forall λl. *)
(*             eq (sorted (isort l)) T *)
(**)
(*   |} *)
(*   in *)
(*   let goal = ([], List.hd (Elaborator.goals_from_string prg)) in *)
(*   let proof = simp_tac in *)
(*   run_proof goal proof; *)
(**)
(*   [%expect {| *)
(*     |}] *)
