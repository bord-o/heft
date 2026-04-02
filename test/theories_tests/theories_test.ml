open Heft
open Kernel
open Derived
open Tactic
open Heft_theories
open Theories

let%expect_test "template" =
  let goal = ([], [%term forall (fun (a : nat) -> true)]) in
  run_proof ~notrace:true goal (intros_tac >> truth_tac);
  [%expect
    {|
    ========================================
    ∀a. T

    Proof Complete!
    with fuel: 5
    |}]

let%expect_test "rewrite induction" =
  let goal = ([], [%term forall (fun (x : nat) -> plus x zero = x)]) in
  run_proof ~name:"plus_x_zero" goal
    (induct_tac >> simp_tac >> gen_tac >> intro_tac >> simp_tac);

  [%expect
    {|
    ========================================
    ∀x. plus x zero = x

    Proof Complete!
    with fuel: 53
    |}]

let%expect_test "basic nat" =
  let goal = ([], [%term plus 2n 3n = 5n]) in
  run_proof ~pretty:true goal simp_tac;

  [%expect
    {|
    ========================================
    plus 2 3 = 5

    Proof Complete!
    with fuel: 29
    |}]

let%expect_test "plus assoc" =
  let goal =
    ( [],
      [%term
        forall (fun (x : nat) (y : nat) (z : nat) ->
            plus x (plus y z) = plus (plus x y) z)] )
  in
  run_proof ~name:"plus_assoc" goal
    (with_term x induct_tac >> intros_tac >> simp_tac >> intros_tac >> simp_tac);
  [%expect
    {|
    ========================================
    ∀x. ∀y. ∀z. plus x (plus y z) = plus (plus x y) z

    Proof Complete!
    with fuel: 88
    |}]

let%expect_test "suc injective" =
  let goal =
    ([], [%term forall (fun (x : nat) (y : nat) -> suc x = suc y ==> (x = y))])
  in
  run_proof ~name:"suc_inj" goal
    (intros_tac
    >> (apply_thm_tac |> with_rules NatTheory.nat_def.injective)
    >> assumption_tac);

  [%expect
    {|
    ========================================
    ∀x. ∀y. suc x = suc y ==> x = y

    Proof Complete!
    with fuel: 13
    |}]

(* Lemma needed for commutativity: plus x (Suc y) = Suc (plus x y) *)
let%expect_test "plus suc lemma" =
  let goal =
    ( [],
      [%term
        forall (fun (x : nat) (y : nat) -> plus x (suc y) = suc (plus x y))] )
  in
  run_proof ~name:"plus_suc" goal
    (induct_tac >> gen_tac >> simp_tac >> intros_tac >> simp_tac);
  [%expect
    {|
    ========================================
    ∀x. ∀y. plus x (suc y) = suc (plus x y)

    Proof Complete!
    with fuel: 69
    |}]

let%expect_test "suc injective rev" =
  let goal =
    ([], [%term forall (fun (x : nat) (y : nat) -> x = y ==> (suc x = suc y))])
  in
  run_proof ~name:"suc_inj_rev" goal
    (intros_tac >> (rewrite_tac |> with_assumptions) >> refl_tac);
  [%expect
    {|
    ========================================
    ∀x. ∀y. x = y ==> suc x = suc y

    Proof Complete!
    with fuel: 13
    |}]

(* Commutativity: plus x y = plus y x *)
let%expect_test "plus comm" =
  let goal =
    ([], [%term forall (fun (x : nat) (y : nat) -> plus x y = plus y x)])
  in
  run_proof ~name:"plus_comm" goal
    (induct_tac >> gen_tac >> simp_tac
    >> with_first (with_proven [ "plus_x_zero" ] rewrite_tac)
    >> refl_tac >> intros_tac >> simp_tac >> sym_tac
    >> with_first (with_proven [ "plus_suc" ] apply_thm_tac));

  [%expect
    {|
    ========================================
    ∀x. ∀y. plus x y = plus y x

    Proof Complete!
    with fuel: 73
    |}]

let%expect_test "cancellation" =
  let goal =
    ( [],
      [%term
        forall (fun (x : nat) (y : nat) (z : nat) ->
            plus x y = plus x z ==> (y = z))] )
  in
  run_proof goal
    (induct_tac >> simp_tac >> intros_tac >> assumption_tac >> intros_tac
   >> simp_asm_tac
    >> with_first (with_proven [ "suc_inj" ] apply_thm_asm_tac)
    >> with_first (with_assumptions apply_thm_asm_tac)
    >> assumption_tac);
  [%expect
    {|
    ========================================
    ∀x. ∀y. ∀z. plus x y = plus x z ==> y = z

    Proof Complete!
    with fuel: 88
    |}]

let%expect_test "cancellation rev" =
  let goal =
    ( [],
      [%term
        forall (fun (x : nat) (y : nat) (z : nat) ->
            plus y x = plus z x ==> (y = z))] )
  in
  run_proof goal
    (induct_tac >> gen_tac
    >> with_proven [ "plus_x_zero" ] simp_tac
    >> intros_tac >> assumption_tac >> intros_tac
    >> with_proven [ "plus_suc" ] rewrite_asm_tac
    >> with_proven [ "plus_suc" ] rewrite_asm_tac
    >> with_proven [ "suc_inj" ] apply_thm_asm_tac
    >> with_first (with_assumptions apply_thm_tac)
    >> assumption_tac);

  [%expect
    {|
    ========================================
    ∀x. ∀y. ∀z. plus y x = plus z x ==> y = z

    Proof Complete!
    with fuel: 65
    |}]

(* xs = Nil ==> length xs = Zero *)
let%expect_test "nil_implies_length_zero" =
  let goal =
    ([], [%term forall (fun (xs : 'a list) -> xs = nil ==> (length xs = zero))])
  in
  run_proof goal (intros_tac >> simp_tac ~with_asms:true);

  [%expect
    {|
    ========================================
    ∀xs. xs = nil ==> length xs = zero

    Proof Complete!
    with fuel: 22
    |}]

(* length xs = Zero ==> xs = Nil *)
let%expect_test "length_zero_implies_nil" =
  let goal =
    ([], [%term forall (fun (xs : 'a list) -> length xs = zero ==> (xs = nil))])
  in
  run_proof goal
    (induct_tac >> intros_tac >> refl_tac >> intros_tac >> simp_asm_tac
   >> sym_asm_tac
    >> with_first (with_rules NatTheory.nat_def.distinct rewrite_asm_tac)
    >> false_elim_tac);
  [%expect
    {|
    ========================================
    ∀x. length x = zero ==> x = nil

    Proof Complete!
    with fuel: 40
    |}]

let%expect_test "append nil xs = xs" =
  let goal =
    make_goal [%term forall (fun (xs : 'a list) -> append nil xs = xs)]
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
  let goal =
    make_goal
      [%term
        forall (fun (x : 'a) (xs : 'a list) (ys : 'a list) ->
            append (cons x xs) ys = cons x (append xs ys))]
  in
  run_proof ~name:"append_cons" goal (intros_tac >> simp_tac);

  [%expect
    {|
    ========================================
    ∀x. ∀xs. ∀ys. append (cons x xs) ys = cons x (append xs ys)

    Proof Complete!
    with fuel: 27
    |}]

let%expect_test "append xs nil = xs" =
  let goal =
    make_goal [%term forall (fun (xs : 'a list) -> append xs nil = xs)]
  in
  run_proof ~name:"append_xs_nil" goal
    (induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "append_cons" ] rewrite_tac
    >> with_proven [ "append_cons" ] simp_tac);

  [%expect
    {|
    ========================================
    ∀x. append x nil = x

    Proof Complete!
    with fuel: 51
    |}]

let%expect_test "append (append xs ys) zs = append xs (append ys zs)" =
  let goal =
    make_goal
      [%term
        forall (fun (xs : 'a list) (ys : 'a list) (zs : 'a list) ->
            append (append xs ys) zs = append xs (append ys zs))]
  in
  run_proof ~name:"append_assoc" goal
    (induct_tac
    >>= [
          with_no_automation_trace auto_dfs_tac;
          with_no_automation_trace auto_dfs_tac;
        ]);
  [%expect
    {|
    ========================================
    ∀x. ∀ys. ∀zs. append (append x ys) zs = append x (append ys zs)

    Proof Complete!
    with fuel: 161
    |}]

let%expect_test "length (append xs ys) = plus (length xs) (length ys)" =
  let goal =
    make_goal
      [%term
        forall (fun (xs : 'a list) (ys : 'a list) (zs : 'a list) ->
            length (append xs ys) = plus (length xs) (length ys))]
  in
  run_proof ~name:"append_length" goal
    (induct_tac
    >> with_no_automation_trace auto_dfs_tac
    >> with_no_automation_trace auto_dfs_tac);

  [%expect
    {|
    ========================================
    ∀x. ∀ys. ∀zs. length (append x ys) = plus (length x) (length ys)

    Proof Complete!
    with fuel: 164
    |}]

let%expect_test "length (reverse xs) = length xs" =
  let goal =
    make_goal
      [%term forall (fun (x : 'a list) -> length (reverse x) = length x)]
  in
  run_proof goal
    (induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "append_length" ] simp_tac
    >> with_first (with_proven [ "plus_comm" ] rewrite_tac)
    >> simp_tac);

  [%expect
    {|
    ========================================
    ∀x. length (reverse x) = length x

    Proof Complete!
    with fuel: 104
    |}]

let%expect_test "reverse (append xs ys) = append (reverse ys) (reverse xs)" =
  let goal =
    make_goal
      [%term
        forall (fun (xs : 'a list) (ys : 'a list) ->
            reverse (append xs ys) = append (reverse ys) (reverse xs))]
  in
  run_proof ~name:"append_reverse" goal
    (induct_tac >> intros_tac
    >> with_proven [ "append_xs_nil" ] simp_tac
    >> intros_tac >> simp_tac
    >> with_first (with_proven [ "append_assoc" ] apply_thm_tac));

  [%expect
    {|
    ========================================
    ∀x. ∀ys. reverse (append x ys) = append (reverse ys) (reverse x)

    Proof Complete!
    with fuel: 90
    |}]

let%expect_test "reverse (reverse xs) = xs" =
  let goal =
    make_goal [%term forall (fun (xs : 'a list) -> reverse (reverse xs) = xs)]
  in
  run_proof goal
    (induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "append_reverse" ] simp_tac);
  [%expect
    {|
    ========================================
    ∀x. reverse (reverse x) = x

    Proof Complete!
    with fuel: 93
    |}]

let%expect_test "test defining with elab" =
  let goal =
    make_goal
      [%term
        forall (fun (x : 'a) (y : 'a) ->
            x = y ==> (fst (pair x y) = snd (pair x y)))]
  in
  run_proof goal (intros_tac >> simp_tac);

  [%expect
    {|
    ========================================
    ∀x. ∀y. x = y ==> fst (pair x y) = snd (pair x y)

    Proof Complete!
    with fuel: 29
    |}]

let%expect_test "test minus" =
  let goal = make_goal [%term pred 3n = 2n] in
  run_proof ~pretty:true goal simp_tac;

  [%expect
    {|
    ========================================
    pred 3 = 2

    Proof Complete!
    with fuel: 12
    |}]

let%expect_test "test minus 2" =
  let goal = make_goal [%term minus 4n 3n = 1n] in
  run_proof ~pretty:true goal simp_tac;

  [%expect
    {|
    ========================================
    minus 4 3 = 1

    Proof Complete!
    with fuel: 66
    |}]

let%expect_test "n - 0 = n" =
  let goal = make_goal [%term forall (fun (n : nat) -> minus n zero = n)] in
  run_proof ~name:"minus_zero" goal
    (induct_tac
    >> with_no_automation_trace auto_dfs_tac
    >> with_no_automation_trace auto_dfs_tac);

  [%expect
    {|
    ========================================
    ∀x. minus x zero = x

    Proof Complete!
    with fuel: 122
    |}]

(* n - (suc m) = (n - m) - 1 *)
let%expect_test "minus suc right" =
  let goal =
    make_goal
      [%term
        forall (fun (n : nat) (m : nat) -> minus n (suc m) = pred (minus n m))]
  in
  run_proof ~name:"minus_suc_right" goal
    (induct_tac
    >> with_proven [ "minus_zero" ] (with_no_automation_trace auto_dfs_tac)
    >> with_no_automation_trace auto_dfs_tac);
  [%expect
    {|
    ========================================
    ∀x. ∀m. minus x (suc m) = pred (minus x m)

    Proof Complete!
    with fuel: 178
    |}]

(* (suc n) - (suc m) = n - m *)
let%expect_test "minus suc suc" =
  let goal =
    make_goal
      [%term
        forall (fun (n : nat) (m : nat) -> minus (suc n) (suc m) = minus n m)]
  in
  run_proof ~name:"minus_suc_suc" goal
    (gen_tac >> induct_tac
    >> with_proven [ "minus_zero" ] simp_tac
    >> intros_tac
    >> with_proven [ "minus_suc_right" ] rewrite_tac
    >> with_assumptions rewrite_tac
    >> with_proven [ "minus_suc_right" ] rewrite_tac
    >> refl_tac);
  [%expect
    {|
    ========================================
    ∀n. ∀x. minus (suc n) (suc x) = minus n x

    Proof Complete!
    with fuel: 81
    |}]

let%expect_test "n - n = z" =
  let goal = make_goal [%term forall (fun (n : nat) -> minus n n = zero)] in
  run_proof ~name:"minus_self" goal
    (induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "minus_suc_suc" ] simp_tac
    >> simp_asm_tac ~with_asms:false);

  [%expect
    {|
    ========================================
    ∀x. minus x x = zero

    Proof Complete!
    with fuel: 103
    |}]

let%expect_test "x - n + n = x" =
  let goal =
    make_goal [%term forall (fun (x : nat) (n : nat) -> minus (plus x n) n = x)]
  in
  run_proof goal
    (gen_tac >> induct_tac
    >> with_proven [ "plus_x_zero"; "minus_zero" ] simp_tac
    >> intros_tac
    >> with_proven [ "plus_suc" ] rewrite_tac
    >> with_proven [ "minus_suc_suc" ] rewrite_tac
    >> assumption_tac);
  [%expect
    {|
    ========================================
    ∀x. ∀x'. minus (plus x x') x' = x

    Proof Complete!
    with fuel: 42
    |}]

let%expect_test "pred twice" =
  let goal = make_goal [%term twice pred 2n = 0n] in
  run_proof goal simp_tac;

  [%expect
    {|
    ========================================
    twice pred (suc (suc zero)) = zero

    Proof Complete!
    with fuel: 29
    |}]

let%expect_test "flip f" =
  let goal =
    make_goal
      [%term
        forall (fun (f : 'a -> 'b -> 'c) (x : 'a) (y : 'b) ->
            flip f y x = f x y)]
  in
  run_proof ~name:"flip_f" goal (intros_tac >> simp_tac);

  [%expect
    {|
    ========================================
    ∀f. ∀x. ∀y. flip f y x = f x y

    Proof Complete!
    with fuel: 27
    |}]

let%expect_test "bool distinct" =
  let goal = make_goal [%term not (true = false)] in
  let t = true_def |> Result.get_ok in
  run_proof goal
    (neg_intro_tac
    >> with_assumptions (with_flip_rules rewrite_tac)
    >> with_rule t rewrite_tac >> refl_tac);

  [%expect
    {|
    ========================================
    ¬T = F

    Proof Complete!
    with fuel: 15
    |}]

let%expect_test "cond true" =
  let goal =
    make_goal
      [%term forall (fun (t1 : 'a) (t2 : 'a) -> (if true then t1 else t2) = t1)]
  in
  run_proof ~notrace:true goal
    (intros_tac
    >> with_rule (cond_def |> Result.get_ok) rewrite_tac
    >> beta_tac
    >> with_rule t_eq_t rewrite_tac
    >> with_rule t_eq_f rewrite_tac
    >> with_rule f_imp_eq rewrite_tac
    >> with_rule conj_t_eq rewrite_tac
    >> with_rule t_imp_eq rewrite_tac
    >> with_rule select_eq rewrite_tac
    >> refl_tac);

  [%expect
    {|
    ========================================
    ∀t1. ∀t2. COND T t1 t2 = t1

    Proof Complete!
    with fuel: 43
    |}]

let%expect_test "cond false" =
  let goal =
    make_goal
      [%term
        forall (fun (t1 : 'a) (t2 : 'a) -> (if false then t1 else t2) = t2)]
  in
  run_proof ~notrace:true goal
    (intros_tac
    >> with_rule (cond_def |> Result.get_ok) rewrite_tac
    >> beta_tac
    >> with_rule f_eq_t rewrite_tac
    >> with_rule f_eq_f rewrite_tac
    >> with_rule f_imp_eq rewrite_tac
    >> with_rule t_conj_eq rewrite_tac
    >> with_rule t_imp_eq rewrite_tac
    >> with_rule select_eq rewrite_tac
    >> refl_tac);

  [%expect
    {|
    ========================================
    ∀t1. ∀t2. COND F t1 t2 = t2

    Proof Complete!
    with fuel: 43
    |}]

let%expect_test "le nat test" =
  let goal = make_goal [%term nat_le 0n 1n] in
  let proof = simp_tac in
  run_proof ~notrace:true goal proof;

  [%expect
    {|
    ========================================
    nat_le zero (suc zero)

    Proof Complete!
    with fuel: 20
    |}]

let%expect_test "le nat test2" =
  let goal = make_goal [%term not (nat_le 3n 1n)] in
  run_proof ~pretty:true ~notrace:true goal
    (simp_tac >> neg_intro_tac >> assumption_tac);

  [%expect
    {|
    ========================================
    ¬(nat_le 3 1)

    Proof Complete!
    with fuel: 64
    |}]

(* insert 3 into [] = [3] *)
let%expect_test "insert into nil" =
  let goal = make_goal [%term insert nil 3n = cons 3n nil] in
  run_proof ~pretty:true ~notrace:true goal simp_tac;

  [%expect
    {|
    ========================================
    insert [] 3 = [3]

    Proof Complete!
    with fuel: 19
    |}]

(* insert 2 into [1] = [1, 2] *)
let%expect_test "insert into singleton" =
  let goal =
    make_goal [%term insert (cons 1n nil) 2n = cons 1n (cons 2n nil)]
  in
  run_proof ~pretty:true ~notrace:true goal simp_tac;

  [%expect
    {|
    ========================================
    insert [1] 2 = [1, 2]

    Proof Complete!
    with fuel: 51
    |}]

let%expect_test "test sub" =
  let goal = make_goal [%term sub 4n 3n = 1n] in
  run_proof ~pretty:true goal simp_tac;

  [%expect
    {|
    ========================================
    sub 4 3 = 1

    Proof Complete!
    with fuel: 87
    |}]

let%expect_test "minus zero left" =
  let goal = make_goal [%term forall (fun (x : nat) -> minus 0n x = 0n)] in
  run_proof ~name:"minus_zero_left" goal
    (induct_tac >> simp_tac >> intros_tac
    >> simp_asm_tac ~with_asms:false
    >> simp_tac ~with_asms:false
    >> with_assumptions rewrite_tac
    >> simp_tac);

  [%expect
    {|
    ========================================
    ∀x. minus zero x = zero

    Proof Complete!
    with fuel: 127
    |}]

let%expect_test "sub eq minus" =
  let goal =
    make_goal [%term forall (fun (x : nat) (n : nat) -> sub x n = minus x n)]
  in
  run_proof goal
    (induct_tac
    >>= [
          with_proven [ "minus_zero_left" ] simp_tac >>> gen_tac >>> refl_tac;
          gen_tac >> intro_tac >> induct_tac
          >>= [
                with_proven [ "minus_zero" ] simp_tac;
                intros_tac
                >> with_proven [ "minus_suc_suc" ] rewrite_tac
                >> simp_tac;
              ];
        ]);

  [%expect
    {|
    ========================================
    ∀x. ∀n. sub x n = minus x n

    Proof Complete!
    with fuel: 162
    |}]

(* isort [] = [] *)
let%expect_test "isort nil" =
  let goal = make_goal [%term isort nil = nil] in
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
  let goal =
    make_goal
      [%term
        isort
          (cons
             (suc (suc (suc zero)))
             (cons (suc zero) (cons (suc (suc zero)) nil)))
        = cons (suc zero)
            (cons (suc (suc zero)) (cons (suc (suc (suc zero))) nil))]
  in
  run_proof ~pretty:true goal simp_tac;
  [%expect
    {|
    ========================================
    isort [3, 1, 2] = [1, 2, 3]

    Proof Complete!
    with fuel: 186
    |}]

let%expect_test "bool eq" =
  let goal = make_goal [%term eqb true false = false] in
  run_proof goal simp_tac;

  [%expect
    {|
    ========================================
    eqb T F = F

    Proof Complete!
    with fuel: 36
    |}]

let%expect_test "bool cases tac" =
  let goal =
    make_goal [%term forall (fun (b : bool) -> b = true || b = false)]
  in

  run_proof ~name:"bool_cases_test" goal
    (cases_tac >>= [ left_tac >> refl_tac; right_tac >> refl_tac ]);
  [%expect
    {|
    ========================================
    ∀b. b = T ∨ b = F

    Proof Complete!
    with fuel: 22
    |}]

let%expect_test "nat_le_flip" =
  let goal =
    make_goal
      [%term
        forall (fun (m : nat) (n : nat) ->
            nat_le m n = false ==> (nat_le n m = true))]
  in
  run_proof ~name:"nat_le_flip" goal
    (induct_tac
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
        ]);
  [%expect
    {|
    ========================================
    ∀x. ∀n. nat_le x n = F ==> nat_le n x = T

    Proof Complete!
    with fuel: 151
    |}]

let%expect_test "sort correct lemma" =
  let goal =
    make_goal
      [%term
        forall (fun (l : nat list) (n : nat) ->
            sorted l ==> sorted (insert l n))]
  in
  run_proof ~name:"sort_correct_lemma" goal
    (induct_tac >>> (intros_tac >> simp_tac)
    >>= [
          conj_tac >>> truth_tac;
          cond_tac >>> (simp_tac >> conj_tac)
          >>= [
                with_arbitrary_term [%term (n1 : nat list)] induct_tac
                >>> (intros_tac >> simp_tac)
                >>= [
                      with_arbitrary_term
                        [%term nat_le (n0' : nat) (n : nat)]
                        cases_tac
                      >>> simp_tac
                      >>= [
                            simp_asm_tac >> elim_conj_asm_tac >> assumption_tac;
                            truth_tac;
                          ];
                    ];
                spec_asm_tac [%term (n : nat)]
                >> apply_asm_tac >> simp_asm_tac >> elim_conj_asm_tac
                >> with_first assumption_tac;
                with_proven [ "nat_le_flip" ] apply_thm_asm_tac >> simp_tac;
                conj_tac
                >>= [
                      with_arbitrary_term [%term (n1 : nat list)] induct_tac
                      >>> (intros_tac >> simp_tac)
                      >>= [
                            simp_asm_tac >> elim_conj_asm_tac >> assumption_tac;
                          ];
                      spec_asm_tac [%term (n1 : nat)]
                      >> simp_asm_tac >> elim_conj_asm_tac
                      >> with_first assumption_tac;
                    ];
              ];
        ]);

  [%expect
    {|
    ========================================
    ∀x. ∀n. sorted x ==> sorted (insert x n)

    Proof Complete!
    with fuel: 553
    |}]

let%expect_test "sort correct" =
  let goal =
    make_goal [%term forall (fun (l : nat list) -> sorted (isort l))]
  in
  run_proof goal
    (induct_tac >> simp_tac >> intros_tac >> simp_tac
    >> with_proven [ "sort_correct_lemma" ] apply_thm_tac
    >> assumption_tac);

  [%expect
    {|
    ========================================
    ∀x. sorted (isort x)

    Proof Complete!
    with fuel: 52
    |}]

let%expect_test "option not none" =
  let goal =
    make_goal
      [%term
        forall (fun (o : 'a option) ->
            (not (o = none)) ==> exists (fun (x : 'a) -> o = some x))]
  in
  run_proof goal
    (intros_tac
    >> with_arbitrary_term [%term (o : 'a option)] destruct_tac
    >> elim_disj_asm_tac >> neg_elim_tac >> elim_exists_asm_tac
    >> with_arbitrary_term [%term (a0 : 'a)] exists_tac
    >> assumption_tac);
  [%expect
    {|
    ========================================
    ∀o. ¬o = none ==> ∃x. o = some x

    Proof Complete!
    with fuel: 30
    |}]

let%expect_test "div fuel irrel" =
  let goal =
    make_goal
      [%term
        forall (fun (n : nat) (m : nat) (a : nat) (b : nat) (x : nat) ->
            div_aux n a b = some x ==> (div_aux (plus n m) a b = some x))]
  in
  run_proof ~name:"div_fuel_irrel" ~notrace:true goal
    (induct_tac >> intros_tac >> simp_asm_tac
    >> with_rule (List.hd OptionTheory.option_def.distinct) rewrite_asm_tac
    >> false_elim_tac >> intros_tac
    >> with_first (with_definition [ "plus" ] rewrite_tac)
    >> beta_tac >> simp_tac >> simp_asm_tac
    >> with_arbitrary_term [%term nat_lt (a : nat) (b : nat)] cases_tac
    >> simp_tac >> simp_asm_tac
    >> with_arbitrary_term
         [%term div_aux (n0 : nat) (sub (a : nat) (b : nat)) (b : nat)]
         destruct_tac
    >> elim_disj_asm_tac >> simp_asm_tac
    >> with_first
       @@ with_rule (List.hd OptionTheory.option_def.distinct) rewrite_asm_tac
    >> false_elim_tac >> elim_exists_asm_tac >> simp_asm_tac
    >> spec_asm_tac [%term (m : nat)]
    >> spec_asm_tac [%term sub (a : nat) (b : nat)]
    >> spec_asm_tac [%term (b : nat)]
    >> spec_asm_tac [%term (a0 : nat)]
    >> with_first mp_asm_tac
    >> with_assumptions rewrite_tac
    >> simp_tac >> simp_tac
    >> with_nth_term 1 (with_assumptions rewrite_asm_tac)
    >> simp_asm_tac >> simp_asm_tac);
  [%expect
    {|
    ========================================
    ∀x. ∀m. ∀a. ∀b. ∀x'. div_aux x a b = some x' ==> div_aux (plus x m) a b = some x'

    Proof Complete!
    with fuel: 292
    |}]

let%expect_test "lt_zero_suc" =
  let n0 = [%term (n0 : nat)] in
  let goal =
    make_goal
      [%term
        forall (fun (b : nat) ->
            nat_lt 0n b ==> exists (fun (x : nat) -> b = suc x))]
  in
  run_proof ~simp:true ~name:"lt_zero_suc" ~notrace:true goal
    (induct_tac >> intros_tac >> simp_asm_tac >> false_elim_tac >> intros_tac
    >> with_arbitrary_term n0 exists_tac
    >> refl_tac);
  [%expect
    {|
    ========================================
    ∀x. nat_lt zero x ==> ∃x'. x = suc x'

    Proof Complete!
    with fuel: 58
    |}]

let nat_induct_auto_tac =
  induct_tac
  >> with_no_automation_trace auto_dfs_tac
  >> with_no_automation_trace auto_dfs_tac

let%expect_test "suc_lt_zero" =
  let goal =
    make_goal
      [%term forall (fun (x : nat) (b : nat) -> b = suc x ==> nat_lt 0n b)]
  in
  run_proof ~simp:true ~name:"suc_lt_zero" ~notrace:true goal
    nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. ∀b. b = suc x ==> nat_lt zero b

    Proof Complete!
    with fuel: 160
    |}]

let%expect_test "lt_zero_suc" =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_lt a zero = false)]
  in
  run_proof ~simp:true ~name:"lt_zero_false" ~notrace:true goal
    nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. nat_lt x zero = F

    Proof Complete!
    with fuel: 97
    |}]

let%expect_test "lt_add_suc_r" =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_lt a (plus a (suc b)))]
  in
  run_proof ~name:"lt_add_suc_r" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_lt x (plus x (suc b))

    Proof Complete!
    with fuel: 154
    |}]

let%expect_test "add_lt_cancel_l" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_lt (plus a b) (plus a c) = nat_lt b c)]
  in
  run_proof ~name:"add_lt_cancel_l" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. ∀b. ∀c. nat_lt (plus x b) (plus x c) = nat_lt b c

    Proof Complete!
    with fuel: 164
    |}]

let%expect_test "add_le_cancel_l" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_le (plus a b) (plus a c) = nat_le b c)]
  in
  run_proof ~name:"add_le_cancel_l" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. ∀b. ∀c. nat_le (plus x b) (plus x c) = nat_le b c

    Proof Complete!
    with fuel: 164
    |}]

(* ===== Group 1: Basic computation rules ===== *)

let%expect_test "sub_zero_r" =
  let goal = make_goal [%term forall (fun (a : nat) -> sub a 0n = a)] in
  run_proof ~simp:true ~name:"sub_zero_r" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. sub x zero = x

    Proof Complete!
    with fuel: 85
    |}]

let%expect_test "sub_suc_suc" =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> sub (suc a) (suc b) = sub a b)]
  in
  run_proof ~simp:true ~name:"sub_suc_suc" ~notrace:true goal
    nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. ∀b. sub (suc x) (suc b) = sub x b

    Proof Complete!
    with fuel: 153
    |}]

let%expect_test "sub_zero_l" =
  let goal = make_goal [%term forall (fun (a : nat) -> sub zero a = 0n)] in
  run_proof ~simp:true ~name:"sub_zero_l" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. sub zero x = zero

    Proof Complete!
    with fuel: 71
    |}]

let%expect_test "lt_zero_suc" =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_lt 0n (suc a) = true)]
  in
  run_proof ~simp:true ~name:"lt_zero_suc" ~notrace:true goal
    nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. nat_lt zero (suc x) = T

    Proof Complete!
    with fuel: 107
    |}]

let%expect_test "lt_suc_suc" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_lt (suc a) (suc b) = nat_lt a b)]
  in
  run_proof ~simp:true ~name:"lt_suc_suc" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_lt (suc x) (suc b) = nat_lt x b

    Proof Complete!
    with fuel: 153
    |}]

let%expect_test "le_zero_eq" =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_le a 0n ==> (a = 0n))]
  in
  run_proof ~simp:true ~name:"le_zero_eq" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. nat_le x zero ==> x = zero

    Proof Complete!
    with fuel: 127
    |}]

let%expect_test "le_zero_l" =
  let goal = make_goal [%term forall (fun (a : nat) -> nat_le 0n a = true)] in

  run_proof ~simp:true ~name:"le_zero_l" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. nat_le zero x = T

    Proof Complete!
    with fuel: 78
    |}]

let%expect_test "le_suc_suc" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_le (suc a) (suc b) = nat_le a b)]
  in

  run_proof ~simp:true ~name:"le_suc_suc" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le (suc x) (suc b) = nat_le x b

    Proof Complete!
    with fuel: 153
    |}]

let%expect_test "le_zero_r" =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_le (suc a) zero = false)]
  in
  run_proof ~simp:true ~name:"le_zero_r" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. nat_le (suc x) zero = F

    Proof Complete!
    with fuel: 117
    |}]

(* ===== Group 2: Reflexivity and basic identity ===== *)

let%expect_test "lt_irrefl" =
  let goal = make_goal [%term forall (fun (a : nat) -> nat_lt a a = false)] in
  run_proof ~simp:true ~name:"lt_irrefl" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. nat_lt x x = F

    Proof Complete!
    with fuel: 64
    |}]

let%expect_test "le_refl" =
  let goal = make_goal [%term forall (fun (a : nat) -> nat_le a a = true)] in
  run_proof ~simp:true ~name:"le_refl" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. nat_le x x = T

    Proof Complete!
    with fuel: 64
    |}]

let%expect_test "sub_self" =
  let goal = make_goal [%term forall (fun (a : nat) -> sub a a = 0n)] in

  run_proof ~simp:true ~name:"sub_self" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. sub x x = zero

    Proof Complete!
    with fuel: 64
    |}]

let%expect_test "add_zero_l" =
  let goal = make_goal [%term forall (fun (a : nat) -> plus 0n a = a)] in
  run_proof ~simp:true ~name:"add_zero_l" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. plus zero x = x

    Proof Complete!
    with fuel: 78
    |}]

let%expect_test "add_suc_l" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> plus (suc a) b = suc (plus a b))]
  in
  run_proof ~simp:true ~name:"add_suc_l" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. ∀b. plus (suc x) b = suc (plus x b)

    Proof Complete!
    with fuel: 124
    |}]

(* ===== Group 3: Successor relationships ===== *)

let%expect_test "lt_suc_self" =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_lt a (suc a) = true)]
  in
  run_proof ~simp:true ~name:"lt_suc_self" ~notrace:true goal
    nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. nat_lt x (suc x) = T

    Proof Complete!
    with fuel: 64
    |}]

let%expect_test "le_suc_self" =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_le a (suc a) = true)]
  in
  run_proof ~simp:true ~name:"le_suc_self" ~notrace:true goal
    nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. nat_le x (suc x) = T

    Proof Complete!
    with fuel: 64
    |}]

let%expect_test "lt_suc_le" =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_lt a (suc b) = nat_le a b)]
  in

  run_proof ~simp:true ~name:"lt_suc_le" ~notrace:true goal
    (induct_tac
    >> with_no_automation_trace auto_dfs_tac
    >> intros_tac >> simp_tac
    >> with_arbitrary_term [%term (b : nat)] destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> elim_exists_asm_tac >> simp_tac);
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_lt x (suc b) = nat_le x b

    Proof Complete!
    with fuel: 155
    |}]

let%expect_test "le_lt_suc" =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_le a b = nat_lt a (suc b))]
  in
  run_proof ~name:"le_lt_suc" ~notrace:true goal nat_induct_auto_tac;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le x b = nat_lt x (suc b)

    Proof Complete!
    with fuel: 117
    |}]

(* (* ===== Group 4: Connection between lt and le ===== *) *)
let%expect_test "not_lt_is_le" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_lt a b = false = nat_le b a)]
  in

  run_proof ~simp:true ~name:"not_lt_is_le" ~notrace:true goal
    (induct_tac >> induct_tac >> simp_tac >> eq_true_elim_tac >> refl_tac
   >> intros_tac >> simp_tac >> eq_false_elim_tac >> neg_intro_tac
   >> sym_asm_tac
    >> with_first (with_assumptions rewrite_tac)
    >> truth_tac >> intros_tac >> simp_tac
    >> with_arbitrary_term [%term (b : nat)] destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> eq_true_elim_tac >> refl_tac
    >> elim_exists_asm_tac >> simp_tac);
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_lt x b = F = nat_le b x

    Proof Complete!
    with fuel: 196
    |}]

let%expect_test "equality simp rules" =
  run_proof ~simp:true ~name:"eq_true_false"
    (make_goal [%term true = false = false])
    (eq_false_elim_tac >> neg_intro_tac
    >> with_assumptions @@ with_flip_rules rewrite_tac
    >> truth_tac);
  run_proof ~simp:true ~name:"eq_false_false"
    (make_goal [%term false = false = true])
    (eq_true_elim_tac >> refl_tac);
  run_proof ~simp:true ~name:"eq_true_true"
    (make_goal [%term true = true = false])
    (eq_true_elim_tac >> refl_tac);
  run_proof ~simp:true ~name:"eq_false_true"
    (make_goal [%term false = true = false])
    (eq_false_elim_tac >> neg_intro_tac >> simp_tac);
  run_proof ~simp:true ~name:"neg_false_true"
    (make_goal [%term (not false) = true])
    (eq_true_elim_tac >> neg_intro_tac >> false_elim_tac);
  run_proof ~simp:true ~name:"neg_true_false"
    (make_goal [%term (not true) = false])
    (eq_false_elim_tac
    >> with_arbitrary_term t assert_tac
    >> truth_tac >> neg_intro_tac >> neg_elim_tac);
  run_proof ~name:"eq_cong"
    (make_goal
       [%term
         forall (fun (f : 'a -> 'b) (x : 'a) (y : 'a) -> x = y ==> (f x = f y))])
    (intros_tac >> simp_tac);

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
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_le a b = false = nat_lt b a)]
  in
  run_proof ~name:"not_le_is_lt" ~notrace:true goal
    (induct_tac >> intros_tac >> simp_tac >> intros_tac >> simp_tac
    >> with_arbitrary_term [%term (b : nat)] destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> elim_exists_asm_tac >> simp_tac
    >> with_arbitrary_term [%term (n0 : nat)] destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> elim_exists_asm_tac >> simp_tac);
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le x b = F = nat_lt b x

    Proof Complete!
    with fuel: 257
    |}]

let%expect_test "lt_implies_le" =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_lt a b ==> nat_le a b)]
  in
  run_proof ~name:"lt_implies_le" ~notrace:true goal
    (induct_tac
    >> with_no_automation_trace auto_dfs_tac
    >> intros_tac >> simp_tac
    >> with_arbitrary_term [%term (b : nat)] destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> simp_asm_tac >> elim_exists_asm_tac
    >> simp_tac >> simp_asm_tac
    >> spec_asm_tac [%term (a0 : nat)]
    >> mp_asm_tac >> assumption_tac);
  [%expect
    {|
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
  let proof =
    induct_tac
    >> with_no_automation_trace auto_dfs_tac
    >> with_no_automation_trace auto_dfs_tac
  in
  run_proof ~name:"le_add_r" ~notrace:true goal proof;
  [%expect
    {|
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
    >> with_first (with_definition [ "length" ] rewrite_asm_tac)
    >> with_proven [ "add_suc_l" ] rewrite_asm_tac
    >> with_proven [ "lt_suc_suc" ] rewrite_asm_tac
    >> spec_asm_tac a1 >> spec_asm_tac consa01' >> mp_asm_tac
    >> elim_exists_asm_tac >> simp_tac
    >> with_arbitrary_term wit exists_tac
    >> refl_tac >> simp_tac
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_proven [ "plus_comm" ] rewrite_asm_tac
    >> with_first (with_definition [ "length" ] rewrite_asm_tac)
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
    >> with_first (with_definition [ "length" ] rewrite_tac)
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
    >> with_first (with_definition [ "length" ] rewrite_tac)
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
    with fuel: 1341
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
    with fuel: 566
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
  let goal =
    make_goal
      [%term
        forall (fun (fuel : nat) (xs : nat list) ->
            nat_lt (length xs) fuel
            ==> exists (fun (x : nat list) -> merge_sort_aux fuel xs = some x))]
  in

  run_proof ~name:"merge_sort_fuel_sufficient" ~pretty:true ~notrace:true goal
    (induct_tac >> intros_tac >> simp_asm_tac >> false_elim_tac >> intros_tac
    >> with_first (with_definition [ "merge_sort_aux" ] rewrite_tac)
    >> beta_tac >> cond_tac
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac ~exclude:[ "merge_sort_aux"; "take"; "drop"; "div"; "merge" ]
    >> with_arbitrary_term [%term (xs : nat list)] exists_tac
    >> refl_tac
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac ~exclude:[ "merge_sort_aux"; "take"; "drop"; "div"; "merge" ]
    >> spec_asm_tac
         [%term take (div (length (xs : nat list)) 2n) (xs : nat list)]
    >> spec_asm_tac
         [%term drop (div (length (xs : nat list)) 2n) (xs : nat list)]
    >> (with_arbitrary_term
          [%term
            nat_lt
              (length (take (div (length (xs : nat list)) 2n) (xs : nat list)))
              (n0 : nat)]
          assert_tac
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
    >> with_arbitrary_term
         [%term
           nat_lt
             (length (drop (div (length (xs : nat list)) 2n) (xs : nat list)))
             (n0 : nat)]
         assert_tac
    >> with_first (with_proven [ "not_le_is_lt" ] rewrite_asm_tac)
    >> with_first (with_proven [ "div_pos" ] apply_thm_asm_tac)
    >> with_proven [ "length_drop" ] rewrite_tac
    >> with_arbitrary_term
         [%term
           nat_lt
             (sub (length (xs : nat list)) (div (length (xs : nat list)) 2n))
             (length (xs : nat list))]
         assert_tac
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
    >> with_arbitrary_term
         [%term merge (x' : nat list) (x'' : nat list)]
         exists_tac
    >> refl_tac);
  [%expect
    {|
    ========================================
    ∀x. ∀xs. nat_lt (length xs) x ==> ∃x. merge_sort_aux x xs = some x

    Proof Complete!
    with fuel: 300
    |}]

let%expect_test "merge sort fuel irrel" =
  let prg =
    {|
    variable fuel additional : nat
    variable xs x : list nat 

    theorem merge_sort_fuel_irrel :
        forall λfuel. forall λadditional. forall λxs. forall λx.
            imp (eq (merge_sort_aux fuel xs) (some x))
                (eq (merge_sort_aux (plus fuel additional) xs) (some x))
  |}
  in

  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof = sorry_tac in
  (*TODO: finish this one*)
  run_proof ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀fuel. ∀additional. ∀xs. ∀x. merge_sort_aux fuel xs = some x ==> merge_sort_aux (plus fuel additional) xs = some x

    Proof Complete!
    with fuel: 1
    |}]

let%expect_test "merge sort unfold" =
  let goal =
    make_goal
      [%term
        forall (fun (xs : nat list) ->
            merge_sort xs
            =
            if nat_le (length xs) 1n then xs
            else
              (fun (half_length : nat) ->
                merge
                  (merge_sort (take half_length xs))
                  (merge_sort (drop half_length xs)))
                (div (length xs) 2n))]
  in
  run_proof ~pretty:false ~notrace:true goal
    (intros_tac
    >> with_definition [ "merge_sort" ] rewrite_tac
    >> beta_tac
    >> with_first (with_definition [ "merge_sort_aux" ] rewrite_tac)
    >> beta_tac >> cond_tac
    >> with_repeat (with_first (with_assumptions rewrite_tac))
    >> simp_tac ~exclude:[ "merge_sort"; "merge"; "merge_sort_aux"; "div" ]
    >> simp_tac ~exclude:[ "merge_sort"; "merge"; "merge_sort_aux"; "div" ]
    >> with_arbitrary_term
         [%term
           merge_sort_aux
             (length (xs : nat list))
             (take (div (length (xs : nat list)) 2n) (xs : nat list))
           = some
               (merge_sort
                  (take (div (length (xs : nat list)) 2n) (xs : nat list)))]
         assert_tac
    >> with_definition [ "merge_sort" ] rewrite_tac
    >> beta_tac
    >> with_arbitrary_term
         [%term
           exists (fun (z : nat list) ->
               merge_sort_aux
                 (suc
                    (length
                       (take (div (length (xs : nat list)) 2n) (xs : nat list))))
                 (take (div (length (xs : nat list)) 2n) (xs : nat list))
               = some z)]
         assert_tac
    >> with_proven [ "merge_sort_fuel_sufficient" ] apply_thm_tac
    >> simp_tac >> elim_exists_asm_tac
    >> with_assumptions rewrite_tac
    >> simp_tac ~exclude:[ "merge_sort"; "merge"; "merge_sort_aux"; "div" ]
    >> with_arbitrary_term
         [%term
           plus
             (suc
                (length
                   (take (div (length (xs : nat list)) 2n) (xs : nat list))))
             (sub
                (length (xs : nat list))
                (suc
                   (length
                      (take (div (length (xs : nat list)) 2n) (xs : nat list)))))
           = length (xs : nat list)]
         assert_tac
    >> with_proven [ "plus_comm" ] rewrite_tac
    >> with_proven [ "sub_add_cancel" ] apply_thm_tac
    >> with_proven [ "length_take" ] rewrite_tac
    >> sorry_tac >> sorry_tac >> sorry_tac);
  [%expect
    {|
    ========================================
    ∀xs. merge_sort xs = COND (nat_le (length xs) (suc zero)) xs ((λhalf_length. merge (merge_sort (take half_length xs)) (merge_sort (drop half_length xs))) (div (length xs) (suc (suc zero))))

    Proof Complete!
    with fuel: 185
    |}]
