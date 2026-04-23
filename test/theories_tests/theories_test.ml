open Heft
open Kernel
open Derived
open Tactic
open Auto

let%expect_test "template" =
  let goal = make_goal [%term forall (fun (a : nat) -> true)] in
  run_proof ~notrace:true goal (intros >> truth);
  [%expect
    {|
    ========================================
    ∀a. T

    Proof Complete!
    with fuel: 5
    |}]

let%expect_test "basic nat" =
  let goal = make_goal [%term plus 2n 3n = 5n] in
  run_proof ~pretty:true goal simp;

  [%expect
    {|
    ========================================
    plus 2 3 = 5

    Proof Complete!
    with fuel: 28
    |}]

let%expect_test "Suc injective" =
  let goal =
    make_goal
      [%term forall (fun (x : nat) (y : nat) -> Suc x = Suc y ==> (x = y))]
  in
  run_proof ~name:"Suc_inj" goal
    (intros >> (apply |> with_rules Nats.nat_def.injective) >> assumption);

  [%expect
    {|
    ========================================
    ∀x. ∀y. Suc x = Suc y ==> x = y

    Proof Complete!
    with fuel: 13
    |}]

(* Lemma needed for commutativity: plus x (Suc y) = Suc (plus x y) *)
let%expect_test "plus Suc lemma" =
  let goal =
    make_goal
      [%term
        forall (fun (x : nat) (y : nat) -> plus x (Suc y) = Suc (plus x y))]
  in
  run_proof ~simp:true ~name:"plus_Suc" goal
    (induct >> gen >> simp >> intros >> simp);
  [%expect
    {|
    ========================================
    ∀x. ∀y. plus x (Suc y) = Suc (plus x y)

    Proof Complete!
    with fuel: 76
    |}]

let%expect_test "Suc injective rev" =
  let goal =
    make_goal
      [%term forall (fun (x : nat) (y : nat) -> x = y ==> (Suc x = Suc y))]
  in
  run_proof ~name:"Suc_inj_rev" goal
    (intros >> (rewrite |> with_assumptions) >> refl);
  [%expect
    {|
    ========================================
    ∀x. ∀y. x = y ==> Suc x = Suc y

    Proof Complete!
    with fuel: 13
    |}]

(* Commutativity: plus x y = plus y x *)
let%expect_test "plus comm" =
  let%thm plus_comm (x : nat) (y : nat) = plus x y = plus y x
  and proof =
    begin
      induct >> (gen >> simp) >> (intros >> simp)
    end
  in
  ignore plus_comm;

  [%expect
    {|
    ========================================
    ∀x. ∀y. plus x y = plus y x

    Proof Complete!
    with fuel: 71
    |}]

let%expect_test "cancellation" =
  let goal =
    make_goal
      [%term
        forall (fun (x : nat) (y : nat) (z : nat) ->
            plus x y = plus x z ==> (y = z))]
  in
  run_proof goal
    (induct >> simp >> intros >> assumption >> intros >> simp_asm
    >> with_first (with_proven [ "Suc_inj" ] apply_asm)
    >> with_first (with_assumptions apply_asm)
    >> assumption);
  [%expect
    {|
    ========================================
    ∀x. ∀y. ∀z. plus x y = plus x z ==> y = z

    Proof Complete!
    with fuel: 87
    |}]

let%expect_test "cancellation rev" =
  let goal =
    make_goal
      [%term
        forall (fun (x : nat) (y : nat) (z : nat) ->
            plus y x = plus z x ==> (y = z))]
  in
  run_proof goal
    (induct >> gen >> simp >> intros >> assumption >> intros
    >> with_proven [ "plus_Suc" ] rewrite_asm
    >> with_proven [ "plus_Suc" ] rewrite_asm
    >> with_proven [ "Suc_inj" ] apply_asm
    >> with_first (with_assumptions apply)
    >> assumption);

  [%expect
    {|
    ========================================
    ∀x. ∀y. ∀z. plus y x = plus z x ==> y = z

    Proof Complete!
    with fuel: 65
    |}]

(* xs = Nil ==> length xs = Zero *)
let%expect_test "Nil_implies_length_Zero" =
  let goal =
    make_goal
      [%term forall (fun (xs : 'a list) -> xs = Nil ==> (length xs = Zero))]
  in
  run_proof goal (intros >> simp ~with_asms:true);

  [%expect
    {|
    ========================================
    ∀xs. xs = Nil ==> length xs = Zero

    Proof Complete!
    with fuel: 23
    |}]

(* length xs = Zero ==> xs = Nil *)
let%expect_test "length_Zero_implies_Nil" =
  let%thm _length_zero_nil (xs : 'a list) = length xs = Zero ==> (xs = Nil)
  and proof =
    begin
      induct >> intros >> refl >> intros >> simp_asm >> discriminate
    end
  in
  ();

  [%expect
    {|
    ========================================
    ∀x. length x = Zero ==> x = Nil

    Proof Complete!
    with fuel: 45
    |}]

let%expect_test "append Nil xs = xs" =
  let goal =
    make_goal [%term forall (fun (xs : 'a list) -> append Nil xs = xs)]
  in
  run_proof goal (intros >> simp);

  [%expect
    {|
    ========================================
    ∀xs. append Nil xs = xs

    Proof Complete!
    with fuel: 24
    |}]

let%expect_test "append (Cons x xs) ys = Cons x (append xs ys)" =
  let goal =
    make_goal
      [%term
        forall (fun (x : 'a) (xs : 'a list) (ys : 'a list) ->
            append (Cons (x, xs)) ys = Cons (x, append xs ys))]
  in
  run_proof ~name:"append_cons" goal (intros >> simp);

  [%expect
    {|
    ========================================
    ∀x. ∀xs. ∀ys. append (Cons x xs) ys = Cons x (append xs ys)

    Proof Complete!
    with fuel: 28
    |}]

let%expect_test "append xs Nil = xs" =
  let goal =
    make_goal [%term forall (fun (xs : 'a list) -> append xs Nil = xs)]
  in
  run_proof ~name:"append_xs_Nil" goal
    (induct >> simp >> intros
    >> with_proven [ "append_cons" ] rewrite
    >> with_proven [ "append_cons" ] simp);

  [%expect
    {|
    ========================================
    ∀x. append x Nil = x

    Proof Complete!
    with fuel: 53
    |}]

let%expect_test "append (append xs ys) zs = append xs (append ys zs)" =
  let goal =
    make_goal
      [%term
        forall (fun (xs : 'a list) (ys : 'a list) (zs : 'a list) ->
            append (append xs ys) zs = append xs (append ys zs))]
  in
  run_proof ~name:"append_assoc" goal
    (induct
    >>= [ with_no_automation_trace auto_dfs; with_no_automation_trace auto_dfs ]
    );
  [%expect
    {|
    ========================================
    ∀x. ∀ys. ∀zs. append (append x ys) zs = append x (append ys zs)

    Proof Complete!
    with fuel: 173
    |}]

let%expect_test "length (append xs ys) = plus (length xs) (length ys)" =
  let goal =
    make_goal
      [%term
        forall (fun (xs : 'a list) (ys : 'a list) (zs : 'a list) ->
            length (append xs ys) = plus (length xs) (length ys))]
  in
  run_proof ~name:"append_length" goal
    (induct
    >> with_no_automation_trace auto_dfs
    >> with_no_automation_trace auto_dfs);

  [%expect
    {|
    ========================================
    ∀x. ∀ys. ∀zs. length (append x ys) = plus (length x) (length ys)

    Proof Complete!
    with fuel: 176
    |}]

let%expect_test "length (reverse xs) = length xs" =
  let goal =
    make_goal
      [%term forall (fun (x : 'a list) -> length (reverse x) = length x)]
  in
  run_proof goal
    (induct >> simp >> intros
    >> with_proven [ "append_length" ] simp
    >> with_first (with_proven [ "plus_comm" ] rewrite)
    >> simp);

  [%expect
    {|
    ========================================
    ∀x. length (reverse x) = length x

    Proof Complete!
    with fuel: 86
    |}]

let%expect_test "reverse (append xs ys) = append (reverse ys) (reverse xs)" =
  let goal =
    make_goal
      [%term
        forall (fun (xs : 'a list) (ys : 'a list) ->
            reverse (append xs ys) = append (reverse ys) (reverse xs))]
  in
  run_proof ~name:"append_reverse" goal
    (induct >> intros
    >> with_proven [ "append_xs_Nil" ] simp
    >> intros >> simp
    >> with_first (with_proven [ "append_assoc" ] apply));

  [%expect
    {|
    ========================================
    ∀x. ∀ys. reverse (append x ys) = append (reverse ys) (reverse x)

    Proof Complete!
    with fuel: 92
    |}]

let%expect_test "reverse (reverse xs) = xs" =
  let goal =
    make_goal [%term forall (fun (xs : 'a list) -> reverse (reverse xs) = xs)]
  in
  run_proof goal
    (induct >> simp >> intros >> with_proven [ "append_reverse" ] simp);
  [%expect
    {|
    ========================================
    ∀x. reverse (reverse x) = x

    Proof Complete!
    with fuel: 95
    |}]

let%expect_test "test defining with elab" =
  let goal =
    make_goal
      [%term
        forall (fun (x : 'a) (y : 'a) ->
            x = y ==> (fst (Pair (x, y)) = snd (Pair (x, y))))]
  in
  run_proof goal (intros >> simp);

  [%expect
    {|
    ========================================
    ∀x. ∀y. x = y ==> fst (Pair x y) = snd (Pair x y)

    Proof Complete!
    with fuel: 59
    |}]

let%expect_test "test minus" =
  let goal = make_goal [%term pred 3n = 2n] in
  run_proof ~pretty:true goal simp;

  [%expect
    {|
    ========================================
    pred 3 = 2

    Proof Complete!
    with fuel: 32
    |}]

let%expect_test "test minus 2" =
  let goal = make_goal [%term minus 4n 3n = 1n] in
  run_proof ~pretty:true goal simp;

  [%expect
    {|
    ========================================
    minus 4 3 = 1

    Proof Complete!
    with fuel: 103
    |}]

let%expect_test "n - 0 = n" =
  let goal = make_goal [%term forall (fun (n : nat) -> minus n Zero = n)] in
  run_proof ~name:"minus_Zero" goal
    (induct
    >> with_no_automation_trace auto_dfs
    >> with_no_automation_trace auto_dfs);

  [%expect
    {|
    ========================================
    ∀x. minus x Zero = x

    Proof Complete!
    with fuel: 127
    |}]

(* n - (Suc m) = (n - m) - 1 *)
let%expect_test "minus Suc right" =
  let goal =
    make_goal
      [%term
        forall (fun (n : nat) (m : nat) -> minus n (Suc m) = pred (minus n m))]
  in
  run_proof ~name:"minus_Suc_right" goal
    (induct
    >> with_proven [ "minus_Zero" ] (with_no_automation_trace auto_dfs)
    >> with_no_automation_trace auto_dfs);
  [%expect
    {|
    ========================================
    ∀x. ∀m. minus x (Suc m) = pred (minus x m)

    Proof Complete!
    with fuel: 216
    |}]

(* (Suc n) - (Suc m) = n - m *)
let%expect_test "minus Suc Suc" =
  let goal =
    make_goal
      [%term
        forall (fun (n : nat) (m : nat) -> minus (Suc n) (Suc m) = minus n m)]
  in
  run_proof ~name:"minus_Suc_Suc" goal
    (gen >> induct
    >> with_proven [ "minus_Zero" ] simp
    >> intros
    >> with_proven [ "minus_Suc_right" ] rewrite
    >> with_assumptions rewrite
    >> with_proven [ "minus_Suc_right" ] rewrite
    >> refl);
  [%expect
    {|
    ========================================
    ∀n. ∀x. minus (Suc n) (Suc x) = minus n x

    Proof Complete!
    with fuel: 94
    |}]

let%expect_test "n - n = z" =
  let goal = make_goal [%term forall (fun (n : nat) -> minus n n = Zero)] in
  run_proof ~name:"minus_self" goal
    (induct >> simp >> intros
    >> with_proven [ "minus_Suc_Suc" ] simp
    >> simp_asm ~with_asms:false);

  [%expect
    {|
    ========================================
    ∀x. minus x x = Zero

    Proof Complete!
    with fuel: 105
    |}]

let%expect_test "x - n + n = x" =
  let goal =
    make_goal [%term forall (fun (x : nat) (n : nat) -> minus (plus x n) n = x)]
  in
  run_proof goal
    (gen >> induct
    >> with_proven [ "plus_x_Zero"; "minus_Zero" ] simp
    >> intros
    >> with_proven [ "plus_Suc" ] rewrite
    >> with_proven [ "minus_Suc_Suc" ] rewrite
    >> assumption);
  [%expect
    {|
    ========================================
    ∀x. ∀x'. minus (plus x x') x' = x

    Proof Complete!
    with fuel: 43
    |}]

let%expect_test "pred twice" =
  let goal = make_goal [%term twice pred 2n = 0n] in
  run_proof goal simp;

  [%expect
    {|
    ========================================
    twice pred (Suc (Suc Zero)) = Zero

    Proof Complete!
    with fuel: 49
    |}]

let%expect_test "flip f" =
  let goal =
    make_goal
      [%term
        forall (fun (f : 'a -> 'b -> 'c) (x : 'a) (y : 'b) ->
            flip f y x = f x y)]
  in
  run_proof ~name:"flip_f" goal (intros >> simp);

  [%expect
    {|
    ========================================
    ∀f. ∀x. ∀y. flip f y x = f x y

    Proof Complete!
    with fuel: 28
    |}]

let%expect_test "bool distinct" =
  let goal = make_goal [%term not (true = false)] in
  let t = true_def |> Result.get_ok in
  run_proof goal
    (neg_intro
    >> with_assumptions (with_flip_rules rewrite)
    >> with_rule t rewrite >> refl);

  [%expect
    {|
    ========================================
    ¬T = F

    Proof Complete!
    with fuel: 15
    |}]

let%expect_test "le nat test" =
  let goal = make_goal [%term nat_le 0n 1n] in
  run_proof ~notrace:true goal simp;

  [%expect
    {|
    ========================================
    nat_le Zero (Suc Zero)

    Proof Complete!
    with fuel: 21
    |}]

let%expect_test "le nat test2" =
  let goal = make_goal [%term not (nat_le 3n 1n)] in
  run_proof ~pretty:true ~notrace:true goal (simp >> neg_intro >> assumption);

  [%expect
    {|
    ========================================
    ¬(nat_le 3 1)

    Proof Complete!
    with fuel: 65
    |}]

(* insert 3 into [] = [3] *)
let%expect_test "insert into Nil" =
  let goal = make_goal [%term insert Nil 3n = Cons (3n, Nil)] in
  run_proof ~pretty:true ~notrace:true goal simp;

  [%expect
    {|
    ========================================
    insert [] 3 = [3]

    Proof Complete!
    with fuel: 20
    |}]

(* insert 2 into [1] = [1, 2] *)
let%expect_test "insert into singleton" =
  let goal =
    make_goal [%term insert (Cons (1n, Nil)) 2n = Cons (1n, Cons (2n, Nil))]
  in
  run_proof ~pretty:true ~notrace:true goal simp;

  [%expect
    {|
    ========================================
    insert [1] 2 = [1, 2]

    Proof Complete!
    with fuel: 52
    |}]

let%expect_test "test sub" =
  let goal = make_goal [%term sub 4n 3n = 1n] in
  run_proof ~pretty:true goal simp;

  [%expect
    {|
    ========================================
    sub 4 3 = 1

    Proof Complete!
    with fuel: 88
    |}]

let%expect_test "minus Zero left" =
  let goal = make_goal [%term forall (fun (x : nat) -> minus 0n x = 0n)] in
  run_proof ~name:"minus_Zero_left" goal
    (induct >> simp >> intros >> simp_asm ~with_asms:false
   >> simp ~with_asms:false >> with_assumptions rewrite >> simp);

  [%expect
    {|
    ========================================
    ∀x. minus Zero x = Zero

    Proof Complete!
    with fuel: 142
    |}]

let%expect_test "sub eq minus" =
  let goal =
    make_goal [%term forall (fun (x : nat) (n : nat) -> sub x n = minus x n)]
  in
  run_proof goal
    (induct
    >>= [
          with_proven [ "minus_Zero_left" ] simp >>> gen >>> refl;
          gen >> intro >> induct
          >>= [
                with_proven [ "minus_Zero" ] simp;
                intros >> with_proven [ "minus_Suc_Suc" ] rewrite >> simp;
              ];
        ]);

  [%expect
    {|
    ========================================
    ∀x. ∀n. sub x n = minus x n

    Proof Complete!
    with fuel: 165
    |}]

(* isort [] = [] *)
let%expect_test "isort Nil" =
  let goal = make_goal [%term isort Nil = Nil] in
  run_proof goal simp;
  [%expect
    {|
    ========================================
    isort Nil = Nil

    Proof Complete!
    with fuel: 13
    |}]

(* isort [3,1,2] = [1,2,3] *)
let%expect_test "isort [3,1,2] = [1,2,3]" =
  let goal =
    make_goal
      [%term
        isort (Cons (3n, Cons (1n, Cons (2n, Nil))))
        = Cons (1n, Cons (2n, Cons (3n, Nil)))]
  in
  run_proof ~pretty:true goal simp;
  [%expect
    {|
    ========================================
    isort [3, 1, 2] = [1, 2, 3]

    Proof Complete!
    with fuel: 187
    |}]

let%expect_test "bool eq" =
  let goal = make_goal [%term eqb true false = false] in
  run_proof goal simp;

  [%expect
    {|
    ========================================
    eqb T F = F

    Proof Complete!
    with fuel: 35
    |}]

let%expect_test "bool cases tac" =
  let goal =
    make_goal [%term forall (fun (b : bool) -> b = true || b = false)]
  in

  run_proof ~name:"bool_cases_test" goal
    (cases >>= [ left >> refl; right >> refl ]);
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
    (induct
    >>= [
          gen >> intro >> simp_asm ~with_asms:false >> sym_asm
          >> eq_true_elim_asm >> false_elim;
          gen >> intro >> induct >> (intro >> simp)
          >> (intros >> simp_asm ~with_asms:false >> simp
             >> with_assumptions (with_first (apply >> assumption)));
        ]);
  [%expect
    {|
    ========================================
    ∀x. ∀n. nat_le x n = F ==> nat_le n x = T

    Proof Complete!
    with fuel: 153
    |}]

let%expect_test "sort correct lemma" =
  let goal =
    make_goal
      [%term
        forall (fun (l : nat list) (n : nat) ->
            sorted l ==> sorted (insert l n))]
  in
  run_proof ~name:"sort_correct_lemma" goal
    (induct >>> (intros >> simp)
    >>= [
          conj >>> truth;
          cond >>> (simp >> conj)
          >>= [
                with_term [%term (n1 : nat list)] induct
                >>> (intros >> simp)
                >>= [
                      with_term [%term nat_le (n0' : nat) (n : nat)] cases
                      >>> simp
                      >>= [ simp_asm >> elim_conj_asm >> assumption; truth ];
                    ];
                spec_asm [%term (n : nat)]
                >> with_assumptions apply >> simp_asm >> elim_conj_asm
                >> assumption;
                with_proven [ "nat_le_flip" ] apply_asm >> simp;
                conj
                >>= [
                      with_term [%term (n1 : nat list)] induct
                      >>> (intros >> simp)
                      >>= [ simp_asm >> elim_conj_asm >> assumption ];
                      spec_asm [%term (n1 : nat)]
                      >> simp_asm >> elim_conj_asm >> assumption;
                    ];
              ];
        ]);

  [%expect
    {|
    ========================================
    ∀x. ∀n. sorted x ==> sorted (insert x n)

    Proof Complete!
    with fuel: 564
    |}]

let%expect_test "sort correct" =
  let goal =
    make_goal [%term forall (fun (l : nat list) -> sorted (isort l))]
  in
  run_proof goal
    (induct >> simp >> intros >> simp
    >> with_proven [ "sort_correct_lemma" ] apply
    >> assumption);

  [%expect
    {|
    ========================================
    ∀x. sorted (isort x)

    Proof Complete!
    with fuel: 54
    |}]

let%expect_test "option not None" =
  let goal =
    make_goal
      [%term
        forall (fun (o : 'a option) ->
            (not (o = None)) ==> exists (fun (x : 'a) -> o = Some x))]
  in
  run_proof goal
    (intros
    >> with_term [%term (o : 'a option)] destruct
    >> elim_disj_asm >> neg_elim >> elim_exists_asm
    >> with_term [%term (a0 : 'a)] exists
    >> assumption);
  [%expect
    {|
    ========================================
    ∀o. ¬o = None ==> ∃x. o = Some x

    Proof Complete!
    with fuel: 30
    |}]

let apply_asm_to_asm ~asm_thm ~asm_to =
  with_nth_choice asm_thm (with_nth_term asm_to (with_assumptions apply_asm))

let%expect_test "div fuel irrel" =
  let%thm div_fuel_irrel (n : nat) (m : nat) (a : nat) (b : nat) (x : nat) =
    div_aux n a b = Some x ==> (div_aux (plus n m) a b = Some x)
  and proof =
    begin
      induct >> intros >> simp_asm >> discriminate >> intros
      >> with_first (with_definition [ "plus" ] rewrite)
      >> beta >> simp >> simp_asm
      >> with_term [%term nat_lt (a : nat) (b : nat)] cases
      >> simp >> simp_asm
      >> with_term
           [%term div_aux (n0 : nat) (sub (a : nat) (b : nat)) (b : nat)]
           destruct
      >> elim_disj_asm >> simp_asm >> discriminate >> elim_exists_asm
      >> simp_asm
      >> apply_asm_to_asm ~asm_thm:3 ~asm_to:1
      >> spec_asm [%term (m : nat)]
      >> with_assumptions rewrite >> simp >> simp
      >> with_nth_term 1 (with_assumptions rewrite_asm)
      >> simp_asm >> simp_asm
    end
  in
  ignore div_fuel_irrel;
  [%expect
    {|
    ========================================
    ∀x. ∀m. ∀a. ∀b. ∀x'. div_aux x a b = Some x' ==> div_aux (plus x m) a b = Some x'

    Proof Complete!
    with fuel: 302
    |}]

let%expect_test "lt_Zero_Suc" =
  let n0 = [%term (n0 : nat)] in
  let goal =
    make_goal
      [%term
        forall (fun (b : nat) ->
            nat_lt 0n b ==> exists (fun (x : nat) -> b = Suc x))]
  in
  run_proof ~simp:true ~name:"lt_Zero_Suc" ~notrace:true goal
    (induct >> intros >> simp_asm >> false_elim >> intros >> with_term n0 exists
   >> refl);
  [%expect
    {|
    ========================================
    ∀x. nat_lt Zero x ==> ∃x'. x = Suc x'

    Proof Complete!
    with fuel: 39
    |}]

let nat_induct_auto =
  induct
  >> with_no_automation_trace auto_dfs
  >> with_no_automation_trace auto_dfs

let%expect_test "Suc_lt_Zero" =
  let goal =
    make_goal
      [%term forall (fun (x : nat) (b : nat) -> b = Suc x ==> nat_lt 0n b)]
  in
  run_proof ~simp:true ~name:"Suc_lt_Zero" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. ∀b. b = Suc x ==> nat_lt Zero b

    Proof Complete!
    with fuel: 170
    |}]

let%expect_test "lt_Zero_Suc" =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_lt a Zero = false)]
  in
  run_proof ~simp:true ~name:"lt_Zero_false" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. nat_lt x Zero = F

    Proof Complete!
    with fuel: 69
    |}]

let%expect_test "lt_add_Suc_r" =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_lt a (plus a (Suc b)))]
  in
  run_proof ~name:"lt_add_Suc_r" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_lt x (plus x (Suc b))

    Proof Complete!
    with fuel: 179
    |}]

let%expect_test "add_lt_cancel_l" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_lt (plus a b) (plus a c) = nat_lt b c)]
  in
  run_proof ~name:"add_lt_cancel_l" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. ∀b. ∀c. nat_lt (plus x b) (plus x c) = nat_lt b c

    Proof Complete!
    with fuel: 175
    |}]

let%expect_test "add_le_cancel_l" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_le (plus a b) (plus a c) = nat_le b c)]
  in
  run_proof ~name:"add_le_cancel_l" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. ∀b. ∀c. nat_le (plus x b) (plus x c) = nat_le b c

    Proof Complete!
    with fuel: 175
    |}]

(* ===== Group 1: Basic computation rules ===== *)

let%expect_test "sub_Zero_r" =
  let goal = make_goal [%term forall (fun (a : nat) -> sub a 0n = a)] in
  run_proof ~simp:true ~name:"sub_Zero_r" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. sub x Zero = x

    Proof Complete!
    with fuel: 90
    |}]

let%expect_test "sub_Suc_Suc" =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> sub (Suc a) (Suc b) = sub a b)]
  in
  run_proof ~simp:true ~name:"sub_Suc_Suc" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. ∀b. sub (Suc x) (Suc b) = sub x b

    Proof Complete!
    with fuel: 161
    |}]

let%expect_test "sub_Zero_l" =
  let goal = make_goal [%term forall (fun (a : nat) -> sub Zero a = 0n)] in
  run_proof ~simp:true ~name:"sub_Zero_l" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. sub Zero x = Zero

    Proof Complete!
    with fuel: 76
    |}]

let%expect_test "lt_Zero_Suc" =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_lt 0n (Suc a) = true)]
  in
  run_proof ~simp:true ~name:"lt_Zero_Suc" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. nat_lt Zero (Suc x) = T

    Proof Complete!
    with fuel: 112
    |}]

let%expect_test "lt_Suc_Suc" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_lt (Suc a) (Suc b) = nat_lt a b)]
  in
  run_proof ~simp:true ~name:"lt_Suc_Suc" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_lt (Suc x) (Suc b) = nat_lt x b

    Proof Complete!
    with fuel: 161
    |}]

let%expect_test "le_Zero_eq" =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_le a 0n ==> (a = 0n))]
  in
  run_proof ~simp:true ~name:"le_Zero_eq" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. nat_le x Zero ==> x = Zero

    Proof Complete!
    with fuel: 135
    |}]

let%expect_test "le_Zero_l" =
  let goal = make_goal [%term forall (fun (a : nat) -> nat_le 0n a = true)] in

  run_proof ~simp:true ~name:"le_Zero_l" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. nat_le Zero x = T

    Proof Complete!
    with fuel: 83
    |}]

let%expect_test "le_Suc_Suc" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_le (Suc a) (Suc b) = nat_le a b)]
  in

  run_proof ~simp:true ~name:"le_Suc_Suc" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le (Suc x) (Suc b) = nat_le x b

    Proof Complete!
    with fuel: 161
    |}]

let%expect_test "le_Zero_r" =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_le (Suc a) Zero = false)]
  in
  run_proof ~simp:true ~name:"le_Zero_r" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. nat_le (Suc x) Zero = F

    Proof Complete!
    with fuel: 122
    |}]

(* ===== Group 2: Reflexivity and basic identity ===== *)

let%expect_test "lt_irrefl" =
  let goal = make_goal [%term forall (fun (a : nat) -> nat_lt a a = false)] in
  run_proof ~simp:true ~name:"lt_irrefl" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. nat_lt x x = F

    Proof Complete!
    with fuel: 69
    |}]

let%expect_test "le_refl" =
  let goal = make_goal [%term forall (fun (a : nat) -> nat_le a a = true)] in
  run_proof ~simp:true ~name:"le_refl" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. nat_le x x = T

    Proof Complete!
    with fuel: 69
    |}]

let%expect_test "sub_self" =
  let goal = make_goal [%term forall (fun (a : nat) -> sub a a = 0n)] in

  run_proof ~simp:true ~name:"sub_self" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. sub x x = Zero

    Proof Complete!
    with fuel: 69
    |}]

let%expect_test "add_Zero_l" =
  let goal = make_goal [%term forall (fun (a : nat) -> plus 0n a = a)] in
  run_proof ~simp:true ~name:"add_Zero_l" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. plus Zero x = x

    Proof Complete!
    with fuel: 81
    |}]

let%expect_test "add_Suc_l" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> plus (Suc a) b = Suc (plus a b))]
  in
  run_proof ~simp:true ~name:"add_Suc_l" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. ∀b. plus (Suc x) b = Suc (plus x b)

    Proof Complete!
    with fuel: 132
    |}]

(* ===== Group 3: Successor relationships ===== *)

let%expect_test "lt_Suc_self" =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_lt a (Suc a) = true)]
  in
  run_proof ~simp:true ~name:"lt_Suc_self" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. nat_lt x (Suc x) = T

    Proof Complete!
    with fuel: 69
    |}]

let%expect_test "le_Suc_self" =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_le a (Suc a) = true)]
  in
  run_proof ~simp:true ~name:"le_Suc_self" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. nat_le x (Suc x) = T

    Proof Complete!
    with fuel: 69
    |}]

let%expect_test "lt_Suc_le" =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_lt a (Suc b) = nat_le a b)]
  in

  run_proof ~simp:true ~name:"lt_Suc_le" ~notrace:true goal
    (induct
    >> with_no_automation_trace auto_dfs
    >> intros >> simp
    >> with_term [%term (b : nat)] destruct
    >> elim_disj_asm >> simp >> elim_exists_asm >> simp);
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_lt x (Suc b) = nat_le x b

    Proof Complete!
    with fuel: 161
    |}]

let%expect_test "le_lt_Suc" =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_le a b = nat_lt a (Suc b))]
  in
  run_proof ~name:"le_lt_Suc" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le x b = nat_lt x (Suc b)

    Proof Complete!
    with fuel: 125
    |}]

(* (* ===== Group 4: Connection between lt and le ===== *) *)
let%expect_test "not_lt_is_le" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_lt a b = false = nat_le b a)]
  in

  run_proof ~simp:true ~name:"not_lt_is_le" ~notrace:true goal
    (induct >> induct >> simp >> eq_true_elim >> refl >> intros >> simp
   >> eq_false_elim >> neg_intro >> sym_asm
    >> with_first (with_assumptions rewrite)
    >> truth >> intros >> simp
    >> with_term [%term (b : nat)] destruct
    >> elim_disj_asm >> simp >> eq_true_elim >> refl >> elim_exists_asm >> simp
    );
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_lt x b = F = nat_le b x

    Proof Complete!
    with fuel: 201
    |}]

let () =
  run_proof ~quiet:true ~simp:true ~name:"eq_true_false"
    (make_goal [%term true = false = false])
    (eq_false_elim >> neg_intro
    >> with_assumptions @@ with_flip_rules rewrite
    >> truth);
  run_proof ~quiet:true ~simp:true ~name:"eq_false_false"
    (make_goal [%term false = false = true])
    (eq_true_elim >> refl);
  run_proof ~quiet:true ~simp:true ~name:"eq_true_true"
    (make_goal [%term true = true = false])
    (eq_true_elim >> refl);
  run_proof ~quiet:true ~simp:true ~name:"eq_false_true"
    (make_goal [%term false = true = false])
    (eq_false_elim >> neg_intro >> simp);
  run_proof ~quiet:true ~simp:true ~name:"neg_false_true"
    (make_goal [%term (not false) = true])
    (eq_true_elim >> neg_intro >> false_elim);
  run_proof ~quiet:true ~simp:true ~name:"neg_true_false"
    (make_goal [%term (not true) = false])
    (eq_false_elim
    >> with_term [%term true] have
    >> truth >> neg_intro >> neg_elim)

let%expect_test "not_le_is_lt" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_le a b = false = nat_lt b a)]
  in
  run_proof ~name:"not_le_is_lt" ~notrace:true goal
    (induct >> intros >> simp >> intros >> simp
    >> with_term [%term (b : nat)] destruct
    >> elim_disj_asm >> simp >> elim_exists_asm >> simp
    >> with_term [%term (n0 : nat)] destruct
    >> elim_disj_asm >> simp >> elim_exists_asm >> simp);
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le x b = F = nat_lt b x

    Proof Complete!
    with fuel: 263
    |}]

let%expect_test "lt_implies_le" =
  let%thm lt_implies_le (a : nat) (b : nat) = nat_lt a b ==> nat_le a b
  and proof =
    begin
      with_term [%term (a : nat)] induct
      >> with_no_automation_trace auto_dfs
      >> (intros @: [ "hIH"; "hlt" ]
         >> simp
         >> with_term [%term (b : nat)] destruct_elim @: [ "hzero"; ""; "hsuc" ]
         >> (simp_asm >> false_elim)
         >> (simp_all >> apply_at "hIH" ~target:"hlt" @! "hle" >> assumption))
    end
  in
  ignore lt_implies_le;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_lt x b ==> nat_le x b

    Proof Complete!
    with fuel: 215
    |}]

(* (* ===== Group 5: Transitivity ===== *) *)

let assumption_reasoning =
  try_
    (with_no_automation_trace
       (with_best_first
          (pick [ simp; simp_asm; false_elim; assumption; truth ])))

let%expect_test "lt_trans" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_lt a b ==> (nat_lt b c ==> nat_lt a c))]
  in
  run_proof ~name:"lt_trans" ~notrace:true goal
    (with_term [%term (a : nat)] induct
    >>> intros
    >>> with_term [%term (b : nat)] induct
    >>> intros
    >>> with_term [%term (c : nat)] induct
    >>> intros >>> try_ assumption_reasoning
    >>= [
          with_repeat (with_first (with_proven [ "lt_Suc_Suc" ] rewrite_asm))
          >> spec_asm [%term (n0' : nat)]
          >> spec_asm [%term (n0'' : nat)]
          >> with_proven [ "lt_Suc_Suc" ] rewrite
          >> with_repeat (with_assumptions (with_first_term apply_asm))
          >> assumption;
        ]);
  [%expect
    {|
    ========================================
    ∀x. ∀b. ∀c. nat_lt x b ==> nat_lt b c ==> nat_lt x c

    Proof Complete!
    with fuel: 990
    |}]

let%expect_test "le_trans" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_le a b ==> (nat_le b c ==> nat_le a c))]
  in
  run_proof ~name:"le_trans" ~notrace:true goal
    (with_term [%term (a : nat)] induct
    >>> intros
    >>> with_term [%term (b : nat)] induct
    >>> intros
    >>> with_term [%term (c : nat)] induct
    >>> intros >>> try_ assumption_reasoning
    >>= [
          with_repeat (with_first (with_proven [ "le_Suc_Suc" ] rewrite_asm))
          >> spec_asm [%term (n0' : nat)]
          >> spec_asm [%term (n0'' : nat)]
          >> with_proven [ "le_Suc_Suc" ] rewrite
          >> with_repeat (with_assumptions (with_first_term apply_asm))
          >> assumption;
        ]);
  [%expect
    {|
    ========================================
    ∀x. ∀b. ∀c. nat_le x b ==> nat_le b c ==> nat_le x c

    Proof Complete!
    with fuel: 728
    |}]

let%expect_test "le_lt_trans" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_le a b ==> (nat_lt b c ==> nat_lt a c))]
  in
  run_proof ~name:"le_lt_trans" ~notrace:true goal
    (with_term [%term (a : nat)] induct
    >>> intros
    >>> with_term [%term (b : nat)] induct
    >>> intros
    >>> with_term [%term (c : nat)] induct
    >>> intros >>> try_ assumption_reasoning
    >>= [
          with_repeat
            (with_first
               (with_proven [ "le_Suc_Suc"; "lt_Suc_Suc" ] rewrite_asm))
          >> spec_asm [%term (n0' : nat)]
          >> spec_asm [%term (n0'' : nat)]
          >> with_proven [ "lt_Suc_Suc" ] rewrite
          >> with_repeat (with_assumptions (with_first_term apply_asm))
          >> assumption;
        ]);
  [%expect
    {|
    ========================================
    ∀x. ∀b. ∀c. nat_le x b ==> nat_lt b c ==> nat_lt x c

    Proof Complete!
    with fuel: 964
    |}]

let%expect_test "lt_le_trans" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_lt a b ==> (nat_le b c ==> nat_lt a c))]
  in
  run_proof ~name:"lt_le_trans" ~notrace:true goal
    (with_term [%term (a : nat)] induct
    >>> intros
    >>> with_term [%term (b : nat)] induct
    >>> intros
    >>> with_term [%term (c : nat)] induct
    >>> intros >>> try_ assumption_reasoning
    >>= [
          with_proven [ "lt_Suc_Suc" ] rewrite
          >> with_repeat
               (with_first
                  (with_proven [ "lt_Suc_Suc"; "le_Suc_Suc" ] rewrite_asm))
          >> spec_asm [%term (n0' : nat)]
          >> spec_asm [%term (n0'' : nat)]
          >> with_repeat (with_assumptions (with_first_term apply_asm))
          >> assumption;
        ]);
  [%expect
    {|
    ========================================
    ∀x. ∀b. ∀c. nat_lt x b ==> nat_le b c ==> nat_lt x c

    Proof Complete!
    with fuel: 926
    |}]

let%expect_test "le_antisym" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) ->
            nat_le a b ==> (nat_le b a ==> ((a : nat) = b)))]
  in
  run_proof ~name:"le_antisym" ~notrace:true goal
    (with_term [%term (a : nat)] induct
    >>> intros
    >>> with_term [%term (b : nat)] induct
    >>> intros >>> try_ assumption_reasoning
    >> with_proven [ "eq_cong" ] apply
    >> with_repeat (with_first (with_proven [ "le_Suc_Suc" ] rewrite_asm))
    >> spec_asm [%term (n0' : nat)]
    >> with_repeat (with_assumptions (with_first_term apply_asm))
    >> assumption);
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le x b ==> nat_le b x ==> x = b

    Proof Complete!
    with fuel: 270
    |}]

(* (* ===== Group 6: Subtraction properties ===== *) *)

let%expect_test "le_weaken_Suc" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_le a b ==> nat_le a (Suc b))]
  in
  run_proof ~name:"le_weaken_Suc" ~notrace:true goal
    (with_term [%term (a : nat)] induct
    >>> intros
    >>> with_term [%term (b : nat)] induct
    >>> try_ intros >>> try_ assumption_reasoning
    >> with_proven [ "le_Suc_Suc" ] rewrite
    >> spec_asm [%term (n0' : nat)]
    >> with_repeat (with_first (with_proven [ "le_Suc_Suc" ] rewrite_asm))
    >> with_first (with_assumptions (with_first_term apply_asm))
    >> sorry);
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le x b ==> nat_le x (Suc b)

    Proof Complete!
    with fuel: 344
    |}]

let%expect_test "lt_weaken_Suc" =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_lt a b ==> nat_lt a (Suc b))]
  in
  run_proof ~name:"lt_weaken_Suc" ~notrace:true goal
    (with_term [%term (a : nat)] induct
    >>> intros
    >>> with_term [%term (b : nat)] induct
    >>> try_ intros >>> try_ assumption_reasoning
    >> with_proven [ "lt_Suc_Suc" ] rewrite
    >> spec_asm [%term (n0' : nat)]
    >> with_repeat (with_first (with_proven [ "lt_Suc_Suc" ] rewrite_asm))
    >> with_first (with_assumptions (with_first_term apply_asm))
    >> sorry);
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_lt x b ==> nat_lt x (Suc b)

    Proof Complete!
    with fuel: 411
    |}]

let%expect_test "sub_le" =
  let goal =
    make_goal [%term forall (fun (a : nat) (b : nat) -> nat_le (sub a b) a)]
  in
  run_proof ~name:"sub_le" ~notrace:true goal
    (with_term [%term (a : nat)] induct
    >>> intros
    >>> with_term [%term (b : nat)] induct
    >>> try_ intros >>> try_ assumption_reasoning
    >> with_proven [ "sub_Suc_Suc" ] rewrite
    >> spec_asm [%term (n0' : nat)]
    >> with_proven [ "le_weaken_Suc" ] apply
    >> assumption);
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le (sub x b) x

    Proof Complete!
    with fuel: 268
    |}]

let%expect_test "sub_lt" =
  let%thm sub_lt (b : nat) (a : nat) =
    nat_lt 0n b ==> (nat_le b a ==> nat_lt (sub a b) a)
  and proof =
    begin
      with_term [%term (b : nat)] induct
      >>> intros >> assumption_reasoning
      >> with_term [%term (a : nat)] destruct
      >> elim_disj_asm >> simp_asm >> simp >> assumption >> elim_exists_asm
      >> with_first (with_assumptions rewrite)
      >> with_first (with_assumptions rewrite)
      >> with_first (with_assumptions rewrite_asm)
      >> with_proven [ "sub_Suc_Suc" ] rewrite
      >> with_first (with_proven [ "le_Suc_Suc" ] rewrite_asm)
      >> with_term [%term (n0 : nat)] destruct
      >> elim_disj_asm >> simp >> elim_exists_asm
      >> with_proven [ "lt_weaken_Suc" ] apply
      >> spec_asm [%term (a0 : nat)]
      >> simp_asm >> simp
      >> with_repeat (with_assumptions (with_first_term apply_asm))
      >> assumption
    end
  in
  ignore sub_lt;
  [%expect
    {|
    ========================================
    ∀x. ∀a. nat_lt Zero x ==> nat_le x a ==> nat_lt (sub a x) a

    Proof Complete!
    with fuel: 438
    |}]

let%expect_test "sub_add_cancel" =
  let%thm sub_add_cancel (a : nat) (b : nat) =
    nat_le b a ==> (plus (sub a b) b = a)
  and proof =
    begin
      with_term [%term (a : nat)] induct
      >>> intros @: [ "hIH" ]
      >>> with_term [%term (b : nat)] induct
      >>> try_ intros >>> try_ assumption_reasoning
      >> (simp >> apply_at "eq_cong" >> apply_at "hIH" >> simp_asm >> simp)
    end
  in
  ignore sub_add_cancel;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le b x ==> plus (sub x b) b = x

    Proof Complete!
    with fuel: 406
    |}]

(* ===== Group 8: Ordering and addition ===== *)

let%expect_test "le_add_r" =
  let goal =
    make_goal [%term forall (fun (a : nat) (b : nat) -> nat_le a (plus a b))]
  in
  run_proof ~name:"le_add_r" ~notrace:true goal nat_induct_auto;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le x (plus x b)

    Proof Complete!
    with fuel: 126
    |}]

(* (* ===== Group 9: Totality ===== *) *)

let%expect_test "lt_total" =
  let%thm lt_total (a : nat) (b : nat) = nat_lt a b || nat_le b a
  and proof =
    begin
      with_term [%term (a : nat)] induct
      >>> intros
      >>> with_term [%term (b : nat)] induct
      >>> try_ intros
      >>= [
            right >> simp;
            left >> simp;
            right >> simp;
            spec_asm [%term (n0' : nat)]
            >> elim_disj_asm >> left
            >> with_proven [ "lt_Suc_Suc" ] rewrite
            >> assumption >> right
            >> with_proven [ "le_Suc_Suc" ] rewrite
            >> assumption;
          ]
    end
    [@notrace]
  in
  ignore lt_total;
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_lt x b ∨ nat_le b x

    Proof Complete!
    with fuel: 162
    |}]

let%expect_test "le_total" =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_le a b || nat_le b a)]
  in
  run_proof ~name:"le_total" ~notrace:true goal
    (with_term [%term (a : nat)] induct
    >>> intros
    >>> with_term [%term (b : nat)] induct
    >>> try_ intros
    >>= [
          right >> simp;
          left >> simp;
          right >> simp;
          spec_asm [%term (n0' : nat)]
          >> elim_disj_asm >> left
          >> with_proven [ "le_Suc_Suc" ] rewrite
          >> assumption >> right
          >> with_proven [ "le_Suc_Suc" ] rewrite
          >> assumption;
        ]);
  [%expect
    {|
    ========================================
    ∀x. ∀b. nat_le x b ∨ nat_le b x

    Proof Complete!
    with fuel: 157
    |}]

let%expect_test "div fuel sufficient" =
  let goal =
    make_goal
      [%term
        forall (fun (n : nat) (a : nat) (b : nat) ->
            nat_lt 0n b
            ==> (nat_lt a n ==> exists (fun (x : nat) -> div_aux n a b = Some x)))]
  in
  run_proof ~name:"div_fuel_sufficient" ~notrace:true goal
    (induct >> intros >> simp_asm >> false_elim >> intros >> simp >> cond
   >> simp >> with_term Nats.n0 exists >> refl >> simp
    >> with_first (with_proven [ "lt_Suc_le" ] rewrite_asm)
    >> with_first (with_proven [ "not_lt_is_le" ] rewrite_asm)
    >> (with_first (with_proven [ "sub_lt" ] apply_asm)
       >> with_first (with_assumptions apply_asm))
    >> (with_first (with_proven [ "lt_le_trans" ] apply_asm)
       >> with_nth_term 4 (with_assumptions apply_asm))
    >> with_nth_term 2 (spec_asm [%term sub (a : nat) (b : nat)])
    >> with_nth_term 0 (spec_asm [%term (b : nat)])
    >> with_first (with_assumptions apply_asm)
    >> with_first (with_assumptions apply_asm)
    >> elim_exists_asm >> simp
    >> with_term [%term Suc (x' : nat)] exists
    >> simp);
  [%expect
    {|
    ========================================
    ∀x. ∀a. ∀b. nat_lt Zero b ==> nat_lt a x ==> ∃x'. div_aux x a b = Some x'

    Proof Complete!
    with fuel: 218
    |}]

let%expect_test "div unfold" =
  let%thm div_unfold (a : nat) (b : nat) =
    nat_lt 0n b ==> (div a b = if nat_lt a b then 0n else Suc (div (sub a b) b))
  and proof =
    begin
      intros
      >> with_definition [ "div" ] rewrite
      >> beta
      >> with_first (with_definition [ "div_aux" ] rewrite)
      >> beta >> with_nth_choice 1 cond >> simp
      >> with_repeat @@ with_assumptions rewrite
      >> with_repeat @@ with_proven [ "cond_false" ] rewrite
      >> with_first (with_proven [ "not_lt_is_le" ] rewrite_asm)
      >> with_term [%term nat_lt (sub (a : nat) (b : nat)) (a : nat)] have
      >> with_proven [ "sub_lt" ] apply
      >> assumption >> assumption
      >> with_term
           [%term
             exists (fun (x' : nat) ->
                 div_aux (a : nat) (sub (a : nat) (b : nat)) (b : nat) = Some x')]
           have
      >> with_proven [ "div_fuel_sufficient" ] apply
      >> assumption >> assumption >> elim_exists_asm
      >> with_first (with_assumptions rewrite)
      >> with_first (with_definition [ "match_option" ] rewrite)
      >> beta
      >> with_first (with_definition [ "match_option" ] rewrite)
      >> beta
      >> with_term
           [%term
             exists (fun (x : nat) ->
                 div_aux
                   (Suc (sub (a : nat) (b : nat)))
                   (sub (a : nat) (b : nat))
                   (b : nat)
                 = Some x)]
           have
      >> with_proven [ "div_fuel_sufficient" ] apply
      >> assumption
      >> with_proven [ "lt_Suc_self" ] rewrite
      >> truth >> elim_exists_asm
      >> with_term
           [%term
             div_aux
               (plus
                  (Suc (sub (a : nat) (b : nat)))
                  (sub (a : nat) (Suc (sub (a : nat) (b : nat)))))
               (sub (a : nat) (b : nat))
               (b : nat)
             = Some (x : nat)]
           have
      >> with_proven [ "div_fuel_irrel" ] apply
      >> assumption
      >> with_term
           [%term
             plus
               (sub (a : nat) (Suc (sub (a : nat) (b : nat))))
               (Suc (sub (a : nat) (b : nat)))
             = (a : nat)]
           have
      >> with_proven [ "sub_add_cancel" ] apply
      >> with_proven [ "le_lt_Suc" ] rewrite
      >> with_proven [ "lt_Suc_Suc" ] rewrite
      >> assumption
      >> with_nth_choice 0 @@ with_proven [ "plus_comm" ] rewrite_asm
      >> with_first (with_assumptions rewrite_asm)
      >> with_first (with_assumptions rewrite_asm)
      >> with_first
           (with_rule (Options.option_def.injective |> List.hd) apply_asm)
      >> with_nth_term 4 (with_assumptions rewrite_asm)
      >> with_definition [ "div" ] rewrite
      >> beta >> with_assumptions rewrite >> simp
    end
  in
  ignore div_unfold;
  [%expect
    {|
    ========================================
    ∀a. ∀b. nat_lt Zero b ==> div a b = COND (nat_lt a b) Zero (Suc (div (sub a b) b))

    Proof Complete!
    with fuel: 262
    |}]

let%expect_test "merge test" =
  let goal =
    make_goal
      [%term
        merge_aux 9n
          (Cons (2n, Cons (4n, Nil)))
          (Cons (1n, Cons (2n, Cons (3n, Nil))))
        = Some (Cons (1n, Cons (2n, Cons (2n, Cons (3n, Cons (4n, Nil))))))]
  in
  let compute =
    try_
      (with_repeat
         (with_first
            (with_definition
               [ "match_list"; "match_option"; "nat_lt"; "match_nat" ]
               rewrite)))
    >> try_ (with_repeat beta)
    >> try_
         (with_repeat
            (with_first (with_proven [ "cond_false"; "cond_true" ] rewrite)))
    >> try_ (with_repeat beta)
    >> try_ (with_first (with_definition [ "merge_aux" ] rewrite))
    >> try_ (with_repeat beta)
    >> try_ refl
  in
  let proof = with_repeat compute in
  run_proof ~pretty:true ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    merge_aux 9 [2, 4] [1, 2, 3] = Some [1, 2, 2, 3, 4]

    Proof Complete!
    with fuel: 828
    |}]

let%expect_test "merge fuel irrel" =
  let rw_asm =
    with_first (with_assumptions rewrite)
    >> with_first (with_assumptions rewrite_asm)
  in
  let _ = rw_asm in
  let%thm merge_fuel_irrel (fuel : nat) (additional : nat) (xs : nat list)
      (ys : nat list) (x : nat list) =
    merge_aux fuel xs ys = Some x
    ==> (merge_aux (plus fuel additional) xs ys = Some x)
  and proof =
    begin
      with_term [%term (fuel : nat)] induct
      >> intros >> simp_asm >> discriminate >> intros
      >> with_term [%term (xs : nat list)] destruct
      >> elim_disj_asm >> simp >> simp_asm >> elim_exists_asm >> elim_exists_asm
      >> with_proven [ "add_Suc_l" ] rewrite
      >> rw_asm
      >> with_term [%term (ys : nat list)] destruct
      >> elim_disj_asm
      >> with_first (with_definition [ "merge_aux" ] rewrite)
      >> beta
      >> with_first (with_definition [ "merge_aux" ] rewrite_asm)
      >> beta >> simp >> beta_asm
      >> with_first (with_assumptions rewrite_asm)
      >> simp_asm >> elim_exists_asm >> elim_exists_asm >> rw_asm
      >> with_first (with_definition [ "merge_aux" ] rewrite)
      >> beta
      >> with_first (with_definition [ "merge_aux" ] rewrite_asm)
      >> beta_asm >> simp >> simp_asm >> cond >> rw_asm
      >> with_proven [ "cond_true" ] rewrite
      >> with_proven [ "cond_true" ] rewrite_asm
      >> with_term
           [%term
             merge_aux
               (n0 : nat)
               (a1 : nat list)
               (Cons ((a0' : nat), (a1' : nat list)))]
           destruct
      >> elim_disj_asm >> simp_asm >> discriminate >> elim_exists_asm
      >> simp_asm
      >> spec_asm [%term (additional : nat)]
      >> spec_asm [%term (a1 : nat list)]
      >> spec_asm [%term Cons ((a0' : nat), (a1' : nat list))]
      >> spec_asm [%term (a0 : nat list)]
      >> with_repeat (with_assumptions (with_first_term apply_asm))
      >> simp >> simp
      >> with_first (with_assumptions rewrite_asm)
      >> simp_asm
      >> with_term
           [%term
             merge_aux
               (n0 : nat)
               (Cons ((a0 : nat), (a1 : nat list)))
               (a1' : nat list)]
           destruct
      >> elim_disj_asm >> simp_asm >> discriminate >> elim_exists_asm
      >> simp_asm
      >> spec_asm [%term (additional : nat)]
      >> spec_asm [%term Cons ((a0 : nat), (a1 : nat list))]
      >> spec_asm [%term (a1' : nat list)]
      >> spec_asm [%term (a0 : nat list)]
      >> with_repeat (with_assumptions (with_first_term apply_asm))
      >> simp
    end
  in
  ignore merge_fuel_irrel;
  [%expect
    {|
    ========================================
    ∀x. ∀additional. ∀xs. ∀ys. ∀x. merge_aux x xs ys = Some x ==> merge_aux (plus x additional) xs ys = Some x

    Proof Complete!
    with fuel: 695
    |}]

let%expect_test "merge fuel sufficient" =
  let goal =
    make_goal
      [%term
        forall (fun (fuel : nat) (xs : nat list) (ys : nat list) ->
            nat_lt (plus (length xs) (length ys)) fuel
            ==> exists (fun (x : nat list) -> merge_aux fuel xs ys = Some x))]
  in
  run_proof ~name:"merge_fuel_sufficient" ~notrace:true goal
    (induct >> intros >> simp_asm >> false_elim >> intros >> simp
    >> with_term [%term (xs : nat list)] destruct
    >> elim_disj_asm >> simp
    >> with_term [%term (ys : nat list)] exists
    >> refl
    >> with_repeat elim_exists_asm
    >> simp
    >> with_term [%term (ys : nat list)] destruct
    >> elim_disj_asm >> simp
    >> with_term [%term Cons ((a0 : nat), (a1 : nat list))] exists
    >> refl
    >> with_repeat elim_exists_asm
    >> simp >> cond >> simp
    >> with_first (with_assumptions rewrite_asm)
    >> with_first (with_assumptions rewrite_asm)
    >> with_first (with_definition [ "length" ] rewrite_asm)
    >> with_proven [ "add_Suc_l" ] rewrite_asm
    >> with_proven [ "lt_Suc_Suc" ] rewrite_asm
    >> spec_asm [%term (a1 : nat list)]
    >> spec_asm [%term Cons ((a0' : nat), (a1' : nat list))]
    >> with_assumptions (with_first_term apply_asm)
    >> elim_exists_asm >> simp
    >> with_term [%term Cons ((a0 : nat), (x' : nat list))] exists
    >> refl >> simp
    >> with_first (with_assumptions rewrite_asm)
    >> with_first (with_assumptions rewrite_asm)
    >> with_proven [ "plus_comm" ] rewrite_asm
    >> with_first (with_definition [ "length" ] rewrite_asm)
    >> with_proven [ "add_Suc_l" ] rewrite_asm
    >> with_proven [ "plus_comm" ] rewrite_asm
    >> with_proven [ "lt_Suc_Suc" ] rewrite_asm
    >> spec_asm [%term Cons ((a0 : nat), (a1 : nat list))]
    >> spec_asm [%term (a1' : nat list)]
    >> with_assumptions (with_first_term apply_asm)
    >> elim_exists_asm >> simp
    >> with_term [%term Cons ((a0' : nat), (x' : nat list))] exists
    >> refl);
  [%expect
    {|
    ========================================
    ∀x. ∀xs. ∀ys. nat_lt (plus (length xs) (length ys)) x ==> ∃x. merge_aux x xs ys = Some x

    Proof Complete!
    with fuel: 437
    |}]

(*
what we want
    def merge : list nat -> list nat -> list nat
        | Nil => λys. ys
        | Cons h t =>
            match_list ys
                (Cons h t)
                (λy'. λys'. 
                    COND (nat_lt h 'y)
                        (Cons h (merge t (Cons y' ys')))
                        (Cons 'y (merge (Cons h t) ys')))

 *)
let%expect_test "merge unfolding lemma" =
  let goal =
    make_goal
      [%term
        forall (fun (xs : nat list) (ys : nat list) ->
            merge xs ys
            = match_list xs ys (fun (h : nat) (t : nat list) ->
                match_list ys
                  (Cons (h, t))
                  (fun (y' : nat) (ys' : nat list) ->
                    if nat_lt h y' then Cons (h, merge t (Cons (y', ys')))
                    else Cons (y', merge (Cons (h, t)) ys'))))]
  in
  run_proof ~name:"merge_unfold" ~notrace:true goal
    (intros
    >> with_term [%term (xs : nat list)] destruct
    >> with_term [%term (ys : nat list)] destruct
    >> with_repeat elim_disj_asm >> simp
    >> with_repeat elim_exists_asm
    >> simp
    >> with_repeat elim_exists_asm
    >> simp
    >> with_repeat elim_exists_asm
    >> with_definition [ "merge" ] rewrite
    >> beta
    >> with_first (with_definition [ "merge_aux" ] rewrite)
    >> with_repeat (with_first (with_assumptions rewrite))
    >> simp ~exclude:[ "merge"; "merge_aux" ]
    >> cond
    >> simp ~exclude:[ "merge"; "merge_aux" ]
    >> with_term
         [%term
           exists (fun (x : nat list) ->
               merge_aux
                 (Suc
                    (Suc
                       (plus (length (a1' : nat list)) (length (a1 : nat list)))))
                 (a1' : nat list)
                 (Cons ((a0 : nat), (a1 : nat list)))
               = Some x)]
         have
    >> with_proven [ "merge_fuel_sufficient" ] apply
    >> simp >> elim_exists_asm
    >> with_first (with_assumptions rewrite)
    >> simp ~exclude:[ "merge"; "merge_aux" ]
    >> with_definition [ "merge" ] rewrite
    >> beta
    >> with_first (with_definition [ "length" ] rewrite)
    >> rewrite_at "plus_Suc"
    >> with_first (with_assumptions rewrite)
    >> simp
    >> simp ~exclude:[ "merge"; "merge_aux" ]
    >> with_term
         [%term
           exists (fun (x : nat list) ->
               merge_aux
                 (Suc
                    (Suc
                       (plus (length (a1' : nat list)) (length (a1 : nat list)))))
                 (Cons ((a0' : nat), (a1' : nat list)))
                 (a1 : nat list)
               = Some x)]
         have
    >> apply_at "merge_fuel_sufficient"
    >> simp >> elim_exists_asm
    >> with_first (with_assumptions rewrite)
    >> simp ~exclude:[ "merge"; "merge_aux" ]
    >> with_definition [ "merge" ] rewrite
    >> beta
    >> with_first (with_definition [ "length" ] rewrite)
    >> with_first (with_definition [ "plus" ] rewrite)
    >> beta
    >> with_first (with_assumptions rewrite)
    >> simp);
  [%expect
    {|
    ========================================
    ∀xs. ∀ys. merge xs ys = match_list xs ys (λh. λt. match_list ys (Cons h t) (λy'. λys'. COND (nat_lt h y') (Cons h (merge t (Cons y' ys'))) (Cons y' (merge (Cons h t) ys'))))

    Proof Complete!
    with fuel: 1278
    |}]

(* sort [3,1,2] = [1,2,3] *)
let%expect_test "merge sort [3,1,2] = [1,2,3]" =
  let rw_def r =
    with_first (with_definition [ r ] rewrite) >> try_ (with_repeat beta)
  in
  let rw_thm r =
    with_first (with_proven [ r ] rewrite) >> try_ (with_repeat beta)
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

  let goal =
    make_goal
      [%term
        merge_sort_aux 8n (Cons (3n, Cons (1n, Cons (2n, Nil))))
        = Some (Cons (1n, Cons (2n, Cons (3n, Nil))))]
  in
  run_proof ~pretty:true ~notrace:true goal
    (rw_def "merge_sort_aux" >> simp ~exclude
    >> with_repeat @@ rw_def "div"
    >> with_repeat @@ rw_def "div_aux"
    >> simp ~exclude >> rw_def "merge_sort_aux" >> simp ~exclude
    >> rw_def "merge_sort_aux" >> simp ~exclude
    >> with_repeat @@ rw_def "div"
    >> with_repeat @@ rw_def "div_aux"
    >> simp ~exclude >> rw_def "merge_sort_aux" >> simp ~exclude
    >> rw_def "merge_sort_aux" >> simp ~exclude >> rw_thm "merge_unfold"
    >> simp ~exclude >> rw_thm "merge_unfold" >> simp ~exclude
    >> rw_thm "merge_unfold" >> simp ~exclude >> rw_thm "merge_unfold"
    >> simp ~exclude >> rw_thm "merge_unfold" >> simp ~exclude
    >> rw_thm "merge_unfold" >> simp ~exclude);
  [%expect
    {|
    ========================================
    merge_sort_aux 8 [3, 1, 2] = Some [1, 2, 3]

    Proof Complete!
    with fuel: 1353
    |}]

let%expect_test "length take" =
  let n = [%term (n : nat)] in
  let n1 = [%term (n1 : nat list)] in
  let xs = [%term (xs : nat list)] in
  let gtake =
    make_goal
      [%term
        forall (fun (n : nat) (xs : nat list) ->
            length (take n xs) = if nat_lt n (length xs) then n else length xs)]
  in
  let gdrop =
    make_goal
      [%term
        forall (fun (n : nat) (xs : nat list) ->
            length (drop n xs) = sub (length xs) n)]
  in
  run_proof ~name:"length_take" ~notrace:true gtake
    (with_term n induct >>> try_ intros >>> with_term xs induct >>> try_ intros
   >>> try_ assumption_reasoning
    >> with_repeat (with_first (with_definition [ "take"; "length" ] rewrite))
    >> beta
    >> with_repeat (with_first (with_definition [ "match_list" ] rewrite))
    >> beta
    >> with_first (with_definition [ "length" ] rewrite)
    >> spec_asm n1 >> with_assumptions rewrite
    >> with_first (with_proven [ "lt_Suc_Suc" ] rewrite)
    >> cond >> simp >> simp);
  run_proof ~name:"length_drop" ~notrace:true gdrop
    (with_term n induct >>> try_ intros >>> with_term xs induct >>> try_ intros
   >>> try_ assumption_reasoning
    >> with_repeat (with_first (with_definition [ "take"; "length" ] rewrite))
    >> beta
    >> with_repeat (with_first (with_definition [ "match_list" ] rewrite))
    >> beta
    >> with_first (with_definition [ "length" ] rewrite)
    >> spec_asm n1 >> with_assumptions rewrite
    >> with_first (with_proven [ "lt_Suc_Suc" ] rewrite)
    >> cond >> simp >> simp);
  [%expect
    {|
    ========================================
    ∀x. ∀xs. length (take x xs) = COND (nat_lt x (length xs)) x (length xs)

    Proof Complete!
    with fuel: 570
    ========================================
    ∀x. ∀xs. length (drop x xs) = sub (length xs) x

    Proof Complete!
    with fuel: 237
    |}]

let%expect_test "div_pos" =
  let%thm div_pos (n : nat) = nat_lt 1n n ==> nat_lt 0n (div n 2n)
  and proof =
    begin
      with_term [%term (n : nat)] induct
      >>> intros >>> try_ assumption_reasoning
      >> with_term
           [%term
             div (Suc (n0 : nat)) 2n
             =
             if nat_lt (Suc (n0 : nat)) 2n then 0n
             else Suc (div (sub (Suc (n0 : nat)) 2n) 2n)]
           have
      >> with_first (with_proven [ "div_unfold" ] apply)
      >> simp >> with_assumptions rewrite >> cond >> simp_asm
      >> with_first eq_true_elim_asm
      >> with_first (with_proven [ "le_Zero_eq" ] apply_asm)
      >> simp_asm >> false_elim >> with_assumptions rewrite
      >> with_proven [ "cond_false" ] rewrite
      >> simp ~exclude:[ "div" ]
    end
  in
  ignore div_pos;
  [%expect
    {|
    ========================================
    ∀x. nat_lt (Suc Zero) x ==> nat_lt Zero (div x (Suc (Suc Zero)))

    Proof Complete!
    with fuel: 799
    |}]

let apply_asm_to_asm ~asm_thm ~asm_to =
  with_nth_choice asm_thm (with_nth_term asm_to (with_assumptions apply_asm))

let%expect_test "div_le" =
  let%thm div_le (n : nat) (k : nat) (m : nat) =
    nat_lt 0n m ==> (nat_le k n ==> nat_le (div k m) n)
  and proof =
    begin
      with_term [%term (n : nat)] induct
      >> intros
      >> with_first (with_proven [ "le_Zero_eq" ] apply_asm)
      >> simp
      >> with_term [%term (m : nat)] destruct
      >> elim_disj_asm >> simp >> elim_exists_asm >> simp >> intros
      >> with_term [%term nat_lt (k : nat) (m : nat)] cases
      >> with_term
           [%term
             div (k : nat) (m : nat)
             =
             if nat_lt (k : nat) (m : nat) then 0n
             else Suc (div (sub (k : nat) (m : nat)) (m : nat))]
           have
      >> with_first (with_proven [ "div_unfold" ] apply)
      >> assumption
      >> with_first (with_assumptions rewrite)
      >> with_first (with_assumptions rewrite)
      >> simp
      >> with_term
           [%term
             div (k : nat) (m : nat)
             =
             if nat_lt (k : nat) (m : nat) then 0n
             else Suc (div (sub (k : nat) (m : nat)) (m : nat))]
           have
      >> with_first (with_proven [ "div_unfold" ] apply)
      >> assumption
      >> with_first (with_assumptions rewrite)
      >> with_first (with_assumptions rewrite)
      >> simp ~exclude:[ "div"; "div_unfold" ]
      >> with_term [%term nat_le (sub (k : nat) (m : nat)) (n0 : nat)] have
      >> with_first (with_proven [ "not_lt_is_le" ] rewrite_asm)
      >> with_term [%term nat_lt (sub (k : nat) (m : nat)) (k : nat)] have
      >> with_proven [ "sub_lt" ] apply
      >> assumption >> assumption
      >> with_specialized ~name:"lt_le_trans"
           ~specs:
             [
               [%term sub (k : nat) (m : nat)];
               [%term (k : nat)];
               [%term Suc (n0 : nat)];
             ]
           apply_asm
      >> apply_asm_to_asm ~asm_thm:0 ~asm_to:4
      >> with_first
           (with_proven [ "lt_Suc_le" ]
              (with_info_trace (with_flip_rules rewrite)))
      >> assumption
      >> spec_asm [%term sub (k : nat) (m : nat)]
      >> spec_asm [%term (m : nat)]
      >> with_repeat (with_assumptions (with_first_term apply_asm))
      >> assumption
    end
  in
  ignore div_le;

  [%expect
    {|
    ========================================
    ∀x. ∀k. ∀m. nat_lt Zero m ==> nat_le k x ==> nat_le (div k m) x

    Proof Complete!
    with fuel: 354
    |}]

let%expect_test "div_lt" =
  let%thm div_lt (n : nat) = nat_lt 1n n ==> nat_lt (div n 2n) n
  and proof =
    begin
      with_term [%term (n : nat)] induct
      >> intros >> assumption_reasoning >> intros
      >> with_term [%term (n0 : nat)] destruct
      >> elim_disj_asm >> simp
      >> with_repeat elim_exists_asm
      >> with_repeat (with_assumptions (with_first rewrite))
      >> with_repeat (with_assumptions (with_first rewrite_asm))
      >> with_term
           [%term
             div (Suc (Suc (a0 : nat))) 2n
             =
             if nat_lt (Suc (Suc (a0 : nat))) 2n then 0n
             else Suc (div (sub (Suc (Suc (a0 : nat))) 2n) 2n)]
           have
      >> with_first (with_proven [ "div_unfold" ] apply)
      >> simp
      >> with_term [%term (a0 : nat)] destruct
      >> elim_disj_asm >> simp
      >> with_repeat elim_exists_asm
      >> with_repeat (with_first (with_assumptions rewrite_asm))
      >> with_repeat (with_first (with_proven [ "lt_Suc_Suc" ] rewrite_asm))
      >> with_first (with_nth_term 0 (with_definition [ "nat_lt" ] rewrite_asm))
      >> beta_asm
      >> with_first
           (with_nth_term 0 (with_definition [ "match_nat" ] rewrite_asm))
      >> try_ beta_asm
      >> with_first (with_nth_term 0 (with_proven [ "cond_false" ] rewrite_asm))
      >> try_ beta_asm
      >> with_first (with_assumptions rewrite)
      >> with_first (with_assumptions rewrite)
      >> with_proven [ "lt_Suc_Suc" ] rewrite
      >> simp ~exclude:[ "nat_lt"; "div" ]
      >> with_repeat (with_assumptions (with_flip_rules (with_first rewrite)))
      >> with_proven [ "div_le" ] apply
      >> simp >> simp
    end
  in
  ignore div_lt;
  [%expect
    {|
    ========================================
    ∀x. nat_lt (Suc Zero) x ==> nat_lt (div x (Suc (Suc Zero))) x

    Proof Complete!
    with fuel: 589
    |}]

let%expect_test "merge sort sufficient" =
  let%thm merge_sort_fuel_sufficient (fuel : nat) (xs : nat list) =
    nat_lt (length xs) fuel
    ==> exists (fun (x : nat list) -> merge_sort_aux fuel xs = Some x)
  and proof =
    begin
      induct >> intros >> simp_asm >> false_elim >> intros
      >> with_first (with_definition [ "merge_sort_aux" ] rewrite)
      >> beta >> cond
      >> with_first (with_assumptions rewrite)
      >> simp ~exclude:[ "merge_sort_aux"; "take"; "drop"; "div"; "merge" ]
      >> with_term [%term (xs : nat list)] exists
      >> refl
      >> with_first (with_assumptions rewrite)
      >> simp ~exclude:[ "merge_sort_aux"; "take"; "drop"; "div"; "merge" ]
      >> spec_asm [%term take (div (length (xs : nat list)) 2n) (xs : nat list)]
      >> spec_asm [%term drop (div (length (xs : nat list)) 2n) (xs : nat list)]
      >> (with_term
            [%term
              nat_lt
                (length
                   (take (div (length (xs : nat list)) 2n) (xs : nat list)))
                (n0 : nat)]
            have
         >> with_first (with_proven [ "not_le_is_lt" ] rewrite_asm)
         >> with_first (with_proven [ "div_lt" ] apply_asm)
         >> with_proven [ "length_take" ] rewrite
         >> with_nth_term 0 (with_proven [ "eq_true_intro" ] apply_asm)
         >> with_assumptions rewrite >> simp ~exclude:[ "div" ]
         >> with_first (with_proven [ "lt_Suc_le" ] rewrite_asm)
         >> with_specialized ~name:"lt_le_trans"
              ~specs:
                [
                  [%term div (length (xs : nat list)) 2n];
                  [%term length (xs : nat list)];
                  [%term (n0 : nat)];
                ]
              apply
         >> with_first (with_assumptions rewrite)
         >> truth >> assumption)
      >> with_term
           [%term
             nat_lt
               (length (drop (div (length (xs : nat list)) 2n) (xs : nat list)))
               (n0 : nat)]
           have
      >> with_first (with_proven [ "not_le_is_lt" ] rewrite_asm)
      >> with_first (with_proven [ "div_pos" ] apply_asm)
      >> with_proven [ "length_drop" ] rewrite
      >> with_term
           [%term
             nat_lt
               (sub (length (xs : nat list)) (div (length (xs : nat list)) 2n))
               (length (xs : nat list))]
           have
      >> with_first (with_proven [ "sub_lt" ] apply)
      >> assumption
      >> with_proven [ "div_le" ] apply
      >> simp >> simp
      >> with_first (with_proven [ "lt_Suc_le" ] rewrite_asm)
      >> with_specialized ~name:"lt_le_trans"
           ~specs:
             [
               [%term
                 sub (length (xs : nat list)) (div (length (xs : nat list)) 2n)];
               [%term length (xs : nat list)];
               [%term (n0 : nat)];
             ]
           apply
      >> assumption >> assumption
      >> with_repeat (with_first (with_assumptions (with_first_term apply_asm)))
      >> with_repeat elim_exists_asm
      >> simp ~exclude:[ "div"; "merge" ]
      >> with_term [%term merge (x' : nat list) (x'' : nat list)] exists
      >> refl
    end
  in
  ignore merge_sort_fuel_sufficient;
  [%expect
    {|
    ========================================
    ∀x. ∀xs. nat_lt (length xs) x ==> ∃x. merge_sort_aux x xs = Some x

    Proof Complete!
    with fuel: 309
    |}]

let%expect_test "merge sort fuel irrel" =
  let goal =
    make_goal
      [%term
        forall
          (fun (fuel : nat) (additional : nat) (xs : nat list) (x : nat list) ->
            merge_sort_aux fuel xs = Some x
            ==> (merge_sort_aux (plus fuel additional) xs = Some x))]
  in
  let proof = sorry in
  (*TODO: finish this one*)
  run_proof ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀fuel. ∀additional. ∀xs. ∀x. merge_sort_aux fuel xs = Some x ==> merge_sort_aux (plus fuel additional) xs = Some x

    Proof Complete!
    with fuel: 1
    |}]

let%expect_test "merge sort unfold" =
  let%thm merge_sort_unfold (xs : nat list) =
    merge_sort xs
    =
    if nat_le (length xs) 1n then xs
    else
      (fun (half_length : nat) ->
        merge
          (merge_sort (take half_length xs))
          (merge_sort (drop half_length xs)))
        (div (length xs) 2n)
  and proof =
    begin
      intros
      >> with_definition [ "merge_sort" ] rewrite
      >> beta
      >> with_first (with_definition [ "merge_sort_aux" ] rewrite)
      >> beta >> cond
      >> with_repeat (with_first (with_assumptions rewrite))
      >> simp ~exclude:[ "merge_sort"; "merge"; "merge_sort_aux"; "div" ]
      >> simp ~exclude:[ "merge_sort"; "merge"; "merge_sort_aux"; "div" ]
      >> with_term
           [%term
             merge_sort_aux
               (length (xs : nat list))
               (take (div (length (xs : nat list)) 2n) (xs : nat list))
             = Some
                 (merge_sort
                    (take (div (length (xs : nat list)) 2n) (xs : nat list)))]
           have
      >> with_definition [ "merge_sort" ] rewrite
      >> beta
      >> with_term
           [%term
             exists (fun (z : nat list) ->
                 merge_sort_aux
                   (Suc
                      (length
                         (take
                            (div (length (xs : nat list)) 2n)
                            (xs : nat list))))
                   (take (div (length (xs : nat list)) 2n) (xs : nat list))
                 = Some z)]
           have
      >> with_proven [ "merge_sort_fuel_sufficient" ] apply
      >> simp >> elim_exists_asm >> with_assumptions rewrite
      >> simp ~exclude:[ "merge_sort"; "merge"; "merge_sort_aux"; "div" ]
      >> with_term
           [%term
             plus
               (Suc
                  (length
                     (take (div (length (xs : nat list)) 2n) (xs : nat list))))
               (sub
                  (length (xs : nat list))
                  (Suc
                     (length
                        (take (div (length (xs : nat list)) 2n) (xs : nat list)))))
             = length (xs : nat list)]
           have
      >> with_proven [ "plus_comm" ] rewrite
      >> with_proven [ "sub_add_cancel" ] apply
      >> with_proven [ "length_take" ] rewrite
      >> sorry >> sorry >> sorry
    end
  in
  ignore merge_sort_unfold;
  [%expect
    {|
    ========================================
    ∀xs. merge_sort xs = COND (nat_le (length xs) (Suc Zero)) xs ((λhalf_length. merge (merge_sort (take half_length xs)) (merge_sort (drop half_length xs))) (div (length xs) (Suc (Suc Zero))))

    Proof Complete!
    with fuel: 189
    |}]
