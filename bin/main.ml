open Heft
open Kernel
open Derived
open Tactic
open Heft_theories
open Theories

let () =
  let goal = make_goal [%term forall (fun (a : nat) -> true)] in
  run_proof ~notrace:true goal (intros_tac >> truth_tac)

let () =
  let goal =
    let bool_ty = Result.get_ok (make_type "bool" []) in
    let p = make_var "P" bool_ty in
    let t_const = Result.get_ok (make_const "T" []) in
    make_goal
      (make_forall p (make_imp p (Result.get_ok (safe_make_eq p t_const))))
  in
  run_proof ~name:"eq_true_intro" ~notrace:true goal
    (intros_tac >> eq_true_elim_tac >> assumption_tac)

let () =
  let goal = make_goal [%term forall (fun (x : nat) -> plus x Zero = x)] in
  run_proof ~name:"plus_x_Zero" goal
    (induct_tac >> simp_tac >> gen_tac >> intro_tac >> simp_tac)

let () =
  let goal = make_goal [%term plus 2n 3n = 5n] in
  run_proof ~pretty:true goal simp_tac

let () =
  let goal =
    make_goal
      [%term
        forall (fun (x : nat) (y : nat) (z : nat) ->
            plus x (plus y z) = plus (plus x y) z)]
  in
  run_proof ~name:"plus_assoc" goal
    (with_term x induct_tac >> intros_tac >> simp_tac >> intros_tac >> simp_tac)

let () =
  let goal =
    make_goal
      [%term forall (fun (x : nat) (y : nat) -> Suc x = Suc y ==> (x = y))]
  in
  run_proof ~name:"Suc_inj" goal
    (intros_tac
    >> (apply_thm_tac |> with_rules NatTheory.nat_def.injective)
    >> assumption_tac)

(* Lemma needed for commutativity: plus x (Suc y) = Suc (plus x y) *)
let () =
  let goal =
    make_goal
      [%term
        forall (fun (x : nat) (y : nat) -> plus x (Suc y) = Suc (plus x y))]
  in
  run_proof ~name:"plus_Suc" goal
    (induct_tac >> gen_tac >> simp_tac >> intros_tac >> simp_tac)

let () =
  let goal =
    make_goal
      [%term forall (fun (x : nat) (y : nat) -> x = y ==> (Suc x = Suc y))]
  in
  run_proof ~name:"Suc_inj_rev" goal
    (intros_tac >> (rewrite_tac |> with_assumptions) >> refl_tac)

(* Commutativity: plus x y = plus y x *)
let () =
  let goal =
    make_goal [%term forall (fun (x : nat) (y : nat) -> plus x y = plus y x)]
  in
  run_proof ~name:"plus_comm" goal
    (induct_tac >> gen_tac >> simp_tac
    >> with_first (with_proven [ "plus_x_Zero" ] rewrite_tac)
    >> refl_tac >> intros_tac >> simp_tac >> sym_tac
    >> with_first (with_proven [ "plus_Suc" ] apply_thm_tac))

let () =
  let goal =
    make_goal
      [%term
        forall (fun (x : nat) (y : nat) (z : nat) ->
            plus x y = plus x z ==> (y = z))]
  in
  run_proof goal
    (induct_tac >> simp_tac >> intros_tac >> assumption_tac >> intros_tac
   >> simp_asm_tac
    >> with_first (with_proven [ "Suc_inj" ] apply_thm_asm_tac)
    >> with_first (with_assumptions apply_thm_asm_tac)
    >> assumption_tac)

let () =
  let goal =
    make_goal
      [%term
        forall (fun (x : nat) (y : nat) (z : nat) ->
            plus y x = plus z x ==> (y = z))]
  in
  run_proof goal
    (induct_tac >> gen_tac
    >> with_proven [ "plus_x_Zero" ] simp_tac
    >> intros_tac >> assumption_tac >> intros_tac
    >> with_proven [ "plus_Suc" ] rewrite_asm_tac
    >> with_proven [ "plus_Suc" ] rewrite_asm_tac
    >> with_proven [ "Suc_inj" ] apply_thm_asm_tac
    >> with_first (with_assumptions apply_thm_tac)
    >> assumption_tac)

(* xs = Nil ==> length xs = Zero *)
let () =
  let goal =
    make_goal
      [%term forall (fun (xs : 'a list) -> xs = Nil ==> (length xs = Zero))]
  in
  run_proof goal (intros_tac >> simp_tac ~with_asms:true)

(* length xs = Zero ==> xs = Nil *)
let () =
  let goal =
    make_goal
      [%term forall (fun (xs : 'a list) -> length xs = Zero ==> (xs = Nil))]
  in
  run_proof goal
    (induct_tac >> intros_tac >> refl_tac >> intros_tac >> simp_asm_tac
   >> sym_asm_tac
    >> with_first (with_rules NatTheory.nat_def.distinct rewrite_asm_tac)
    >> false_elim_tac)

let () =
  let goal =
    make_goal [%term forall (fun (xs : 'a list) -> append Nil xs = xs)]
  in
  run_proof goal (intros_tac >> simp_tac)

let () =
  let goal =
    make_goal
      [%term
        forall (fun (x : 'a) (xs : 'a list) (ys : 'a list) ->
            append (Cons (x, xs)) ys = Cons (x, append xs ys))]
  in
  run_proof ~name:"append_cons" goal (intros_tac >> simp_tac)

let () =
  let goal =
    make_goal [%term forall (fun (xs : 'a list) -> append xs Nil = xs)]
  in
  run_proof ~name:"append_xs_Nil" goal
    (induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "append_cons" ] rewrite_tac
    >> with_proven [ "append_cons" ] simp_tac)

let () =
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
        ])

let () =
  let goal =
    make_goal
      [%term
        forall (fun (xs : 'a list) (ys : 'a list) (zs : 'a list) ->
            length (append xs ys) = plus (length xs) (length ys))]
  in
  run_proof ~name:"append_length" goal
    (induct_tac
    >> with_no_automation_trace auto_dfs_tac
    >> with_no_automation_trace auto_dfs_tac)

let () =
  let goal =
    make_goal
      [%term forall (fun (x : 'a list) -> length (reverse x) = length x)]
  in
  run_proof goal
    (induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "append_length" ] simp_tac
    >> with_first (with_proven [ "plus_comm" ] rewrite_tac)
    >> simp_tac)

let () =
  let goal =
    make_goal
      [%term
        forall (fun (xs : 'a list) (ys : 'a list) ->
            reverse (append xs ys) = append (reverse ys) (reverse xs))]
  in
  run_proof ~name:"append_reverse" goal
    (induct_tac >> intros_tac
    >> with_proven [ "append_xs_Nil" ] simp_tac
    >> intros_tac >> simp_tac
    >> with_first (with_proven [ "append_assoc" ] apply_thm_tac))

let () =
  let goal =
    make_goal [%term forall (fun (xs : 'a list) -> reverse (reverse xs) = xs)]
  in
  run_proof goal
    (induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "append_reverse" ] simp_tac)

let () =
  let goal =
    make_goal
      [%term
        forall (fun (x : 'a) (y : 'a) ->
            x = y ==> (fst (Pair (x, y)) = snd (Pair (x, y))))]
  in
  run_proof goal (intros_tac >> simp_tac)

let () =
  let goal = make_goal [%term pred 3n = 2n] in
  run_proof ~pretty:true goal simp_tac

let () =
  let goal = make_goal [%term minus 4n 3n = 1n] in
  run_proof ~pretty:true goal simp_tac

let () =
  let goal = make_goal [%term forall (fun (n : nat) -> minus n Zero = n)] in
  run_proof ~name:"minus_Zero" goal
    (induct_tac
    >> with_no_automation_trace auto_dfs_tac
    >> with_no_automation_trace auto_dfs_tac)

(* n - (Suc m) = (n - m) - 1 *)
let () =
  let goal =
    make_goal
      [%term
        forall (fun (n : nat) (m : nat) -> minus n (Suc m) = pred (minus n m))]
  in
  run_proof ~name:"minus_Suc_right" goal
    (induct_tac
    >> with_proven [ "minus_Zero" ] (with_no_automation_trace auto_dfs_tac)
    >> with_no_automation_trace auto_dfs_tac)

(* (Suc n) - (Suc m) = n - m *)
let () =
  let goal =
    make_goal
      [%term
        forall (fun (n : nat) (m : nat) -> minus (Suc n) (Suc m) = minus n m)]
  in
  run_proof ~name:"minus_Suc_Suc" goal
    (gen_tac >> induct_tac
    >> with_proven [ "minus_Zero" ] simp_tac
    >> intros_tac
    >> with_proven [ "minus_Suc_right" ] rewrite_tac
    >> with_assumptions rewrite_tac
    >> with_proven [ "minus_Suc_right" ] rewrite_tac
    >> refl_tac)

let () =
  let goal = make_goal [%term forall (fun (n : nat) -> minus n n = Zero)] in
  run_proof ~name:"minus_self" goal
    (induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "minus_Suc_Suc" ] simp_tac
    >> simp_asm_tac ~with_asms:false)

let () =
  let goal =
    make_goal [%term forall (fun (x : nat) (n : nat) -> minus (plus x n) n = x)]
  in
  run_proof goal
    (gen_tac >> induct_tac
    >> with_proven [ "plus_x_Zero"; "minus_Zero" ] simp_tac
    >> intros_tac
    >> with_proven [ "plus_Suc" ] rewrite_tac
    >> with_proven [ "minus_Suc_Suc" ] rewrite_tac
    >> assumption_tac)

let () =
  let goal = make_goal [%term twice pred 2n = 0n] in
  run_proof goal simp_tac

let () =
  let goal =
    make_goal
      [%term
        forall (fun (f : 'a -> 'b -> 'c) (x : 'a) (y : 'b) ->
            flip f y x = f x y)]
  in
  run_proof ~name:"flip_f" goal (intros_tac >> simp_tac)

let () =
  let goal = make_goal [%term not (true = false)] in
  let t = true_def |> Result.get_ok in
  run_proof goal
    (neg_intro_tac
    >> with_assumptions (with_flip_rules rewrite_tac)
    >> with_rule t rewrite_tac >> refl_tac)

let () =
  let goal = make_goal [%term nat_le 0n 1n] in
  run_proof ~notrace:true goal simp_tac

let () =
  let goal = make_goal [%term not (nat_le 3n 1n)] in
  run_proof ~pretty:true ~notrace:true goal
    (simp_tac >> neg_intro_tac >> assumption_tac)

(* insert 3 into [] = [3] *)
let () =
  let goal = make_goal [%term insert Nil 3n = Cons (3n, Nil)] in
  run_proof ~pretty:true ~notrace:true goal simp_tac

(* insert 2 into [1] = [1, 2] *)
let () =
  let goal =
    make_goal [%term insert (Cons (1n, Nil)) 2n = Cons (1n, Cons (2n, Nil))]
  in
  run_proof ~pretty:true ~notrace:true goal simp_tac

let () =
  let goal = make_goal [%term sub 4n 3n = 1n] in
  run_proof ~pretty:true goal simp_tac

let () =
  let goal = make_goal [%term forall (fun (x : nat) -> minus 0n x = 0n)] in
  run_proof ~name:"minus_Zero_left" goal
    (induct_tac >> simp_tac >> intros_tac
    >> simp_asm_tac ~with_asms:false
    >> simp_tac ~with_asms:false
    >> with_assumptions rewrite_tac
    >> simp_tac)

let () =
  let goal =
    make_goal [%term forall (fun (x : nat) (n : nat) -> sub x n = minus x n)]
  in
  run_proof goal
    (induct_tac
    >>= [
          with_proven [ "minus_Zero_left" ] simp_tac >>> gen_tac >>> refl_tac;
          gen_tac >> intro_tac >> induct_tac
          >>= [
                with_proven [ "minus_Zero" ] simp_tac;
                intros_tac
                >> with_proven [ "minus_Suc_Suc" ] rewrite_tac
                >> simp_tac;
              ];
        ])

(* isort [] = [] *)
let () =
  let goal = make_goal [%term isort Nil = Nil] in
  run_proof goal simp_tac

(* isort [3,1,2] = [1,2,3] *)
let () =
  let goal =
    make_goal
      [%term
        isort (Cons (3n, Cons (1n, Cons (2n, Nil))))
        = Cons (1n, Cons (2n, Cons (3n, Nil)))]
  in
  run_proof ~pretty:true goal simp_tac

let () =
  let goal = make_goal [%term eqb true false = false] in
  run_proof goal simp_tac

let () =
  let goal =
    make_goal [%term forall (fun (b : bool) -> b = true || b = false)]
  in

  run_proof ~name:"bool_cases_test" goal
    (cases_tac >>= [ left_tac >> refl_tac; right_tac >> refl_tac ])

let () =
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
        ])

let () =
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
        ])

let () =
  let goal =
    make_goal [%term forall (fun (l : nat list) -> sorted (isort l))]
  in
  run_proof goal
    (induct_tac >> simp_tac >> intros_tac >> simp_tac
    >> with_proven [ "sort_correct_lemma" ] apply_thm_tac
    >> assumption_tac)

let () =
  let goal =
    make_goal
      [%term
        forall (fun (o : 'a option) ->
            (not (o = None)) ==> exists (fun (x : 'a) -> o = Some x))]
  in
  run_proof goal
    (intros_tac
    >> with_arbitrary_term [%term (o : 'a option)] destruct_tac
    >> elim_disj_asm_tac >> neg_elim_tac >> elim_exists_asm_tac
    >> with_arbitrary_term [%term (a0 : 'a)] exists_tac
    >> assumption_tac)

let () =
  let goal =
    make_goal
      [%term
        forall (fun (n : nat) (m : nat) (a : nat) (b : nat) (x : nat) ->
            div_aux n a b = Some x ==> (div_aux (plus n m) a b = Some x))]
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
    >> simp_asm_tac >> simp_asm_tac)

let () =
  let n0 = [%term (n0 : nat)] in
  let goal =
    make_goal
      [%term
        forall (fun (b : nat) ->
            nat_lt 0n b ==> exists (fun (x : nat) -> b = Suc x))]
  in
  run_proof ~simp:true ~name:"lt_Zero_Suc" ~notrace:true goal
    (induct_tac >> intros_tac >> simp_asm_tac >> false_elim_tac >> intros_tac
    >> with_arbitrary_term n0 exists_tac
    >> refl_tac)

let nat_induct_auto_tac =
  induct_tac
  >> with_no_automation_trace auto_dfs_tac
  >> with_no_automation_trace auto_dfs_tac

let () =
  let goal =
    make_goal
      [%term forall (fun (x : nat) (b : nat) -> b = Suc x ==> nat_lt 0n b)]
  in
  run_proof ~simp:true ~name:"Suc_lt_Zero" ~notrace:true goal
    nat_induct_auto_tac

let () =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_lt a Zero = false)]
  in
  run_proof ~simp:true ~name:"lt_Zero_false" ~notrace:true goal
    nat_induct_auto_tac

let () =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_lt a (plus a (Suc b)))]
  in
  run_proof ~name:"lt_add_Suc_r" ~notrace:true goal nat_induct_auto_tac

let () =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_lt (plus a b) (plus a c) = nat_lt b c)]
  in
  run_proof ~name:"add_lt_cancel_l" ~notrace:true goal nat_induct_auto_tac

let () =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_le (plus a b) (plus a c) = nat_le b c)]
  in
  run_proof ~name:"add_le_cancel_l" ~notrace:true goal nat_induct_auto_tac

(* ===== Group 1: Basic computation rules ===== *)

let () =
  let goal = make_goal [%term forall (fun (a : nat) -> sub a 0n = a)] in
  run_proof ~simp:true ~name:"sub_Zero_r" ~notrace:true goal nat_induct_auto_tac

let () =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> sub (Suc a) (Suc b) = sub a b)]
  in
  run_proof ~simp:true ~name:"sub_Suc_Suc" ~notrace:true goal
    nat_induct_auto_tac

let () =
  let goal = make_goal [%term forall (fun (a : nat) -> sub Zero a = 0n)] in
  run_proof ~simp:true ~name:"sub_Zero_l" ~notrace:true goal nat_induct_auto_tac

let () =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_lt 0n (Suc a) = true)]
  in
  run_proof ~simp:true ~name:"lt_Zero_Suc" ~notrace:true goal
    nat_induct_auto_tac

let () =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_lt (Suc a) (Suc b) = nat_lt a b)]
  in
  run_proof ~simp:true ~name:"lt_Suc_Suc" ~notrace:true goal nat_induct_auto_tac

let () =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_le a 0n ==> (a = 0n))]
  in
  run_proof ~simp:true ~name:"le_Zero_eq" ~notrace:true goal nat_induct_auto_tac

let () =
  let goal = make_goal [%term forall (fun (a : nat) -> nat_le 0n a = true)] in

  run_proof ~simp:true ~name:"le_Zero_l" ~notrace:true goal nat_induct_auto_tac

let () =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_le (Suc a) (Suc b) = nat_le a b)]
  in

  run_proof ~simp:true ~name:"le_Suc_Suc" ~notrace:true goal nat_induct_auto_tac

let () =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_le (Suc a) Zero = false)]
  in
  run_proof ~simp:true ~name:"le_Zero_r" ~notrace:true goal nat_induct_auto_tac

(* ===== Group 2: Reflexivity and basic identity ===== *)

let () =
  let goal = make_goal [%term forall (fun (a : nat) -> nat_lt a a = false)] in
  run_proof ~simp:true ~name:"lt_irrefl" ~notrace:true goal nat_induct_auto_tac

let () =
  let goal = make_goal [%term forall (fun (a : nat) -> nat_le a a = true)] in
  run_proof ~simp:true ~name:"le_refl" ~notrace:true goal nat_induct_auto_tac

let () =
  let goal = make_goal [%term forall (fun (a : nat) -> sub a a = 0n)] in

  run_proof ~simp:true ~name:"sub_self" ~notrace:true goal nat_induct_auto_tac

let () =
  let goal = make_goal [%term forall (fun (a : nat) -> plus 0n a = a)] in
  run_proof ~simp:true ~name:"add_Zero_l" ~notrace:true goal nat_induct_auto_tac

let () =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> plus (Suc a) b = Suc (plus a b))]
  in
  run_proof ~simp:true ~name:"add_Suc_l" ~notrace:true goal nat_induct_auto_tac

(* ===== Group 3: Successor relationships ===== *)

let () =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_lt a (Suc a) = true)]
  in
  run_proof ~simp:true ~name:"lt_Suc_self" ~notrace:true goal
    nat_induct_auto_tac

let () =
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_le a (Suc a) = true)]
  in
  run_proof ~simp:true ~name:"le_Suc_self" ~notrace:true goal
    nat_induct_auto_tac

let () =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_lt a (Suc b) = nat_le a b)]
  in

  run_proof ~simp:true ~name:"lt_Suc_le" ~notrace:true goal
    (induct_tac
    >> with_no_automation_trace auto_dfs_tac
    >> intros_tac >> simp_tac
    >> with_arbitrary_term [%term (b : nat)] destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> elim_exists_asm_tac >> simp_tac)

let () =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_le a b = nat_lt a (Suc b))]
  in
  run_proof ~name:"le_lt_Suc" ~notrace:true goal nat_induct_auto_tac

(* (* ===== Group 4: Connection between lt and le ===== *) *)
let () =
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
    >> elim_exists_asm_tac >> simp_tac)

let () =
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
    (intros_tac >> simp_tac)

let () =
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
    >> elim_disj_asm_tac >> simp_tac >> elim_exists_asm_tac >> simp_tac)

let () =
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
    >> mp_asm_tac >> assumption_tac)

(* (* ===== Group 5: Transitivity ===== *) *)

let assumption_reasoning_tac =
  try_
    (with_no_automation_trace
       (with_best_first
          (pick_tac
             [
               simp_tac; simp_asm_tac; false_elim_tac; assumption_tac; truth_tac;
             ])))

let () =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_lt a b ==> (nat_lt b c ==> nat_lt a c))]
  in
  run_proof ~name:"lt_trans" ~notrace:true goal
    (with_arbitrary_term [%term (a : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (b : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (c : nat)] induct_tac
    >>> intros_tac
    >>> try_ assumption_reasoning_tac
    >>= [
          with_repeat
            (with_first (with_proven [ "lt_Suc_Suc" ] rewrite_asm_tac))
          >> spec_asm_tac [%term (n0' : nat)]
          >> spec_asm_tac [%term (n0'' : nat)]
          >> with_proven [ "lt_Suc_Suc" ] rewrite_tac
          >> with_repeat mp_asm_tac >> assumption_tac;
        ])

let () =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_le a b ==> (nat_le b c ==> nat_le a c))]
  in
  run_proof ~name:"le_trans" ~notrace:true goal
    (with_arbitrary_term [%term (a : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (b : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (c : nat)] induct_tac
    >>> intros_tac
    >>> try_ assumption_reasoning_tac
    >>= [
          with_repeat
            (with_first (with_proven [ "le_Suc_Suc" ] rewrite_asm_tac))
          >> spec_asm_tac [%term (n0' : nat)]
          >> spec_asm_tac [%term (n0'' : nat)]
          >> with_proven [ "le_Suc_Suc" ] rewrite_tac
          >> with_repeat mp_asm_tac >> assumption_tac;
        ])

let () =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_le a b ==> (nat_lt b c ==> nat_lt a c))]
  in
  run_proof ~name:"le_lt_trans" ~notrace:true goal
    (with_arbitrary_term [%term (a : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (b : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (c : nat)] induct_tac
    >>> intros_tac
    >>> try_ assumption_reasoning_tac
    >>= [
          with_repeat
            (with_first
               (with_proven [ "le_Suc_Suc"; "lt_Suc_Suc" ] rewrite_asm_tac))
          >> spec_asm_tac [%term (n0' : nat)]
          >> spec_asm_tac [%term (n0'' : nat)]
          >> with_proven [ "lt_Suc_Suc" ] rewrite_tac
          >> with_repeat mp_asm_tac >> assumption_tac;
        ])

let () =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_lt a b ==> (nat_le b c ==> nat_lt a c))]
  in
  run_proof ~name:"lt_le_trans" ~notrace:true goal
    (with_arbitrary_term [%term (a : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (b : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (c : nat)] induct_tac
    >>> intros_tac
    >>> try_ assumption_reasoning_tac
    >>= [
          with_proven [ "lt_Suc_Suc" ] rewrite_tac
          >> with_repeat
               (with_first
                  (with_proven [ "lt_Suc_Suc"; "le_Suc_Suc" ] rewrite_asm_tac))
          >> spec_asm_tac [%term (n0' : nat)]
          >> spec_asm_tac [%term (n0'' : nat)]
          >> with_repeat mp_asm_tac >> assumption_tac;
        ])

let () =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) ->
            nat_le a b ==> (nat_le b a ==> ((a : nat) = b)))]
  in
  run_proof ~name:"le_antisym" ~notrace:true goal
    (with_arbitrary_term [%term (a : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (b : nat)] induct_tac
    >>> intros_tac
    >>> try_ assumption_reasoning_tac
    >> with_proven [ "eq_cong" ] apply_thm_tac
    >> with_repeat (with_first (with_proven [ "le_Suc_Suc" ] rewrite_asm_tac))
    >> spec_asm_tac [%term (n0' : nat)]
    >> with_repeat mp_asm_tac >> assumption_tac)

(* (* ===== Group 6: Subtraction properties ===== *) *)

let () =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_le a b ==> nat_le a (Suc b))]
  in
  run_proof ~name:"le_weaken_Suc" ~notrace:true goal
    (with_arbitrary_term [%term (a : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (b : nat)] induct_tac
    >>> try_ intros_tac
    >>> try_ assumption_reasoning_tac
    >> with_proven [ "le_Suc_Suc" ] rewrite_tac
    >> spec_asm_tac [%term (n0' : nat)]
    >> with_repeat (with_first (with_proven [ "le_Suc_Suc" ] rewrite_asm_tac))
    >> with_first mp_asm_tac >> assume_tac)

let () =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_lt a b ==> nat_lt a (Suc b))]
  in
  run_proof ~name:"lt_weaken_Suc" ~notrace:true goal
    (with_arbitrary_term [%term (a : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (b : nat)] induct_tac
    >>> try_ intros_tac
    >>> try_ assumption_reasoning_tac
    >> with_proven [ "lt_Suc_Suc" ] rewrite_tac
    >> spec_asm_tac [%term (n0' : nat)]
    >> with_repeat (with_first (with_proven [ "lt_Suc_Suc" ] rewrite_asm_tac))
    >> with_first mp_asm_tac >> assume_tac)

let () =
  let goal =
    make_goal [%term forall (fun (a : nat) (b : nat) -> nat_le (sub a b) a)]
  in
  run_proof ~name:"sub_le" ~notrace:true goal
    (with_arbitrary_term [%term (a : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (b : nat)] induct_tac
    >>> try_ intros_tac
    >>> try_ assumption_reasoning_tac
    >> with_proven [ "sub_Suc_Suc" ] rewrite_tac
    >> spec_asm_tac [%term (n0' : nat)]
    >> with_proven [ "le_weaken_Suc" ] apply_thm_tac
    >> assumption_tac)

let () =
  let goal =
    make_goal
      [%term
        forall (fun (b : nat) (a : nat) ->
            nat_lt 0n b ==> (nat_le b a ==> nat_lt (sub a b) a))]
  in
  run_proof ~name:"sub_lt" ~notrace:true goal
    (with_arbitrary_term [%term (b : nat)] induct_tac
    >>> intros_tac >> assumption_reasoning_tac
    >> with_arbitrary_term [%term (a : nat)] destruct_tac
    >> elim_disj_asm_tac >> simp_asm_tac >> simp_tac
    >> with_first assumption_tac >> elim_exists_asm_tac
    >> with_first (with_assumptions rewrite_tac)
    >> with_first (with_assumptions rewrite_tac)
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_proven [ "sub_Suc_Suc" ] rewrite_tac
    >> with_first (with_proven [ "le_Suc_Suc" ] rewrite_asm_tac)
    >> with_arbitrary_term [%term (n0 : nat)] destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> elim_exists_asm_tac
    >> with_proven [ "lt_weaken_Suc" ] apply_thm_tac
    >> spec_asm_tac [%term (a0 : nat)]
    >> simp_asm_tac >> simp_tac >> with_repeat mp_asm_tac >> assumption_tac)

let () =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) ->
            nat_le b a ==> (plus (sub a b) b = a))]
  in
  run_proof ~name:"sub_add_cancel" ~notrace:true goal
    (with_arbitrary_term [%term (a : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (b : nat)] induct_tac
    >>> try_ intros_tac
    >>> try_ assumption_reasoning_tac
    >>= [
          simp_tac
          >> with_proven [ "eq_cong" ] apply_thm_tac
          >> with_proven [ "plus_x_Zero" ] rewrite_tac
          >> refl_tac;
          simp_asm_tac >> simp_tac
          >> with_proven [ "plus_Suc" ] rewrite_tac
          >> with_proven [ "eq_cong" ] apply_thm_tac
          >> spec_asm_tac [%term (n0' : nat)]
          >> mp_asm_tac >> assumption_tac;
        ])

(* (* ===== Group 8: Ordering and addition ===== *) *)

let () =
  let goal =
    make_goal [%term forall (fun (a : nat) (b : nat) -> nat_le a (plus a b))]
  in
  run_proof ~name:"le_add_r" ~notrace:true goal nat_induct_auto_tac

(* (* ===== Group 9: Totality ===== *) *)

let () =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_lt a b || nat_le b a)]
  in
  run_proof ~name:"lt_total" ~notrace:true goal
    (with_arbitrary_term [%term (a : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (b : nat)] induct_tac
    >>> try_ intros_tac
    >>= [
          right_tac >> simp_tac;
          left_tac >> simp_tac;
          right_tac >> simp_tac;
          spec_asm_tac [%term (n0' : nat)]
          >> elim_disj_asm_tac >> left_tac
          >> with_proven [ "lt_Suc_Suc" ] rewrite_tac
          >> assumption_tac >> right_tac
          >> with_proven [ "le_Suc_Suc" ] rewrite_tac
          >> assumption_tac;
        ])

let () =
  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_le a b || nat_le b a)]
  in
  run_proof ~name:"le_total" ~notrace:true goal
    (with_arbitrary_term [%term (a : nat)] induct_tac
    >>> intros_tac
    >>> with_arbitrary_term [%term (b : nat)] induct_tac
    >>> try_ intros_tac
    >>= [
          right_tac >> simp_tac;
          left_tac >> simp_tac;
          right_tac >> simp_tac;
          spec_asm_tac [%term (n0' : nat)]
          >> elim_disj_asm_tac >> left_tac
          >> with_proven [ "le_Suc_Suc" ] rewrite_tac
          >> assumption_tac >> right_tac
          >> with_proven [ "le_Suc_Suc" ] rewrite_tac
          >> assumption_tac;
        ])

let () =
  let goal =
    make_goal
      [%term
        forall (fun (n : nat) (a : nat) (b : nat) ->
            nat_lt 0n b
            ==> (nat_lt a n ==> exists (fun (x : nat) -> div_aux n a b = Some x)))]
  in
  run_proof ~name:"div_fuel_sufficient" ~notrace:true goal
    (induct_tac >> intros_tac >> simp_asm_tac >> false_elim_tac >> intros_tac
   >> simp_tac >> cond_tac >> simp_tac
    >> with_arbitrary_term NatTheory.n0 exists_tac
    >> refl_tac >> simp_tac
    >> with_first (with_proven [ "lt_Suc_le" ] rewrite_asm_tac)
    >> with_first (with_proven [ "not_lt_is_le" ] rewrite_asm_tac)
    >> (with_arbitrary_term
          [%term nat_lt (sub (a : nat) (b : nat)) (a : nat)]
          assert_tac
       >> with_proven [ "sub_lt" ] apply_thm_tac
       >> with_first assumption_tac >> with_first assumption_tac)
    >> (with_arbitrary_term
          [%term nat_lt (sub (a : nat) (b : nat)) (n0 : nat)]
          assert_tac
       >> with_proven [ "lt_le_trans" ] apply_thm_tac
       >> with_first assumption_tac >> with_first assumption_tac)
    >> spec_asm_tac [%term sub (a : nat) (b : nat)]
    >> spec_asm_tac [%term (b : nat)]
    >> with_repeat mp_asm_tac >> elim_exists_asm_tac >> simp_tac
    >> with_arbitrary_term [%term Suc (x' : nat)] exists_tac
    >> simp_tac)

let () =
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) ->
            nat_lt 0n b
            ==> (div a b = if nat_lt a b then 0n else Suc (div (sub a b) b)))]
  in
  run_proof ~name:"div_unfold" ~notrace:true goal
    (intros_tac
    >> with_definition [ "div" ] rewrite_tac
    >> beta_tac
    >> with_first (with_definition [ "div_aux" ] rewrite_tac)
    >> beta_tac >> with_nth_choice 1 cond_tac >> simp_tac
    >> with_repeat @@ with_assumptions rewrite_tac
    >> with_repeat @@ with_proven [ "cond_false" ] rewrite_tac
    >> with_first (with_proven [ "not_lt_is_le" ] rewrite_asm_tac)
    >> with_arbitrary_term
         [%term nat_lt (sub (a : nat) (b : nat)) (a : nat)]
         assert_tac
    >> with_proven [ "sub_lt" ] apply_thm_tac
    >> with_first assumption_tac >> with_first assumption_tac
    >> with_arbitrary_term
         [%term
           exists (fun (x' : nat) ->
               div_aux (a : nat) (sub (a : nat) (b : nat)) (b : nat) = Some x')]
         assert_tac
    >> with_proven [ "div_fuel_sufficient" ] apply_thm_tac
    >> with_first assumption_tac >> with_first assumption_tac
    >> elim_exists_asm_tac
    >> with_first (with_assumptions rewrite_tac)
    >> with_first (with_definition [ "match_option" ] rewrite_tac)
    >> beta_tac
    >> with_first (with_definition [ "match_option" ] rewrite_tac)
    >> beta_tac
    >> with_arbitrary_term
         [%term
           exists (fun (x : nat) ->
               div_aux
                 (Suc (sub (a : nat) (b : nat)))
                 (sub (a : nat) (b : nat))
                 (b : nat)
               = Some x)]
         assert_tac
    >> with_proven [ "div_fuel_sufficient" ] apply_thm_tac
    >> with_first assumption_tac
    >> with_proven [ "lt_Suc_self" ] rewrite_tac
    >> truth_tac >> elim_exists_asm_tac
    >> with_arbitrary_term
         [%term
           div_aux
             (plus
                (Suc (sub (a : nat) (b : nat)))
                (sub (a : nat) (Suc (sub (a : nat) (b : nat)))))
             (sub (a : nat) (b : nat))
             (b : nat)
           = Some (x : nat)]
         assert_tac
    >> with_proven [ "div_fuel_irrel" ] apply_thm_tac
    >> with_first assumption_tac
    >> with_arbitrary_term
         [%term
           plus
             (sub (a : nat) (Suc (sub (a : nat) (b : nat))))
             (Suc (sub (a : nat) (b : nat)))
           = (a : nat)]
         assert_tac
    >> with_proven [ "sub_add_cancel" ] apply_thm_tac
    >> with_proven [ "le_lt_Suc" ] rewrite_tac
    >> with_proven [ "lt_Suc_Suc" ] rewrite_tac
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
    >> simp_tac)

let () =
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
  run_proof ~pretty:true ~notrace:true goal proof

let () =
  let goal =
    make_goal
      [%term
        forall
          (fun
            (fuel : nat)
            (additional : nat)
            (xs : nat list)
            (ys : nat list)
            (x : nat list)
          ->
            merge_aux fuel xs ys = Some x
            ==> (merge_aux (plus fuel additional) xs ys = Some x))]
  in
  let rw_asm =
    with_first (with_assumptions rewrite_tac)
    >> with_first (with_assumptions rewrite_asm_tac)
  in
  run_proof ~name:"merge_fuel_irrel" ~notrace:true goal
    (with_arbitrary_term [%term (fuel : nat)] induct_tac
    >> intros_tac >> simp_asm_tac
    >> with_rules OptionTheory.option_def.distinct rewrite_asm_tac
    >> false_elim_tac >> intros_tac
    >> with_arbitrary_term [%term (xs : nat list)] destruct_tac
    >> elim_disj_asm_tac >> simp_tac >> simp_asm_tac >> elim_exists_asm_tac
    >> elim_exists_asm_tac
    >> with_proven [ "add_Suc_l" ] rewrite_tac
    >> rw_asm
    >> with_arbitrary_term [%term (ys : nat list)] destruct_tac
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
    >> with_arbitrary_term
         [%term
           merge_aux
             (n0 : nat)
             (a1 : nat list)
             (Cons ((a0' : nat), (a1' : nat list)))]
         destruct_tac
    >> elim_disj_asm_tac >> simp_asm_tac
    >> with_first (with_rules OptionTheory.option_def.distinct rewrite_asm_tac)
    >> false_elim_tac >> elim_exists_asm_tac >> simp_asm_tac
    >> spec_asm_tac [%term (additional : nat)]
    >> spec_asm_tac [%term (a1 : nat list)]
    >> spec_asm_tac [%term Cons ((a0' : nat), (a1' : nat list))]
    >> spec_asm_tac [%term (a0'' : nat list)]
    >> with_repeat mp_asm_tac >> simp_tac >> simp_tac
    >> with_first (with_assumptions rewrite_asm_tac)
    >> simp_asm_tac
    >> with_arbitrary_term
         [%term
           merge_aux
             (n0 : nat)
             (Cons ((a0 : nat), (a1 : nat list)))
             (a1' : nat list)]
         destruct_tac
    >> elim_disj_asm_tac >> simp_asm_tac
    >> with_first (with_rules OptionTheory.option_def.distinct rewrite_asm_tac)
    >> false_elim_tac >> elim_exists_asm_tac >> simp_asm_tac
    >> spec_asm_tac [%term (additional : nat)]
    >> spec_asm_tac [%term Cons ((a0 : nat), (a1 : nat list))]
    >> spec_asm_tac [%term (a1' : nat list)]
    >> spec_asm_tac [%term (a0'' : nat list)]
    >> with_repeat mp_asm_tac >> simp_tac)

let () =
  let goal =
    make_goal
      [%term
        forall (fun (fuel : nat) (xs : nat list) (ys : nat list) ->
            nat_lt (plus (length xs) (length ys)) fuel
            ==> exists (fun (x : nat list) -> merge_aux fuel xs ys = Some x))]
  in
  run_proof ~name:"merge_fuel_sufficient" ~notrace:true goal
    (induct_tac >> intros_tac >> simp_asm_tac >> false_elim_tac >> intros_tac
   >> simp_tac
    >> with_arbitrary_term [%term (xs : nat list)] destruct_tac
    >> elim_disj_asm_tac >> simp_tac
    >> with_arbitrary_term [%term (ys : nat list)] exists_tac
    >> refl_tac
    >> with_repeat elim_exists_asm_tac
    >> simp_tac
    >> with_arbitrary_term [%term (ys : nat list)] destruct_tac
    >> elim_disj_asm_tac >> simp_tac
    >> with_arbitrary_term [%term Cons ((a0 : nat), (a1 : nat list))] exists_tac
    >> refl_tac
    >> with_repeat elim_exists_asm_tac
    >> simp_tac >> cond_tac >> simp_tac
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_first (with_definition [ "length" ] rewrite_asm_tac)
    >> with_proven [ "add_Suc_l" ] rewrite_asm_tac
    >> with_proven [ "lt_Suc_Suc" ] rewrite_asm_tac
    >> spec_asm_tac [%term (a1 : nat list)]
    >> spec_asm_tac [%term Cons ((a0' : nat), (a1' : nat list))]
    >> mp_asm_tac >> elim_exists_asm_tac >> simp_tac
    >> with_arbitrary_term [%term Cons ((a0 : nat), (x' : nat list))] exists_tac
    >> refl_tac >> simp_tac
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_proven [ "plus_comm" ] rewrite_asm_tac
    >> with_first (with_definition [ "length" ] rewrite_asm_tac)
    >> with_proven [ "add_Suc_l" ] rewrite_asm_tac
    >> with_proven [ "plus_comm" ] rewrite_asm_tac
    >> with_proven [ "lt_Suc_Suc" ] rewrite_asm_tac
    >> spec_asm_tac [%term Cons ((a0 : nat), (a1 : nat list))]
    >> spec_asm_tac [%term (a1' : nat list)]
    >> mp_asm_tac >> elim_exists_asm_tac >> simp_tac
    >> with_arbitrary_term
         [%term Cons ((a0' : nat), (x' : nat list))]
         exists_tac
    >> refl_tac)

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
let () =
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
    (intros_tac
    >> with_arbitrary_term [%term (xs : nat list)] destruct_tac
    >> with_arbitrary_term [%term (ys : nat list)] destruct_tac
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
    >> with_arbitrary_term
         [%term
           exists (fun (x : nat list) ->
               merge_aux
                 (Suc
                    (plus
                       (length (a1' : nat list))
                       (Suc (length (a1 : nat list)))))
                 (a1' : nat list)
                 (Cons ((a0 : nat), (a1 : nat list)))
               = Some x)]
         assert_tac
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
    >> with_arbitrary_term
         [%term
           exists (fun (x : nat list) ->
               merge_aux
                 (Suc
                    (plus
                       (length (a1' : nat list))
                       (Suc (length (a1 : nat list)))))
                 (Cons ((a0' : nat), (a1' : nat list)))
                 (a1 : nat list)
               = Some x)]
         assert_tac
    >> with_proven [ "merge_fuel_sufficient" ] apply_thm_tac
    >> simp_tac
    >> with_proven [ "plus_Suc" ] rewrite_tac
    >> simp_tac >> elim_exists_asm_tac
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac ~exclude:[ "merge"; "merge_aux" ]
    >> with_definition [ "merge" ] rewrite_tac
    >> beta_tac
    >> with_first (with_definition [ "length" ] rewrite_tac)
    >> with_first (with_proven [ "plus_Suc" ] rewrite_asm_tac)
    >> with_first (with_proven [ "plus_comm" ] rewrite_tac)
    >> with_first (with_proven [ "plus_Suc" ] rewrite_tac)
    >> with_first (with_proven [ "plus_comm" ] rewrite_tac)
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac)

(* sort [3,1,2] = [1,2,3] *)
let () =
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

  let goal =
    make_goal
      [%term
        merge_sort_aux 8n (Cons (3n, Cons (1n, Cons (2n, Nil))))
        = Some (Cons (1n, Cons (2n, Cons (3n, Nil))))]
  in
  run_proof ~pretty:true ~notrace:true goal
    (rw_def "merge_sort_aux" >> simp_tac ~exclude
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
    >> rw_thm "merge_unfold" >> simp_tac ~exclude)

let () =
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
    (with_arbitrary_term n induct_tac
    >>> try_ intros_tac
    >>> with_arbitrary_term xs induct_tac
    >>> try_ intros_tac
    >>> try_ assumption_reasoning_tac
    >> with_repeat
         (with_first (with_definition [ "take"; "length" ] rewrite_tac))
    >> beta_tac
    >> with_repeat (with_first (with_definition [ "match_list" ] rewrite_tac))
    >> beta_tac
    >> with_first (with_definition [ "length" ] rewrite_tac)
    >> spec_asm_tac n1
    >> with_assumptions rewrite_tac
    >> with_first (with_proven [ "lt_Suc_Suc" ] rewrite_tac)
    >> cond_tac >> simp_tac >> simp_tac);
  run_proof ~name:"length_drop" ~notrace:true gdrop
    (with_arbitrary_term n induct_tac
    >>> try_ intros_tac
    >>> with_arbitrary_term xs induct_tac
    >>> try_ intros_tac
    >>> try_ assumption_reasoning_tac
    >> with_repeat
         (with_first (with_definition [ "take"; "length" ] rewrite_tac))
    >> beta_tac
    >> with_repeat (with_first (with_definition [ "match_list" ] rewrite_tac))
    >> beta_tac
    >> with_first (with_definition [ "length" ] rewrite_tac)
    >> spec_asm_tac n1
    >> with_assumptions rewrite_tac
    >> with_first (with_proven [ "lt_Suc_Suc" ] rewrite_tac)
    >> cond_tac >> simp_tac >> simp_tac)

let () =
  let n = [%term (n : nat)] in
  let m = [%term (m : nat)] in
  let ltkm = [%term nat_lt (k : nat) (m : nat)] in
  let subkm = [%term sub (k : nat) (m : nat)] in
  let subkmlen0 = [%term nat_le (sub (k : nat) (m : nat)) (n0 : nat)] in
  let subltkmk = [%term nat_lt (sub (k : nat) (m : nat)) (k : nat)] in
  let subltkm_Sucn0 =
    [%term nat_lt (sub (k : nat) (m : nat)) (Suc (n0 : nat))]
  in

  let n0 = [%term (n0 : nat)] in
  let a0 = [%term (a0 : nat)] in
  let div_unfld =
    [%term
      div (Suc (n0 : nat)) 2n
      =
      if nat_lt (Suc (n0 : nat)) 2n then 0n
      else Suc (div (sub (Suc (n0 : nat)) 2n) 2n)]
  in
  let div_unfld2 =
    [%term
      div (Suc (Suc (a0 : nat))) 2n
      =
      if nat_lt (Suc (Suc (a0 : nat))) 2n then 0n
      else Suc (div (sub (Suc (Suc (a0 : nat))) 2n) 2n)]
  in
  let div_unfld3 =
    [%term
      div (k : nat) (m : nat)
      =
      if nat_lt (k : nat) (m : nat) then 0n
      else Suc (div (sub (k : nat) (m : nat)) (m : nat))]
  in
  let gpos =
    make_goal
      [%term forall (fun (n : nat) -> nat_lt 1n n ==> nat_lt 0n (div n 2n))]
  in
  let gle =
    make_goal
      [%term
        forall (fun (n : nat) (k : nat) (m : nat) ->
            nat_lt 0n m ==> (nat_le k n ==> nat_le (div k m) n))]
  in
  let glt =
    make_goal
      [%term forall (fun (n : nat) -> nat_lt 1n n ==> nat_lt (div n 2n) n)]
  in

  run_proof ~name:"div_pos" ~notrace:true gpos
    (with_arbitrary_term n induct_tac
    >>> intros_tac
    >>> try_ assumption_reasoning_tac
    >> with_arbitrary_term div_unfld assert_tac
    >> with_first (with_proven [ "div_unfold" ] apply_thm_tac)
    >> simp_tac
    >> with_assumptions rewrite_tac
    >> cond_tac >> simp_asm_tac
    >> with_first eq_true_elim_asm_tac
    >> with_first (with_proven [ "le_Zero_eq" ] apply_thm_asm_tac)
    >> simp_asm_tac >> false_elim_tac
    >> with_assumptions rewrite_tac
    >> with_proven [ "cond_false" ] rewrite_tac
    >> simp_tac ~exclude:[ "div" ]);
  run_proof ~name:"div_le" ~notrace:true gle
    (with_arbitrary_term n induct_tac
    >> intros_tac
    >> with_first (with_proven [ "le_Zero_eq" ] apply_thm_asm_tac)
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
    >> with_arbitrary_term subltkm_Sucn0 assert_tac
    >> with_proven [ "lt_le_trans" ] apply_thm_tac
    >> with_first assumption_tac >> with_first assumption_tac
    >> with_first
         (with_proven [ "lt_Suc_le" ]
            (with_info_trace (with_flip_rules rewrite_tac)))
    >> with_first assumption_tac >> spec_asm_tac subkm >> spec_asm_tac m
    >> with_repeat mp_asm_tac >> with_first assumption_tac);
  run_proof ~pretty:true ~name:"div_lt" ~notrace:true glt
    (with_arbitrary_term n induct_tac
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
    >> with_repeat (with_first (with_proven [ "lt_Suc_Suc" ] rewrite_asm_tac))
    >> with_first
         (with_nth_term 0 (with_definition [ "nat_lt" ] rewrite_asm_tac))
    >> beta_asm_tac
    >> with_first
         (with_nth_term 0 (with_definition [ "match_nat" ] rewrite_asm_tac))
    >> try_ beta_asm_tac
    >> with_first
         (with_nth_term 0 (with_proven [ "cond_false" ] rewrite_asm_tac))
    >> try_ beta_asm_tac
    >> with_first (with_assumptions rewrite_tac)
    >> with_first (with_assumptions rewrite_tac)
    >> with_proven [ "lt_Suc_Suc" ] rewrite_tac
    >> simp_tac ~exclude:[ "nat_lt"; "div" ]
    >> with_repeat (with_assumptions (with_flip_rules (with_first rewrite_tac)))
    >> with_proven [ "div_le" ] apply_thm_tac
    >> simp_tac >> simp_tac)

let () =
  let goal =
    make_goal
      [%term
        forall (fun (fuel : nat) (xs : nat list) ->
            nat_lt (length xs) fuel
            ==> exists (fun (x : nat list) -> merge_sort_aux fuel xs = Some x))]
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
       >> with_first (with_proven [ "lt_Suc_le" ] rewrite_asm_tac)
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
    >> with_first (with_proven [ "lt_Suc_le" ] rewrite_asm_tac)
    >> with_first (with_proven [ "lt_le_trans" ] apply_thm_tac)
    >> with_first assumption_tac >> with_first assumption_tac
    >> with_repeat (with_first mp_asm_tac)
    >> with_repeat elim_exists_asm_tac
    >> simp_tac ~exclude:[ "div"; "merge" ]
    >> with_arbitrary_term
         [%term merge (x' : nat list) (x'' : nat list)]
         exists_tac
    >> refl_tac)

let () =
  let goal =
    make_goal
      [%term
        forall
          (fun (fuel : nat) (additional : nat) (xs : nat list) (x : nat list) ->
            merge_sort_aux fuel xs = Some x
            ==> (merge_sort_aux (plus fuel additional) xs = Some x))]
  in
  let proof = sorry_tac in
  (*TODO: finish this one*)
  run_proof ~notrace:true goal proof

let () =
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
           = Some
               (merge_sort
                  (take (div (length (xs : nat list)) 2n) (xs : nat list)))]
         assert_tac
    >> with_definition [ "merge_sort" ] rewrite_tac
    >> beta_tac
    >> with_arbitrary_term
         [%term
           exists (fun (z : nat list) ->
               merge_sort_aux
                 (Suc
                    (length
                       (take (div (length (xs : nat list)) 2n) (xs : nat list))))
                 (take (div (length (xs : nat list)) 2n) (xs : nat list))
               = Some z)]
         assert_tac
    >> with_proven [ "merge_sort_fuel_sufficient" ] apply_thm_tac
    >> simp_tac >> elim_exists_asm_tac
    >> with_assumptions rewrite_tac
    >> simp_tac ~exclude:[ "merge_sort"; "merge"; "merge_sort_aux"; "div" ]
    >> with_arbitrary_term
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
         assert_tac
    >> with_proven [ "plus_comm" ] rewrite_tac
    >> with_proven [ "sub_add_cancel" ] apply_thm_tac
    >> with_proven [ "length_take" ] rewrite_tac
    >> sorry_tac >> sorry_tac >> sorry_tac)
