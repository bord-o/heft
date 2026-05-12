open Heft
open Kernel
open Derived
open Tactic
open Auto

let run_proof = run_proof ~quiet:true

let () =
  let goal = make_goal [%term forall (fun (a : nat) -> true)] in
  run_proof ~notrace:true goal (intros >> truth);

  let goal = make_goal [%term plus 2n 3n = 5n] in
  run_proof ~pretty:true goal simp;

  let goal =
    make_goal
      [%term forall (fun (x : nat) (y : nat) -> Suc x = Suc y ==> (x = y))]
  in
  run_proof ~name:"Suc_inj" goal
    (intros >> (apply |> with_rules Nats.nat_def.injective) >> assumption);

  (* Lemma needed for commutativity: plus x (Suc y) = Suc (plus x y) *)
  let goal =
    make_goal
      [%term
        forall (fun (x : nat) (y : nat) -> plus x (Suc y) = Suc (plus x y))]
  in
  run_proof ~simp:true ~name:"plus_Suc" goal
    (induct >> gen >> simp >> intros >> simp);

  let goal =
    make_goal
      [%term forall (fun (x : nat) (y : nat) -> x = y ==> (Suc x = Suc y))]
  in
  run_proof ~name:"Suc_inj_rev" goal
    (intros >> (rewrite |> with_assumptions) >> refl);

  (* Commutativity: plus x y = plus y x *)
  let%thm plus_comm (x : nat) (y : nat) = plus x y = plus y x
  and proof =
    begin
      induct >> (gen >> simp) >> (intros >> simp)
    end
    [@quiet]
  in
  ignore plus_comm;

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

  (* xs = Nil ==> length xs = Zero *)
  let goal =
    make_goal
      [%term forall (fun (xs : 'a list) -> xs = Nil ==> (length xs = Zero))]
  in
  run_proof goal (intros >> simp ~with_asms:true);

  (* length xs = Zero ==> xs = Nil *)
  let%thm _length_zero_nil (xs : 'a list) = length xs = Zero ==> (xs = Nil)
  and proof =
    begin
      induct >> intros >> refl >> intros >> simp_asm >> discriminate
    end
    [@quiet]
  in
  ();

  let goal =
    make_goal [%term forall (fun (xs : 'a list) -> append Nil xs = xs)]
  in
  run_proof goal (intros >> simp);

  let goal =
    make_goal
      [%term
        forall (fun (x : 'a) (xs : 'a list) (ys : 'a list) ->
            append (Cons (x, xs)) ys = Cons (x, append xs ys))]
  in
  run_proof ~name:"append_cons" goal (intros >> simp);

  let goal =
    make_goal [%term forall (fun (xs : 'a list) -> append xs Nil = xs)]
  in
  run_proof ~name:"append_xs_Nil" goal
    (induct >> simp >> intros
    >> with_proven [ "append_cons" ] rewrite
    >> with_proven [ "append_cons" ] simp);

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

  let goal =
    make_goal
      [%term forall (fun (x : 'a list) -> length (reverse x) = length x)]
  in
  run_proof goal
    (induct >> simp >> intros
    >> with_proven [ "append_length" ] simp
    >> with_first (with_proven [ "plus_comm" ] rewrite)
    >> simp);

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

  let goal =
    make_goal [%term forall (fun (xs : 'a list) -> reverse (reverse xs) = xs)]
  in
  run_proof goal
    (induct >> simp >> intros >> with_proven [ "append_reverse" ] simp);

  let goal =
    make_goal
      [%term
        forall (fun (x : 'a) (y : 'a) ->
            x = y ==> (fst (Pair (x, y)) = snd (Pair (x, y))))]
  in
  run_proof goal (intros >> simp);

  let goal = make_goal [%term pred 3n = 2n] in
  run_proof ~pretty:true goal simp;

  let goal = make_goal [%term minus 4n 3n = 1n] in
  run_proof ~pretty:true goal simp;

  let goal = make_goal [%term forall (fun (n : nat) -> minus n Zero = n)] in
  run_proof ~name:"minus_Zero" goal
    (induct
    >> with_no_automation_trace auto_dfs
    >> with_no_automation_trace auto_dfs);

  (* n - (Suc m) = (n - m) - 1 *)
  let goal =
    make_goal
      [%term
        forall (fun (n : nat) (m : nat) -> minus n (Suc m) = pred (minus n m))]
  in
  run_proof ~name:"minus_Suc_right" goal
    (induct
    >> with_proven [ "minus_Zero" ] (with_no_automation_trace auto_dfs)
    >> with_no_automation_trace auto_dfs);

  (* (Suc n) - (Suc m) = n - m *)
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

  let goal = make_goal [%term forall (fun (n : nat) -> minus n n = Zero)] in
  run_proof ~name:"minus_self" goal
    (induct >> simp >> intros
    >> with_proven [ "minus_Suc_Suc" ] simp
    >> simp_asm ~with_asms:false);

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

  let goal = make_goal [%term twice pred 2n = 0n] in
  run_proof goal simp;

  let goal =
    make_goal
      [%term
        forall (fun (f : 'a -> 'b -> 'c) (x : 'a) (y : 'b) ->
            flip f y x = f x y)]
  in
  run_proof ~name:"flip_f" goal (intros >> simp);

  let goal = make_goal [%term not (true = false)] in
  let t = true_def |> Result.get_ok in
  run_proof goal
    (neg_intro
    >> with_assumptions (with_flip_rules rewrite)
    >> with_rule t rewrite >> refl);

  let goal = make_goal [%term nat_le 0n 1n] in
  run_proof ~notrace:true goal simp;

  let goal = make_goal [%term not (nat_le 3n 1n)] in
  run_proof ~pretty:true ~notrace:true goal (simp >> neg_intro >> assumption);

  (* insert 3 into [] = [3] *)
  let goal = make_goal [%term insert Nil 3n = Cons (3n, Nil)] in
  run_proof ~pretty:true ~notrace:true goal simp;

  (* insert 2 into [1] = [1, 2] *)
  let goal =
    make_goal [%term insert (Cons (1n, Nil)) 2n = Cons (1n, Cons (2n, Nil))]
  in
  run_proof ~pretty:true ~notrace:true goal simp;

  let goal = make_goal [%term sub 4n 3n = 1n] in
  run_proof ~pretty:true goal simp;

  let goal = make_goal [%term forall (fun (x : nat) -> minus 0n x = 0n)] in
  run_proof ~name:"minus_Zero_left" goal
    (induct >> simp >> intros >> simp_asm ~with_asms:false
   >> simp ~with_asms:false >> with_assumptions rewrite >> simp);

  let goal =
    make_goal [%term forall (fun (x : nat) (n : nat) -> sub x n = minus x n)]
  in
  run_proof goal
    (induct
    >>= [
          with_proven [ "minus_Zero_left" ] simp @>> gen @>> refl;
          gen >> intro >> induct
          >>= [
                with_proven [ "minus_Zero" ] simp;
                intros >> with_proven [ "minus_Suc_Suc" ] rewrite >> simp;
              ];
        ]);

  (* isort [] = [] *)
  let goal = make_goal [%term isort Nil = Nil] in
  run_proof goal simp;

  (* isort [3,1,2] = [1,2,3] *)
  let goal =
    make_goal
      [%term
        isort (Cons (3n, Cons (1n, Cons (2n, Nil))))
        = Cons (1n, Cons (2n, Cons (3n, Nil)))]
  in
  run_proof ~pretty:true goal simp;

  let goal = make_goal [%term eqb true false = false] in
  run_proof goal simp;

  let goal =
    make_goal [%term forall (fun (b : bool) -> b = true || b = false)]
  in

  run_proof ~name:"bool_cases_test" goal
    (gen >> with_term [%term (b : bool)] destruct >> assumption);

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

  let goal =
    make_goal
      [%term
        forall (fun (l : nat list) (n : nat) ->
            sorted l ==> sorted (insert l n))]
  in
  run_proof ~name:"sort_correct_lemma" goal
    (induct @>> (intros >> simp)
    >>= [
          conj @>> truth;
          cond @>> (simp >> conj)
          >>= [
                with_term [%term (n1 : nat list)] induct @>> (intros >> simp)
                >>= [
                      with_term
                        [%term nat_le (n0' : nat) (n : nat)]
                        destruct_elim
                      @>> simp
                      >>= [ simp_asm >> elim_conj_asm >> assumption; truth ];
                    ];
                spec_asm [%term (n : nat)]
                >> with_assumptions apply >> simp_asm >> elim_conj_asm
                >> assumption;
                with_proven [ "nat_le_flip" ] apply_asm >> simp;
                conj
                >>= [
                      with_term [%term (n1 : nat list)] induct
                      @>> (intros >> simp)
                      >>= [ simp_asm >> elim_conj_asm >> assumption ];
                      spec_asm [%term (n1 : nat)]
                      >> simp_asm >> elim_conj_asm >> assumption;
                    ];
              ];
        ]);

  let goal =
    make_goal [%term forall (fun (l : nat list) -> sorted (isort l))]
  in
  run_proof goal
    (induct >> simp >> intros >> simp
    >> with_proven [ "sort_correct_lemma" ] apply
    >> assumption);

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

  let apply_asm_to_asm ~asm_thm ~asm_to =
    with_nth_choice asm_thm (with_nth_term asm_to (with_assumptions apply_asm))
  in

  let%thm div_fuel_irrel (n : nat) (m : nat) (a : nat) (b : nat) (x : nat) =
    div_aux n a b = Some x ==> (div_aux (plus n m) a b = Some x)
  and proof =
    begin
      induct >> intros >> simp_asm >> discriminate >> intros
      >> with_first (with_definition [ "plus" ] rewrite)
      >> beta >> simp >> simp_asm
      >> with_term [%term nat_lt (a : nat) (b : nat)] destruct_elim
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
    [@quiet]
  in
  ignore div_fuel_irrel;

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

  let nat_induct_auto =
    induct
    >> with_no_automation_trace auto_dfs
    >> with_no_automation_trace auto_dfs
  in

  let goal =
    make_goal
      [%term forall (fun (x : nat) (b : nat) -> b = Suc x ==> nat_lt 0n b)]
  in
  run_proof ~simp:true ~name:"Suc_lt_Zero" ~notrace:true goal nat_induct_auto;

  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_lt a Zero = false)]
  in
  run_proof ~simp:true ~name:"lt_Zero_false" ~notrace:true goal nat_induct_auto;

  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_lt a (plus a (Suc b)))]
  in
  run_proof ~name:"lt_add_Suc_r" ~notrace:true goal nat_induct_auto;

  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_lt (plus a b) (plus a c) = nat_lt b c)]
  in
  run_proof ~name:"add_lt_cancel_l" ~notrace:true goal nat_induct_auto;

  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_le (plus a b) (plus a c) = nat_le b c)]
  in
  run_proof ~name:"add_le_cancel_l" ~notrace:true goal nat_induct_auto;

  (* ===== Group 1: Basic computation rules ===== *)
  let goal = make_goal [%term forall (fun (a : nat) -> sub a 0n = a)] in
  run_proof ~simp:true ~name:"sub_Zero_r" ~notrace:true goal nat_induct_auto;

  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> sub (Suc a) (Suc b) = sub a b)]
  in
  run_proof ~simp:true ~name:"sub_Suc_Suc" ~notrace:true goal nat_induct_auto;

  let goal = make_goal [%term forall (fun (a : nat) -> sub Zero a = 0n)] in
  run_proof ~simp:true ~name:"sub_Zero_l" ~notrace:true goal nat_induct_auto;

  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_lt 0n (Suc a) = true)]
  in
  run_proof ~simp:true ~name:"lt_Zero_Suc" ~notrace:true goal nat_induct_auto;

  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_lt (Suc a) (Suc b) = nat_lt a b)]
  in
  run_proof ~simp:true ~name:"lt_Suc_Suc" ~notrace:true goal nat_induct_auto;

  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_le a 0n ==> (a = 0n))]
  in
  run_proof ~simp:true ~name:"le_Zero_eq" ~notrace:true goal nat_induct_auto;

  let goal = make_goal [%term forall (fun (a : nat) -> nat_le 0n a = true)] in

  run_proof ~simp:true ~name:"le_Zero_l" ~notrace:true goal nat_induct_auto;

  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_le (Suc a) (Suc b) = nat_le a b)]
  in

  run_proof ~simp:true ~name:"le_Suc_Suc" ~notrace:true goal nat_induct_auto;

  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_le (Suc a) Zero = false)]
  in
  run_proof ~simp:true ~name:"le_Zero_r" ~notrace:true goal nat_induct_auto;

  (* ===== Group 2: Reflexivity and basic identity ===== *)
  let goal = make_goal [%term forall (fun (a : nat) -> nat_lt a a = false)] in
  run_proof ~simp:true ~name:"lt_irrefl" ~notrace:true goal nat_induct_auto;

  let goal = make_goal [%term forall (fun (a : nat) -> nat_le a a = true)] in
  run_proof ~simp:true ~name:"le_refl" ~notrace:true goal nat_induct_auto;

  let goal = make_goal [%term forall (fun (a : nat) -> sub a a = 0n)] in

  run_proof ~simp:true ~name:"sub_self" ~notrace:true goal nat_induct_auto;

  let goal = make_goal [%term forall (fun (a : nat) -> plus 0n a = a)] in
  run_proof ~simp:true ~name:"add_Zero_l" ~notrace:true goal nat_induct_auto;

  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> plus (Suc a) b = Suc (plus a b))]
  in
  run_proof ~simp:true ~name:"add_Suc_l" ~notrace:true goal nat_induct_auto;

  (* ===== Group 3: Successor relationships ===== *)
  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_lt a (Suc a) = true)]
  in
  run_proof ~simp:true ~name:"lt_Suc_self" ~notrace:true goal nat_induct_auto;

  let goal =
    make_goal [%term forall (fun (a : nat) -> nat_le a (Suc a) = true)]
  in
  run_proof ~simp:true ~name:"le_Suc_self" ~notrace:true goal nat_induct_auto;

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

  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_le a b = nat_lt a (Suc b))]
  in
  run_proof ~name:"le_lt_Suc" ~notrace:true goal nat_induct_auto;

  (* (* ===== Group 4: Connection between lt and le ===== *) *)
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

  run_proof ~simp:true ~name:"eq_true_false"
    (make_goal [%term true = false = false])
    (eq_false_elim >> neg_intro
    >> with_assumptions @@ with_flip_rules rewrite
    >> truth);
  run_proof ~simp:true ~name:"eq_false_false"
    (make_goal [%term false = false = true])
    (eq_true_elim >> refl);
  run_proof ~simp:true ~name:"eq_true_true"
    (make_goal [%term true = true = false])
    (eq_true_elim >> refl);
  run_proof ~simp:true ~name:"eq_false_true"
    (make_goal [%term false = true = false])
    (eq_false_elim >> neg_intro >> simp);
  run_proof ~simp:true ~name:"neg_false_true"
    (make_goal [%term (not false) = true])
    (eq_true_elim >> neg_intro >> false_elim);
  run_proof ~simp:true ~name:"neg_true_false"
    (make_goal [%term (not true) = false])
    (eq_false_elim
    >> with_term [%term true] have
    >> truth >> neg_intro >> neg_elim);

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
    [@quiet]
  in
  ignore lt_implies_le;

  (* (* ===== Group 5: Transitivity ===== *) *)
  let assumption_reasoning =
    try_
      (with_no_automation_trace
         (with_best_first
            (pick [ simp; simp_asm; false_elim; assumption; truth ])))
  in

  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_lt a b ==> (nat_lt b c ==> nat_lt a c))]
  in
  run_proof ~name:"lt_trans" ~notrace:true goal
    (with_term [%term (a : nat)] induct
     @>> intros
     @>> with_term [%term (b : nat)] induct
     @>> intros
     @>> with_term [%term (c : nat)] induct
     @>> intros @>> try_ assumption_reasoning
    >>= [
          with_repeat (with_first (with_proven [ "lt_Suc_Suc" ] rewrite_asm))
          >> spec_asm [%term (n0' : nat)]
          >> spec_asm [%term (n0'' : nat)]
          >> with_proven [ "lt_Suc_Suc" ] rewrite
          >> with_repeat (with_assumptions (with_first_term apply_asm))
          >> assumption;
        ]);

  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_le a b ==> (nat_le b c ==> nat_le a c))]
  in
  run_proof ~name:"le_trans" ~notrace:true goal
    (with_term [%term (a : nat)] induct
     @>> intros
     @>> with_term [%term (b : nat)] induct
     @>> intros
     @>> with_term [%term (c : nat)] induct
     @>> intros @>> try_ assumption_reasoning
    >>= [
          with_repeat (with_first (with_proven [ "le_Suc_Suc" ] rewrite_asm))
          >> spec_asm [%term (n0' : nat)]
          >> spec_asm [%term (n0'' : nat)]
          >> with_proven [ "le_Suc_Suc" ] rewrite
          >> with_repeat (with_assumptions (with_first_term apply_asm))
          >> assumption;
        ]);

  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_le a b ==> (nat_lt b c ==> nat_lt a c))]
  in
  run_proof ~name:"le_lt_trans" ~notrace:true goal
    (with_term [%term (a : nat)] induct
     @>> intros
     @>> with_term [%term (b : nat)] induct
     @>> intros
     @>> with_term [%term (c : nat)] induct
     @>> intros @>> try_ assumption_reasoning
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

  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) (c : nat) ->
            nat_lt a b ==> (nat_le b c ==> nat_lt a c))]
  in
  run_proof ~name:"lt_le_trans" ~notrace:true goal
    (with_term [%term (a : nat)] induct
     @>> intros
     @>> with_term [%term (b : nat)] induct
     @>> intros
     @>> with_term [%term (c : nat)] induct
     @>> intros @>> try_ assumption_reasoning
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

  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) ->
            nat_le a b ==> (nat_le b a ==> ((a : nat) = b)))]
  in
  run_proof ~name:"le_antisym" ~notrace:true goal
    (with_term [%term (a : nat)] induct
     @>> intros
     @>> with_term [%term (b : nat)] induct
     @>> intros @>> try_ assumption_reasoning
    >> with_proven [ "eq_cong" ] apply
    >> with_repeat (with_first (with_proven [ "le_Suc_Suc" ] rewrite_asm))
    >> spec_asm [%term (n0' : nat)]
    >> with_repeat (with_assumptions (with_first_term apply_asm))
    >> assumption);

  (* (* ===== Group 6: Subtraction properties ===== *) *)
  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_le a b ==> nat_le a (Suc b))]
  in
  run_proof ~name:"le_weaken_Suc" ~notrace:true goal
    (with_term [%term (a : nat)] induct
     @>> intros
     @>> with_term [%term (b : nat)] induct
     @>> try_ intros @>> try_ assumption_reasoning
    >> with_proven [ "le_Suc_Suc" ] rewrite
    >> spec_asm [%term (n0' : nat)]
    >> with_repeat (with_first (with_proven [ "le_Suc_Suc" ] rewrite_asm))
    >> with_first (with_assumptions (with_first_term apply_asm))
    >> sorry);

  let goal =
    make_goal
      [%term
        forall (fun (a : nat) (b : nat) -> nat_lt a b ==> nat_lt a (Suc b))]
  in
  run_proof ~name:"lt_weaken_Suc" ~notrace:true goal
    (with_term [%term (a : nat)] induct
     @>> intros
     @>> with_term [%term (b : nat)] induct
     @>> try_ intros @>> try_ assumption_reasoning
    >> with_proven [ "lt_Suc_Suc" ] rewrite
    >> spec_asm [%term (n0' : nat)]
    >> with_repeat (with_first (with_proven [ "lt_Suc_Suc" ] rewrite_asm))
    >> with_first (with_assumptions (with_first_term apply_asm))
    >> sorry);

  let goal =
    make_goal [%term forall (fun (a : nat) (b : nat) -> nat_le (sub a b) a)]
  in
  run_proof ~name:"sub_le" ~notrace:true goal
    (with_term [%term (a : nat)] induct
     @>> intros
     @>> with_term [%term (b : nat)] induct
     @>> try_ intros @>> try_ assumption_reasoning
    >> with_proven [ "sub_Suc_Suc" ] rewrite
    >> spec_asm [%term (n0' : nat)]
    >> with_proven [ "le_weaken_Suc" ] apply
    >> assumption);

  let%thm sub_lt (b : nat) (a : nat) =
    nat_lt 0n b ==> (nat_le b a ==> nat_lt (sub a b) a)
  and proof =
    begin
      with_term [%term (b : nat)] induct @>> intros
      >> assumption_reasoning
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
    [@quiet]
  in
  ignore sub_lt;

  let%thm sub_add_cancel (a : nat) (b : nat) =
    nat_le b a ==> (plus (sub a b) b = a)
  and proof =
    begin
      with_term [%term (a : nat)] induct
      @>> (intros @: [ "hIH" ])
      @>> with_term [%term (b : nat)] induct
      @>> try_ intros @>> try_ assumption_reasoning
      >> (simp >> apply_at "eq_cong" >> apply_at "hIH" >> simp_asm >> simp)
    end
    [@quiet]
  in
  ignore sub_add_cancel;

  (* ===== Group 8: Ordering and addition ===== *)
  let goal =
    make_goal [%term forall (fun (a : nat) (b : nat) -> nat_le a (plus a b))]
  in
  run_proof ~name:"le_add_r" ~notrace:true goal nat_induct_auto;

  (* (* ===== Group 9: Totality ===== *) *)
  let%thm lt_total (a : nat) (b : nat) = nat_lt a b || nat_le b a
  and proof =
    begin
      with_term [%term (a : nat)] induct
      @>> intros
      @>> with_term [%term (b : nat)] induct
      @>> try_ intros
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
    [@quiet] [@notrace]
  in
  ignore lt_total;

  let goal =
    make_goal
      [%term forall (fun (a : nat) (b : nat) -> nat_le a b || nat_le b a)]
  in
  run_proof ~name:"le_total" ~notrace:true goal
    (with_term [%term (a : nat)] induct
     @>> intros
     @>> with_term [%term (b : nat)] induct
     @>> try_ intros
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

  let%thm div_unfold (a : nat) (b : nat) =
    nat_lt 0n b ==> (div a b = if nat_lt a b then 0n else Suc (div (sub a b) b))
  and proof =
    begin
      intros
      >> with_definition [ "div" ] rewrite
      >> beta
      >> with_first (with_definition [ "div_aux" ] rewrite)
      >> beta >> cond >> simp
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
    [@quiet]
  in
  ignore div_unfold;

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
    [@quiet]
  in
  ignore merge_fuel_irrel;

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

  (* sort [3,1,2] = [1,2,3] *)
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
    (with_term n induct @>> try_ intros @>> with_term xs induct @>> try_ intros
     @>> try_ assumption_reasoning
    >> with_repeat (with_first (with_definition [ "take"; "length" ] rewrite))
    >> beta
    >> with_repeat (with_first (with_definition [ "match_list" ] rewrite))
    >> beta
    >> with_first (with_definition [ "length" ] rewrite)
    >> spec_asm n1 >> with_assumptions rewrite
    >> with_first (with_proven [ "lt_Suc_Suc" ] rewrite)
    >> cond >> simp >> simp);
  run_proof ~name:"length_drop" ~notrace:true gdrop
    (with_term n induct @>> try_ intros @>> with_term xs induct @>> try_ intros
     @>> try_ assumption_reasoning
    >> with_repeat (with_first (with_definition [ "take"; "length" ] rewrite))
    >> beta
    >> with_repeat (with_first (with_definition [ "match_list" ] rewrite))
    >> beta
    >> with_first (with_definition [ "length" ] rewrite)
    >> spec_asm n1 >> with_assumptions rewrite
    >> with_first (with_proven [ "lt_Suc_Suc" ] rewrite)
    >> cond >> simp >> simp);

  let%thm div_pos (n : nat) = nat_lt 1n n ==> nat_lt 0n (div n 2n)
  and proof =
    begin
      with_term [%term (n : nat)] induct
      @>> intros @>> try_ assumption_reasoning
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
    [@quiet]
  in
  ignore div_pos;

  let apply_asm_to_asm ~asm_thm ~asm_to =
    with_nth_choice asm_thm (with_nth_term asm_to (with_assumptions apply_asm))
  in

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
      >> with_term [%term nat_lt (k : nat) (m : nat)] destruct_elim
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
    [@quiet]
  in
  ignore div_le;

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
    [@quiet]
  in
  ignore div_lt;

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
    [@quiet]
  in
  ignore merge_sort_fuel_sufficient;

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
    [@quiet]
  in
  ignore merge_sort_unfold
