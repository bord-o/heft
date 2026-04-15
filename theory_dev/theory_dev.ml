open Heft
open Kernel
open Derived
open Tactic
open Auto
(**)
(* let () = Heft_theories.Sets.init () *)

let () =
  print_newline ();
  print_newline ()

[@@@warning "-26-27-32-33"]

(* [@@@ocamlformat "disable"] *)

let%thm eq_cong (f : 'a -> 'b) (x : 'a) (y : 'a) = x = y ==> (f x = f y)

and proof =
  begin
    intros_tac >> simp_tac
  end
  [@quiet]

let%thm lt_Zero_false (m : nat) = nat_lt m Zero = false

and proof =
  begin
    induct_tac
    >> with_no_automation_trace auto_dfs_tac
    >> with_no_automation_trace auto_dfs_tac
  end
  [@simp] [@quiet]

let%thm lt_Suc_or_eq (m : nat) (n : nat) =
  nat_lt m (Suc n) = (nat_lt m n || m = n)

and proof =
  begin
    induct_tac
    >> (intros_tac >> simp_tac >> sym_tac >> eq_true_elim_tac
       >> with_term [%term (n : nat)] destruct_tac
       >> elim_disj_asm_tac
       >> (simp_tac >> right_tac >> refl_tac)
       >> (elim_exists_asm_tac >> simp_tac >> left_tac >> truth_tac))
    >> (intros_tac @: [ "hIH" ]
       >> with_term [%term (n : nat)] destruct_tac
       >> elim_disj_asm_tac >> simp_tac >> sym_tac >> eq_false_elim_tac
       >> neg_intro_tac
       >> elim_disj_asm_tac @: [ "hfalse"; "hrest" ]
       >> assumption_tac
       >> with_named_asm_term "hrest" sym_asm_tac @: [ "hrest'" ]
       >> discriminate_tac >> elim_exists_asm_tac >> simp_tac >> eq_iff_tac
       >> elim_disj_asm_tac @: [ "hlt_na"; "heq_na" ]
       >> left_tac >> assumption_tac >> right_tac
       >> with_rules Nats.nat_def.injective apply_tac
       >> assumption_tac >> elim_disj_asm_tac >> left_tac >> assumption_tac
       >> right_tac >> apply_at_tac "eq_cong" >> assumption_tac)
  end
  (* [@trace] *)
  [@quiet]

(* ∀P. (∀n. (∀m. m < n ==> P m) ==> P n) ==> ∀n. P n *)
let%thm nat_induct_strong (p : nat -> bool) =
  forall (fun (n : nat) -> forall (fun (m : nat) -> nat_lt m n ==> p m) ==> p n)
  ==> forall (fun (n : nat) -> p n)

and proof =
  begin
    intros_tac @: [ "hstrong" ]
    >> with_term
         [%term
           forall (fun (n : nat) (m : nat) ->
               nat_lt m n ==> (p : nat -> bool) m)]
         assert_tac
       @: [ "hweak" ]
    >> induct_tac >> intros_tac >> simp_asm_tac >> false_elim_tac
    >> intros_tac @: [ "hIH"; "hlt" ]
    >> with_term [%term nat_lt (m : nat) (Suc (n0 : nat))] cases_tac
       @: [ "htrue"; "hfalse" ]
    >> rewrite_at_tac "lt_Suc_or_eq" ~target:"hlt"
    >> elim_disj_asm_tac @: [ "hlt_mn"; "heq_mn" ]
    >> apply_at_tac "hIH" ~target:"hlt_mn"
    >> assumption_tac >> rewrite_at_tac "heq_mn" >> apply_at_tac "hstrong"
    >> assumption_tac
    >> rewrite_at_tac "hfalse" ~target:"hlt"
    >> false_elim_tac
    (* TODO make apply handle nested quantification better*)
    >> with_named_asm_term "hweak" (spec_asm_tac [%term (n : nat)])
       @: [ "hweak'" ]
    >> with_named_asm_term "hstrong" (spec_asm_tac [%term (n : nat)])
       @: [ "hstrong'" ]
    >> apply_at_tac "hstrong'" ~target:"hweak'"
    >> assumption_tac
  end
  (* [@trace] *)
  [@quiet]

let%def wf (r : 'a -> 'a -> bool) : bool =
  forall (fun (p : 'a -> bool) ->
      forall (fun (x : 'a) -> forall (fun (y : 'a) -> r y x ==> p y) ==> p x)
      ==> forall (fun (x : 'a) -> p x))

let%thm wf_num = wf nat_lt

and proof =
  begin
    rewrite_at_tac "wf" >> beta_tac
    >> with_info_trace (with_proven [ "nat_induct_strong" ] exact_tac)
  end
  [@quiet]

let%thm wf_measure_gen (r : 'b -> 'b -> bool) (m : 'a -> 'b) =
  wf r ==> wf (fun (x : 'a) (y : 'a) -> r (m x) (m y))

and proof =
  begin
    rewrite_at_tac "wf" >> beta_tac >> rewrite_at_tac "wf" >> beta_tac
    >> intros_tac @: [ "hwflam"; "hwfr" ]
    >> with_named_asm_term "hwflam"
         (spec_asm_tac
            [%term
              fun (b : 'b) ->
                forall (fun (a : 'a) ->
                    (m : 'a -> 'b) a = b ==> (p : 'a -> bool) a)])
       @: [ "hwfspec" ]
    >> with_named_asm_term "hwfspec" assert_premise_tac @: [ "hprem" ]
    >> intros_tac @: [ "hall"; "heq" ]
    >> with_named_asm_term "hwfr" (spec_asm_tac [%term (a : 'a)])
       @: [ "hwfr_a" ]
    >> apply_at_tac "hwfr_a" >> intros_tac @: [ "hr" ]
    >> rewrite_at_tac "heq" ~target:"hr"
    >> apply_at_tac "hall" ~target:"hr" @: [ "hall'" ]
    >> apply_at_tac "hall'" >> refl_tac
    >> apply_at_tac "hwfspec" ~target:"hprem" @: [ "hall'" ]
    >> with_named_asm_term "hall'"
         (spec_asm_tac [%term (m : 'a -> 'b) (x : 'a)])
       @: [ "hfinal" ]
    >> apply_at_tac "hfinal" >> refl_tac
  end
  [@quiet]

let%def measure (m : 'a -> nat) : 'a -> 'a -> bool =
 fun (x : 'a) (y : 'a) -> nat_lt (m x) (m y)

(* let () = Printing.print_thm measure  *)

let%thm wf_measure (m : 'a -> nat) = wf (measure m)

and proof =
  begin
    rewrite_at_tac "measure" >> beta_tac >> gen_tac
    >> apply_at_tac "wf_measure_gen"
    >> with_proven [ "wf_num" ] exact_tac
  end
  [@quiet]

let%thm wf_rec (r : 'a -> 'a -> bool) =
  wf r
  ==> forall (fun (h : ('a -> 'b) -> 'a -> 'b) ->
      forall (fun (f : 'a -> 'b) (g : 'a -> 'b) (x : 'a) ->
          forall (fun (z : 'a) -> r z x ==> (f z = g z)) ==> (h f x = h g x))
      ==> exists (fun (f : 'a -> 'b) -> forall (fun (x : 'a) -> f x = h f x)))

and proof =
  begin
    intros_tac @: [ "hwf"; "himp" ] >> sorry_tac
  end
  [@quiet]

let () = ()
