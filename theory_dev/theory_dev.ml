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

[@@@ocamlformat "disable"]

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
    >> (with_names [ "hIH" ] intros_tac
       >> with_term [%term (n : nat)] destruct_tac
       >> elim_disj_asm_tac >> simp_tac >> sym_tac >> eq_false_elim_tac
       >> neg_intro_tac
       >> with_names [ "hfalse"; "hrest" ] elim_disj_asm_tac
       >> assumption_tac
       >> with_names [ "hrest'" ] (with_named_asm_term "hrest" sym_asm_tac)
       >> discriminate_tac
       >> elim_exists_asm_tac >> simp_tac >> eq_iff_tac
       >> with_names [ "hlt_na"; "heq_na" ] elim_disj_asm_tac
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
    with_names [ "hstrong" ] intros_tac
    >> with_names [ "hweak" ]
         (with_term
            [%term
              forall (fun (n : nat) (m : nat) ->
                  nat_lt m n ==> (p : nat -> bool) m)]
            assert_tac)
    >> induct_tac >> intros_tac >> simp_asm_tac >> false_elim_tac
    >> with_names [ "hIH"; "hlt" ] intros_tac
    >> with_names [ "htrue"; "hfalse" ]
         (with_term [%term nat_lt (m : nat) (Suc (n0 : nat))] cases_tac)
    >> rewrite_at_tac "lt_Suc_or_eq" ~target:"hlt"
    >> with_names [ "hlt_mn"; "heq_mn" ] elim_disj_asm_tac
    >> apply_at_tac "hIH" ~target:"hlt_mn"
    >> assumption_tac >> rewrite_at_tac "heq_mn" >> apply_at_tac "hstrong"
    >> assumption_tac
    >> rewrite_at_tac "hfalse" ~target:"hlt"
    >> false_elim_tac
    (* TODO make apply handle nested quantification better*)
    >> with_names [ "hweak'" ]
         (with_named_asm_term "hweak" (spec_asm_tac [%term (n : nat)]))
    >> with_names [ "hstrong'" ]
         (with_named_asm_term "hstrong" (spec_asm_tac [%term (n : nat)]))
    >> apply_at_tac "hstrong'" ~target:"hweak'"
    >> assumption_tac
  end
(* [@trace] *)
[@quiet]

let%def wf (r : 'a -> 'a -> bool) : bool =
  forall (fun (p : 'a -> bool) ->
      forall (fun (x : 'a) -> forall (fun (y : 'a) -> r y x ==> p y) ==> p x)
      ==> forall (fun (x : 'a) -> p x))

let%thm wf_num =
  wf (nat_lt)
and proof =
begin
    rewrite_at_tac "wf"  >> beta_tac
    >> with_info_trace (with_proven ["nat_induct_strong"] exact_tac)
end
(* [@trace] *)
(* let () = Printing.print_thm wf *)

let () = ()
