open Heft
open Kernel
open Derived
open Tactic

(* [@@@warning "-26-27-32-33"] *)

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
