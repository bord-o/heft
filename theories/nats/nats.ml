open Heft
open Kernel
open Result.Syntax
open Derived
open Tactic
open Auto

let () = print_endline "initializing theory nats"

[%%inductive type nat = Zero | Suc of nat]

let%def pred (n : nat) : nat = match n with Zero -> Zero | Suc m -> m

let%primrec plus (n : nat) (m : nat) : nat =
  match n with Zero -> m | Suc n' -> Suc (plus n' m)

let _ = plus

let%primrec minus' (n : nat) (m : nat) : nat =
  match n with Zero -> m | Suc n' -> pred (minus' n' m)

let%def minus (n : nat) : nat -> nat = (flip minus') n

let%primrec mult (n : nat) (m : nat) : nat =
  match n with Zero -> Zero | Suc n' -> plus m (mult n' m)

let%primrec nat_match (n : nat) (zero_case : 'a) (suc_case : nat -> 'a) : 'a =
  match n with Zero -> zero_case | Suc n' -> suc_case n'

let%def is_zero (n : nat) : bool = match n with Zero -> true | Suc n' -> false

let%primrec nat_le (n : nat) (m : nat) : bool =
  match n with
  | Zero -> true
  | Suc n' -> ( match m with Zero -> false | Suc k -> nat_le n' k)

let%primrec nat_lt (n : nat) (m : nat) : bool =
  match n with
  | Zero -> ( match m with Zero -> false | Suc k -> true)
  | Suc n' -> ( match m with Zero -> false | Suc k -> nat_lt n' k)

let%primrec sub (n : nat) (m : nat) : nat =
  match n with
  | Zero -> Zero
  | Suc n' -> ( match m with Zero -> Suc n' | Suc k -> sub n' k)

let%primrec div_aux (fuel : nat) (a : nat) (b : nat) : nat option =
  match fuel with
  | Zero -> None
  | Suc left -> (
      if nat_lt a b then Some Zero
      else
        match (div_aux left (sub a b) b : nat option) with
        | None -> None
        | Some r -> Some (Suc r))

let%def div (a : nat) (b : nat) : nat =
  match (div_aux (Suc a) a b : nat option) with None -> Zero | Some x -> x

let nat_ty = make_type "nat" [] |> Result.get_ok
let nat_def = Hashtbl.find the_inductives "nat"
let zero = make_const "Zero" [] |> Result.get_ok
let suc = make_const "Suc" [] |> Result.get_ok
let rec nat_of_int n = if n <= 0 then zero else App (suc, nat_of_int (n - 1))
let n0 = zero
let n1 = nat_of_int 1
let n2 = nat_of_int 2
let n3 = nat_of_int 3
let n4 = nat_of_int 4
let n5 = nat_of_int 5
let n6 = nat_of_int 6
let n7 = nat_of_int 7
let n8 = nat_of_int 8
let n9 = nat_of_int 9
let n10 = nat_of_int 10

let plus =
  let v = make_const "plus" [] in
  match v with Ok t -> t | Error e -> failwith @@ Printing.print_error e

let make_plus a b =
  let* ab = make_app plus a in
  make_app ab b

[@@@ocamlformat "disable"]
let%thm plus_x_Zero (x : nat) = 
    plus x Zero = x
and proof =
  begin
    induct_tac >> simp_tac >> gen_tac >> intro_tac >> simp_tac
  end [@quiet] [@simp]

let%thm plus_assoc (x : nat ) (y:nat) (z:nat) = 
    plus x (plus y z) = plus (plus x y) z
and proof =
  begin
    induct_tac >> intros_tac >> simp_tac >> intros_tac >> simp_tac
  end [@quiet]

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
       >> with_rules nat_def.injective apply_tac
       >> assumption_tac >> elim_disj_asm_tac >> left_tac >> assumption_tac
       >> right_tac >> apply_at_tac "eq_cong" >> assumption_tac)
  end
  (* [@trace] *)
  [@quiet]
