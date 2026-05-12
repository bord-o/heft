open Heft
open Kernel
open Result.Syntax
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
    induct >> simp >> gen >> intro >> simp
  end [@quiet] [@simp]

let%thm plus_assoc (x : nat ) (y:nat) (z:nat) = 
    plus x (plus y z) = plus (plus x y) z
and proof =
  begin
    induct >> intros >> simp >> intros >> simp
  end [@quiet]

let%thm lt_Zero_false (m : nat) = nat_lt m Zero = false

and proof =
  begin
    induct
    >> with_no_automation_trace auto_dfs
    >> with_no_automation_trace auto_dfs
  end
  [@simp] [@quiet]

let%thm lt_Suc_or_eq (m : nat) (n : nat) =
  nat_lt m (Suc n) = (nat_lt m n || m = n)

and proof =
  begin
    induct
    >> (intros >> simp >> sym >> eq_true_elim
       >> with_term [%term (n : nat)] destruct
       >> elim_disj_asm
       >> (simp >> right >> refl)
       >> (elim_exists_asm >> simp >> left >> truth))
    >> (intros @: [ "hIH" ]
       >> with_term [%term (n : nat)] destruct
       >> elim_disj_asm >> simp >> sym >> eq_false_elim
       >> neg_intro
       >> elim_disj_asm @: [ "hfalse"; "hrest" ]
       >> assumption
       >> with_named_asm_term "hrest" sym_asm @: [ "hrest'" ]
       >> discriminate >> elim_exists_asm >> simp >> eq_iff
       >> elim_disj_asm @: [ "hlt_na"; "heq_na" ]
       >> left >> assumption >> right
       >> with_rules nat_def.injective apply
       >> assumption >> elim_disj_asm >> left >> assumption
       >> right >> apply_at "eq_cong" >> assumption)
  end
  (* [@trace] *)
  [@quiet]

let%thm plus_Suc (m : nat) (n : nat) = 
    plus m (Suc n) = Suc (plus m n)
and proof =
    begin
        induct >> gen >> simp >> intros >> simp
    end
    [@simp]
    [@quiet]


let%thm nat_distinct_flip (m : nat) = Suc m = Zero = F

and proof =
  begin
    noop >> intros >> eq_false_elim >> neg_intro >> sym_asm
    >> with_rules nat_def.distinct (with_first rewrite_asm)
    >> assumption
  end
  [@quiet]


let%thm nat_le_refl (n : nat) = nat_le n n

and proof =
  begin
    induct >> simp >> intros >> simp >> assumption
  end
  [@quiet] 

let%thm nat_lt_antisym (m : nat) (n : nat) = nat_lt m n = T ==> (nat_lt n m = F)

and proof =
  begin
    induct
    >>= [
          induct >>= [ intros >> simp; intros >> simp ];
          gen >> intro @! "ih" >> induct
          >>= [
                intros @! "heq" >> simp_asm >> eq_false_elim >> neg_intro
                >> simp;
                intros >> simp >> apply_at "ih" >> simp_asm;
              ];
        ]
  end
  [@quiet]

let%thm not_lt_bidir (m : nat) (n : nat) =
  nat_lt m n = false ==> (nat_lt n m = false ==> (n = m))

and proof =
  begin
    induct
    >>= [
          induct
          >>= [
                simp >> intros >> refl;
                intros >> simp_all >> ccontr
                >> with_assumptions @@ with_flip_rules (with_first @@ rewrite)
                >> truth;
              ];
          gen >> intro @! "hall" >> induct
          >>= [
                intros >> simp_all >> ccontr
                >> with_assumptions @@ with_flip_rules (with_first @@ rewrite)
                >> truth;
                intros @: [ "h1"; "h2"; "h3" ]
                >> apply_at "eq_cong" >> apply_at "hall" >> simp_all >> simp_all;
              ];
        ]
  end
  [@quiet]

let assumption_reasoning =
  try_
    (with_no_automation_trace
       (with_best_first
          (pick [ simp; simp_asm; false_elim; assumption; truth ])))

  let%thm sub_lt (b : nat) (a : nat) =
    nat_lt 0n b ==> (nat_le b a ==> nat_lt (sub a b) a)
  and proof =
    begin
        sorry
      (* with_term [%term (b : nat)] induct *)
      (* @>> intros >> assumption_reasoning *)
      (* >> with_term [%term (a : nat)] destruct *)
      (* >> elim_disj_asm >> simp_asm >> simp >> assumption >> elim_exists_asm *)
      (* >> with_first (with_assumptions rewrite) *)
      (* >> with_first (with_assumptions rewrite) *)
      (* >> with_first (with_assumptions rewrite_asm) *)
      (* >> with_proven [ "sub_Suc_Suc" ] rewrite *)
      (* >> with_first (with_proven [ "le_Suc_Suc" ] rewrite_asm) *)
      (* >> with_term [%term (n0 : nat)] destruct *)
      (* >> elim_disj_asm >> simp >> elim_exists_asm *)
      (* >> with_proven [ "lt_weaken_Suc" ] apply *)
      (* >> spec_asm [%term (a0 : nat)] *)
      (* >> simp_asm >> simp *)
      (* >> with_repeat (with_assumptions (with_first_term apply_asm)) *)
      (* >> assumption *)
    end
    [@quiet]
