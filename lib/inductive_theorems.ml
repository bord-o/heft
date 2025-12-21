open Kernel
open Result.Syntax
open Printing
open Derived
open Inductive

let pp_thm th = print_newline @@ print_endline @@ Printing.pretty_print_thm th

let pp_term trm =
  print_newline @@ print_endline @@ Printing.pretty_print_hol_term trm
type nat = Zero | Suc of nat

let rec add_nat m n = match m, n with
    | Zero, n ->  n
    | Suc(m'), n -> Suc (add_nat m' n)


let nat_def = 
    let nat_ty =  TyCon ("nat", []) in
    define_inductive "nat" [] [
      { name = "Zero"; arg_types = [] };
      { name = "Suc"; arg_types = [ nat_ty ] };
    ]

let new_specification name ex_thm =
    let g, bod = destruct_exists (concl ex_thm) in
    let* g_ty = type_of_term g in

    let* existence_pred = make_lam g bod in

    let* choice_def = choice_def in
    let* typed_choice_def = inst_type ([(make_vartype "a", g_ty)] |> List.to_seq |> Hashtbl.of_seq) choice_def in

    pp_term bod;
    (* pp_thm ex_thm; *)
    (* print_endline @@ pretty_print_hol_term ~with_type:true existence_pred; *)
    (* print_endline @@ pretty_print_thm ~with_type:true typed_choice_def; *)
    (* print_endline @@ pretty_print_thm ~with_type:true ex_thm; *)

    let* this_def = spec existence_pred typed_choice_def in
    let* this_choice = mp this_def ex_thm in

    Ok this_choice 


(* let nat_add =  *)
(*     let* nat_def = nat_def in *)
(*     let suc = nat_def.constructors |> List.assoc_opt "Suc" |> Option.get in *)
(**)
(*     let* nat_ty = make_type "nat" [] in *)
(*     let n = make_var "n"  nat_ty in *)
(*     let m = make_var "m" nat_ty in *)
(*     let m' = make_var "m'" nat_ty in *)
(*     let r = make_var "r" nat_ty in *)
(**)
(*     let zero_case = n in *)
(*     let* suc_case =  *)
(*         let* a = make_app suc r in *)
(*         let* b = make_lam r a in  *)
(*         make_lam m' b *)
(*     in *)
(*     pp_term suc_case; *)
(**)
(*     Ok () *)
(**)
