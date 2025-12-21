open Kernel
open Result.Syntax
open Inductive
open Derived
open Printing
open Inductive_theorems

let print_term = Fun.compose print_endline show_term
let print_thm = Fun.compose print_endline show_thm
let print_types = ref false

let clear_env () =
  Hashtbl.clear the_inductives;
  Hashtbl.clear the_term_constants;
  Hashtbl.clear the_type_constants;
  the_axioms := [];
  the_definitions := []

let print_thm_result =
  Format.pp_print_result
    ~ok:(fun fmt thm ->
      Format.pp_print_string fmt (pretty_print_thm ~with_type:!print_types thm))
    ~error:pp_kernel_error Format.std_formatter

let print_term_result =
  Format.pp_print_result
    ~ok:(fun fmt term ->
      Format.pp_print_string fmt
        (pretty_print_hol_term ~with_type:!print_types term))
    ~error:pp_kernel_error Format.std_formatter

let%expect_test "test inductive nats" =
  let () = clear_env () in
  let _ = init_types () in
  let thm =
        let nat_ty =  TyCon ("nat", []) in
        let* nat_def = nat_def in
        let suc = nat_def.constructors |> List.assoc_opt "Suc" |> Option.get in

        let n = make_var "n"  nat_ty in
        let m = make_var "m" nat_ty in
        let m' = make_var "m'" nat_ty in
        let r = make_var "r" nat_ty in

        let zero_case = n in
        let* suc_case = 
            let* a = make_app suc r in
            let* b = make_lam r a in 
            make_lam m' b
        in
        let* typed_nat_def = inst_type ([(make_vartype "r", type_of_var r)] |> List.to_seq |> Hashtbl.of_seq) nat_def.recursion in
        let* specced = specs [zero_case; suc_case] typed_nat_def in
        (* print_endline @@ pretty_print_thm ~with_type:true specced; *)
        let plus_n = make_var "plus_n" (make_fun_ty nat_ty nat_ty) in
        let* def = new_specification plus_n specced in
        Ok def 

  in

  print_thm_result thm;
  [%expect {|
    |}]
