open Kernel
open Result.Syntax
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
  (* let () = clear_env () in *)
  let _ = init_types () in
  let thm =
      let* plus_def =  plus_def in
      let nat_ind = Hashtbl.find_opt the_inductives "nat"  |> Option.get in
      let suc = nat_ind.constructors |> List.assoc_opt "Suc" |> Option.get in
      let zero = nat_ind.constructors |> List.assoc_opt "Zero" |> Option.get in

      let* one = make_app suc zero in
      let* two = make_app suc one in
      let* three = make_app suc two in

      let* zcase = conj_left plus_def in
      let* succase = conj_right plus_def in

      let (plus_name, plus_ty) = the_term_constants |> Hashtbl.to_seq |> Seq.find (fun (n, ty) -> n = "plus") |> Option.get in
      let plus = Const (plus_name, plus_ty) in

      let* plus_one = make_app plus one in
      let* one_plus_one = make_app plus_one one in
      (*lets try to prove that 1 + 1 = 2 *)
      let* inst_suc_case = spec zero succase in
      let* zcase_applied = ap_thm zcase one in
      let* zcase_reduc = conv_equality deep_beta zcase_applied in
      let* suc_both = ap_term suc zcase_reduc in
      let* applied = ap_thm inst_suc_case one in
      let* reduc = conv_equality deep_beta applied in
      let* t = trans reduc suc_both in
      (* not so bad *)

      (* how about comm? *)
      (* plus a b = plus b a*)
      let a = make_var "a" nat_ind.ty in
      let b = make_var "b" nat_ind.ty in
      let n = make_var "n" nat_ind.ty in
      let n' = make_var "n'" nat_ind.ty in

      let* plus_a  = make_app plus a in
      let* plus_ab = make_app plus_a b in

      let* plus_b  = make_app plus b in
      let* plus_ba = make_app plus_b a in
      let* goal = safe_make_eq plus_ab plus_ba in

      (*need lemmas*)
      let* plus_n = make_app plus n in
      let* plus_nZ = make_app plus_n zero in
      let* goal = safe_make_eq plus_nZ n in
      let* induction_inst = make_lam n goal in
      (* pp_term induction_inst; *)

      let type_inst = [(make_vartype "r", nat_ind.ty)] |> List.to_seq |> Hashtbl.of_seq in
      let* typed_induction_thm = inst_type type_inst nat_ind.induction in
      (* print_endline @@ pretty_print_thm ~with_type:true zcase; *)
      (* print_endline @@ pretty_print_thm ~with_type:true succase; *)
      (* print_endline @@ pretty_print_thm ~with_type:true typed_induction_thm; *)


      let* inst_induction = spec induction_inst typed_induction_thm in
      (* pp_thm inst_induction;  *)
      (*
      plus Zero Zero = Zero ==> 
      (∀n0. plus n0 Zero = n0 ==> plus (Suc n0) Zero = Suc n0) ==> 
      ∀x. plus x Zero = x
       *)
      (* start with base case *)
      let* zz = ap_thm zcase zero in
      let* rzz = conv_equality deep_beta zz in
      (*done*)
      let* first_discharged = mp inst_induction rzz in
      pp_thm first_discharged;

      let* ih_assm = assume @@ imp_left_term (concl first_discharged) in
      let* specced_ih = spec n' ih_assm in

      let ih_term = imp_left_term (concl specced_ih) in
      let step_term = imp_right_term (concl specced_ih) in
      pp_term ih_term;
      pp_term step_term;
      (* start the proof *)
      let* assm_ih = assume ih_term in
      let* this_scase = spec n' succase in
      pp_thm this_scase;
      let* ap2 = ap_thm this_scase zero in
      pp_thm ap2;
      let* reduc_ap2 = conv_equality deep_beta ap2 in
      pp_thm reduc_ap2;

      let* ap_ih = ap_term suc assm_ih in
      pp_thm ap_ih;

      let* th1 = trans reduc_ap2 ap_ih in
      pp_thm th1;

      let* th1_imp = disch ih_term th1 in
      pp_thm th1_imp;

      let* gen_th1 = gen n' th1_imp in
      pp_thm gen_th1;

      let* th2 = mp first_discharged gen_th1 in
      pp_thm th2;
      (* woohoo *)


      Ok truth

  in

  print_thm_result thm;
  [%expect {|
    |}]
