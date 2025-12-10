open Kernel
open Result.Syntax

let pp_thm th = print_newline @@ print_endline @@ Printing.pretty_print_thm th

let pp_term trm =
  print_newline @@ print_endline @@ Printing.pretty_print_hol_term trm

let make_exn (thm : (thm, kernel_error) result) =
  thm
  |> Result.map_error (fun e -> show_kernel_error e)
  |> Result.error_to_failure

(**)
(* initialization *)
(**)




let ap_term tm th =
  let thm =
    let* rth = refl tm in
    mk_comb rth th
  in
  make_exn thm

let ap_thm th tm =
  let thm =
    let* term_rfl = refl tm in
    mk_comb th term_rfl
  in
  make_exn thm

let sym th =
  let tm = concl th in
  let* l, _ = destruct_eq tm in
  let* lth = refl l in
  let* r = rator tm in
  let* rr = rator r in
  let applied = ap_term rr th in
  let* comb = mk_comb applied lth in
  eq_mp comb lth

(* \p. p = \p. p is true*)
let truth =
  let thm =
    let p = Var ("p", bool_ty) in
    (* p : bool*)
    let id_fun = Lam (p, p) in
    (*\p. p*)
    let* id_fun_eq = safe_make_eq id_fun id_fun in
    (* \p. p = \p. p *)
    let* t_eq = safe_make_eq (make_var "T" bool_ty) id_fun_eq in
    (* T = (\p. p = \p. p )*)
    let* t_def = new_basic_definition t_eq in
    (* define it *)
    let* id_fun_refl = refl id_fun in
    (* |- \p. p = \p. p  *)
    let* t_def_sym = sym t_def in
    (* |- (\p. p = \p. p ) = T*)
    eq_mp t_def_sym id_fun_refl
  in
  make_exn thm

(* |- p should derive |- p = T *)
let eq_truth_intro thm = make_exn (deduct_antisym_rule thm truth)

(* |- p = T  should derive |- p *)
let eq_truth_elim th =
  let thm =
    let* thm_sym = sym th in
    eq_mp thm_sym truth
  in
  make_exn thm

let undisch th =
  print_endline "the goal: {p ==> q, p} ⊢ q";
  let* _p = refl (make_var "p" bool_ty) in
  Ok th

let wip () =
  let p = make_var "p" bool_ty in
  let q = make_var "q" bool_ty in
  let p_imp_q = make_imp p q in
  let* p_imp_q_thm = assume p_imp_q in
  undisch p_imp_q_thm
