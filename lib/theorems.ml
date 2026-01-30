open Kernel
open Derived
open Result.Syntax
open Inductive

let p = Var ("P", bool_ty)
let q = Var ("Q", bool_ty)
let r = Var ("R", bool_ty)
let s = Var ("S", bool_ty)
let g = Var ("f", TyCon ("fun", [ bool_ty; bool_ty ]))
let x = Var ("x", bool_ty)
let y = Var ("y", bool_ty)
let z = Var ("z", bool_ty)
let axiom_for_test tm = Result.get_ok (new_axiom tm)

let double_negation_implies_p =
  let thm =
    let neg_neg_p = make_neg (make_neg p) in
    let p = p in
    let* start = assume neg_neg_p in
    let* nelim = not_elim start in
    let* contr = ccontr p nelim in
    disch neg_neg_p contr
  in
  make_exn thm

let forall_symmetry =
  let thm =
    let* x_eq_y = safe_make_eq x y in

    let* xy_th = assume x_eq_y in
    let* yx_th = sym xy_th in
    let* imp = disch x_eq_y yx_th in
    gens [ x; y ] imp
  in
  make_exn thm

let identity =
  let thm =
    let* p_th = assume p in
    disch p p_th
  in
  make_exn thm

let contrapositive =
  let thm =
    let p_imp_q = make_imp p q in

    let* pq_th = assume p_imp_q in
    let* nq_th = assume (make_neg q) in
    let* p_th = assume p in
    let* qmp = mp pq_th p_th in
    let* nnq = not_elim nq_th in
    let* combined = prove_hyp qmp nnq in
    let* np = not_intro p combined in
    let* d1 = disch (make_neg q) np in
    let* d2 = disch p_imp_q d1 in
    Ok d2
  in
  make_exn thm

let nat_def =
  let nat_ty = TyCon ("nat", []) in
  define_inductive "nat" []
    [
      { name = "Zero"; arg_types = [] };
      { name = "Suc"; arg_types = [ nat_ty ] };
    ]
  |> Result.get_ok

let plus_def =
  let d =
    let nat_ty = TyCon ("nat", []) in
    let nat_def = nat_def in
    let suc = nat_def.constructors |> List.assoc_opt "Suc" |> Option.get in
    let n = make_var "n" nat_ty in
    let m' = make_var "m'" nat_ty in
    let r = make_var "r" (make_fun_ty nat_ty nat_ty) in
    let* zero_case = make_lam n n in
    (* λn. n *)
    let* suc_case =
      let* r_n = make_app r n in
      let* suc_rn = make_app suc r_n in
      let* lam_n_suc_rn = make_lam n suc_rn in
      let* lam_r = make_lam r lam_n_suc_rn in
      make_lam m' lam_r (* λm'. λr. λn. Suc (r n) *)
    in
    let return_type = make_fun_ty nat_ty nat_ty in
    define_recursive_function "plus" return_type "nat" [ zero_case; suc_case ]
  in
  d |> Result.get_ok
