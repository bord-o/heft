open Heft
open Kernel
open Derived
open Result.Syntax
open Tactic

let t = make_true ()
let f = make_false ()
let init () = ()

let not_t_eq_f =
  let thm =
    let* t_eq_f = safe_make_eq t f in
    let* assumed = assume t_eq_f in
    let* false_th = eq_mp assumed truth in
    disch t_eq_f false_th
  in
  make_exn thm

let not_f_eq_t =
  let thm =
    let* f_eq_t = safe_make_eq f t in
    let* assumed = assume f_eq_t in
    let* flipped = sym assumed in
    let* false_th = eq_mp flipped truth in
    disch f_eq_t false_th
  in
  make_exn thm

let t_eq_t = make_exn (eq_truth_intro (Result.get_ok (refl t)))

let t_eq_f =
  let thm =
    let* t_eq_f = safe_make_eq t f in
    let* fwd = undisch not_t_eq_f in
    let* f_assumed = assume f in
    let* bwd = contr t_eq_f f_assumed in
    deduct_antisym_rule bwd fwd
  in
  make_exn thm

let f_eq_t =
  let thm =
    let* f_eq_t = safe_make_eq f t in
    let* fwd = undisch not_f_eq_t in
    let* f_assumed = assume f in
    let* bwd = contr f_eq_t f_assumed in
    deduct_antisym_rule bwd fwd
  in
  make_exn thm

let f_eq_f = make_exn (eq_truth_intro (Result.get_ok (refl f)))

let t_imp_eq =
  let thm =
    let p = Var ("P", bool_ty) in
    let t_imp_p = make_imp t p in
    let* t_imp_p_assumed = assume t_imp_p in
    let* fwd = mp t_imp_p_assumed truth in
    let* p_assumed = assume p in
    let* bwd = disch t p_assumed in
    let* eq_th = deduct_antisym_rule bwd fwd in
    gen p eq_th
  in
  make_exn thm

let f_imp_eq =
  let thm =
    let p = Var ("P", bool_ty) in
    let* f_assumed = assume f in
    let* p_from_f = contr p f_assumed in
    let* f_imp_p_thm = disch f p_from_f in
    let* eq_th = eq_truth_intro f_imp_p_thm in
    gen p eq_th
  in
  make_exn thm

let conj_t_eq =
  let thm =
    let p = Var ("P", bool_ty) in
    let p_and_t = make_conj p t in
    let* fwd = conj_left (Result.get_ok (assume p_and_t)) in
    let* p_assumed = assume p in
    let* bwd = conj p_assumed truth in
    let* eq_th = deduct_antisym_rule bwd fwd in
    gen p eq_th
  in
  make_exn thm

let t_conj_eq =
  let thm =
    let p = Var ("P", bool_ty) in
    let t_and_p = make_conj t p in
    let* fwd = conj_right (Result.get_ok (assume t_and_p)) in
    let* p_assumed = assume p in
    let* bwd = conj truth p_assumed in
    let* eq_th = deduct_antisym_rule bwd fwd in
    gen p eq_th
  in
  make_exn thm

let select_eq =
  let thm =
    let a_ty = TyVar "a" in
    let a = Var ("a", a_ty) in
    let x = Var ("x", a_ty) in
    let* choice = choice_def in
    let* x_eq_a = safe_make_eq x a in
    let* pred = make_lam x x_eq_a in
    let* specced = spec pred choice in
    let* a_eq_a = refl a in
    let* exists_witness = exists_p x x_eq_a a a_eq_a in
    let* applied = mp specced exists_witness in
    let* beta_th = deep_beta (concl applied) in
    let* result = eq_mp beta_th applied in
    gen a result
  in
  make_exn thm

let goal = make_goal [%term (if true then (t1 : 'a) else (t2 : 'a)) = (t1 : 'a)]

let () =
  run_proof ~notrace:true ~name:"cond_true" ~simp:true ~quiet:true goal
    (with_rule (cond_def |> Result.get_ok) rewrite_tac
    >> beta_tac
    >> with_rule t_eq_t rewrite_tac
    >> with_rule t_eq_f rewrite_tac
    >> with_rule f_imp_eq rewrite_tac
    >> with_rule conj_t_eq rewrite_tac
    >> with_rule t_imp_eq rewrite_tac
    >> with_rule select_eq rewrite_tac
    >> refl_tac)

let goal =
  make_goal [%term (if false then (t1 : 'a) else (t2 : 'a)) = (t2 : 'a)]

let () =
  run_proof ~notrace:true ~name:"cond_false" ~simp:true ~quiet:true goal
    (with_rule (cond_def |> Result.get_ok) rewrite_tac
    >> beta_tac
    >> with_rule f_eq_t rewrite_tac
    >> with_rule f_eq_f rewrite_tac
    >> with_rule f_imp_eq rewrite_tac
    >> with_rule t_conj_eq rewrite_tac
    >> with_rule t_imp_eq rewrite_tac
    >> with_rule select_eq rewrite_tac
    >> refl_tac)
