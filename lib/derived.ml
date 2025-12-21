open Kernel
open Result.Syntax
open Util

let pp_thm th = print_newline @@ print_endline @@ Printing.pretty_print_thm th

let pp_term trm =
  print_newline @@ print_endline @@ Printing.pretty_print_hol_term trm

let make_exn (thm : (thm, kernel_error) result) =
  thm
  |> Result.map_error (fun e -> show_kernel_error e)
  |> Result.error_to_failure

(**)
(* initialization *)

let init_types () =
  let* () = new_type "bool" 0 in
  let* () = new_type "fun" 2 in
  Ok ()

(* T = ((λp:bool. p) = (λp. p)) *)
let init_true () =
  let p = Var ("p", bool_ty) in
  let id = Lam (p, p) in
  let* id_eq_id = safe_make_eq id id in
  let t_var = Var ("T", bool_ty) in
  let* def_eq = safe_make_eq t_var id_eq_id in
  new_basic_definition def_eq

let make_true () = Const ("T", bool_ty)

(* ∀ = (λP. P = (λx. T)) *)
let init_forall () =
  let a = TyVar "a" in
  let pred_ty = make_fun_ty a bool_ty in
  let forall_ty = make_fun_ty pred_ty bool_ty in
  let forall_var = Var ("!", forall_ty) in
  let p_var = Var ("P", pred_ty) in
  let x_var = Var ("x", a) in
  let t = make_true () in
  let lam_x_t = Lam (x_var, t) in
  let* p_eq_lam = safe_make_eq p_var lam_x_t in
  let rhs = Lam (p_var, p_eq_lam) in
  let* def_eq = safe_make_eq forall_var rhs in
  new_basic_definition def_eq

let make_forall_const var_ty =
  let pred_ty = make_fun_ty var_ty bool_ty in
  let forall_ty = make_fun_ty pred_ty bool_ty in
  Const ("!", forall_ty)

let make_forall var body =
  let var_ty = type_of_var var in
  App (make_forall_const var_ty, Lam (var, body))

let make_foralls vars body = List.fold_right make_forall vars body

(* ∧ = (λp q. (λf. f p q) = (λf. f T T)) *)
let init_conj () =
  let p = Var ("p", bool_ty) in
  let q = Var ("q", bool_ty) in
  let conj_var =
    Var ("/\\", make_fun_ty bool_ty (make_fun_ty bool_ty bool_ty))
  in
  let f_ty = make_fun_ty bool_ty (make_fun_ty bool_ty bool_ty) in
  let f = Var ("f", f_ty) in
  let t = make_true () in
  let f_p_q = App (App (f, p), q) in
  let f_t_t = App (App (f, t), t) in
  let lam_f_p_q = Lam (f, f_p_q) in
  let lam_f_t_t = Lam (f, f_t_t) in
  let* eq_lams = safe_make_eq lam_f_p_q lam_f_t_t in
  let rhs = Lam (p, Lam (q, eq_lams)) in
  let* def_eq = safe_make_eq conj_var rhs in
  new_basic_definition def_eq

let make_conj_const () =
  Const ("/\\", make_fun_ty bool_ty (make_fun_ty bool_ty bool_ty))

let make_conj p q = App (App (make_conj_const (), p), q)

let make_conjs = function
  | [] -> make_true ()
  | [ p ] -> p
  | p :: ps -> List.fold_left make_conj p ps

(* ==> = (λp q. p ∧ q ⟺ p) *)
let init_imp () =
  let p = Var ("p", bool_ty) in
  let q = Var ("q", bool_ty) in
  let imp_var =
    Var ("==>", make_fun_ty bool_ty (make_fun_ty bool_ty bool_ty))
  in
  let p_and_q = make_conj p q in
  let* p_and_q_eq_p = safe_make_eq p_and_q p in
  let rhs = Lam (p, Lam (q, p_and_q_eq_p)) in
  let* def_eq = safe_make_eq imp_var rhs in
  new_basic_definition def_eq

let make_imp_const () =
  Const ("==>", make_fun_ty bool_ty (make_fun_ty bool_ty bool_ty))

let make_imp p q = App (App (make_imp_const (), p), q)

let make_imps antecedents consequent =
  List.fold_right make_imp antecedents consequent

(* F = (∀p. p) *)
let init_false () =
  let p = Var ("p", bool_ty) in
  let f_var = Var ("F", bool_ty) in
  let forall_p_p = make_forall p p in
  let* def_eq = safe_make_eq f_var forall_p_p in
  new_basic_definition def_eq

let make_false () = Const ("F", bool_ty)

(* ¬ = (λp. p ==> F) *)
let init_neg () =
  let p = Var ("p", bool_ty) in
  let neg_var = Var ("~", make_fun_ty bool_ty bool_ty) in
  let f = make_false () in
  let p_imp_f = make_imp p f in
  let rhs = Lam (p, p_imp_f) in
  let* def_eq = safe_make_eq neg_var rhs in
  new_basic_definition def_eq

let make_neg_const () = Const ("~", make_fun_ty bool_ty bool_ty)
let make_neg p = App (make_neg_const (), p)

(* ∃ = (λP. ¬(∀x. ¬(P x))) *)
let init_exists () =
  let a = TyVar "a" in
  let pred_ty = make_fun_ty a bool_ty in
  let exists_ty = make_fun_ty pred_ty bool_ty in
  let exists_var = Var ("?", exists_ty) in
  let p_var = Var ("P", pred_ty) in
  let x_var = Var ("x", a) in
  let p_x = App (p_var, x_var) in
  let not_p_x = make_neg p_x in
  let forall_not_p = make_forall x_var not_p_x in
  let not_forall_not_p = make_neg forall_not_p in
  let rhs = Lam (p_var, not_forall_not_p) in
  let* def_eq = safe_make_eq exists_var rhs in
  new_basic_definition def_eq

let make_exists_const var_ty =
  let pred_ty = make_fun_ty var_ty bool_ty in
  let exists_ty = make_fun_ty pred_ty bool_ty in
  Const ("?", exists_ty)

let make_exists var body =
  let var_ty = type_of_var var in
  App (make_exists_const var_ty, Lam (var, body))

(* ∨ = (λp q. ∀r. (p ==> r) ==> (q ==> r) ==> r) *)
let init_disj () =
  let p = Var ("p", bool_ty) in
  let q = Var ("q", bool_ty) in
  let r = Var ("r", bool_ty) in
  let disj_var =
    Var ("\\/", make_fun_ty bool_ty (make_fun_ty bool_ty bool_ty))
  in
  let p_imp_r = make_imp p r in
  let q_imp_r = make_imp q r in
  let body = make_imp p_imp_r (make_imp q_imp_r r) in
  let forall_r = make_forall r body in
  let rhs = Lam (p, Lam (q, forall_r)) in
  let* def_eq = safe_make_eq disj_var rhs in
  new_basic_definition def_eq

let make_disj_const () =
  Const ("\\/", make_fun_ty bool_ty (make_fun_ty bool_ty bool_ty))

let make_disj p q = App (App (make_disj_const (), p), q)

let make_neq l r =
  match safe_make_eq l r with Ok eq -> Ok (make_neg eq) | Error e -> Error e

(* ∀p. p /\ ¬p  *)
let init_classical () =
  let p = Var ("p", bool_ty) in
  let excl_middle = make_forall p (make_disj p (make_neg p)) in
  new_axiom excl_middle

let _ = init_types ()
(** [T = ((λp:bool. p) = (λp. p))] *)
let true_def = init_true ()
(** [∀ = (λP. P = (λx. T))] *)
let forall_def = init_forall ()
(** [∧ = (λp q. (λf. f p q) = (λf. f T T))] *)
let conj_def = init_conj ()
(** [==> = (λp q. p ∧ q ⟺ p)] *)
let imp_def = init_imp ()
(** [F = (∀p. p)] *)
let false_def = init_false ()
(** [¬ = (λp. p ==> F)] *)
let neg_def = init_neg ()
(** [∃ = (λP. ¬(∀x. ¬(P x)))] *)
let exists_def = init_exists ()
(** [∨ = (λp q. ∀r. (p ==> r) ==> (q ==> r) ==> r)] *)
let disj_def = init_disj ()
(** [∀p. p /\ ¬p] *)
let classical_def = init_classical ()

let term_of_negation = function
    | App (Const ("~", _), t ) -> t
    | _ -> failwith "todo"

let quantifier_of_forall = function
    | App (Const ("!", _), Lam (bind, _) ) -> bind
    | _ -> failwith "todo"

type side = Left  | Right
let side_of_op op side = function
  | App (App (Const (oper, _), p), q) when oper = op -> 
          (match side with
            | Left -> p
            | Right -> q)
  | _ -> failwith ("TODO: Not a " ^ op)

(** obtain [p] from [p /\ q]*)
let conj_left_term = Left |> side_of_op "/\\"

(** obtain [q] from [p /\ q]*)
let conj_right_term = Right |> side_of_op "/\\"

(** obtain [p] from [p \/ q]*)
let disj_left_term = Left |> side_of_op "\\/"

(** obtain [q] from [p \/ q]*)
let disj_right_term = Right |> side_of_op "\\/"

(** obtain [p] from [p ==> q]*)
let imp_left_term = Left |> side_of_op "==>"

(** obtain [q] from [p ==> q]*)
let imp_right_term = Right |> side_of_op "==>"

let ap_term tm th =
  let* rth = refl tm in
  mk_comb rth th

let ap_thm th tm =
  let* term_rfl = refl tm in
  mk_comb th term_rfl

  (* [|- x = y] should derive [|- y = x] *)
let sym th =
  let tm = concl th in
  let* l, _ = destruct_eq tm in
  let* lth = refl l in
  let* r = rator tm in
  let* rr = rator r in
  let* applied = ap_term rr th in
  let* comb = mk_comb applied lth in
  eq_mp comb lth

(** [λp. p = λp. p] is truth *)
(* T is already defined, just build up the identity reflection and use eq_mp to get T *)
let truth =
  let thm =
    let p = Var ("p", bool_ty) in
    let id_fun = Lam (p, p) in
    let* id_fun_refl = refl id_fun in
    let* t_def = true_def in
    let* t_def_sym = sym t_def in
    eq_mp t_def_sym id_fun_refl
  in
  make_exn thm

(** [|- p] should derive [|- p = T] *)
let eq_truth_intro thm = deduct_antisym_rule thm truth

(** [|- p = T] should derive [|- p] *)
let eq_truth_elim th =
  let* thm_sym = sym th in
  eq_mp thm_sym truth

(* try to apply beta, then get binder from f, instantiate it with the arg f is applied to and beta that *)

(** [|- (λx. x /\ x) arg] should derive [|- arg /\ arg] *)
let beta_conv tm =
  match beta tm with
  | Ok reduced -> Ok reduced
  | Error _ ->
      let* f, arg = destruct_app tm in
      let* v, _ = destruct_lam f in
      let* reduced = beta (App (f, v)) in
      let* instantiated_body = inst [ (arg, v) ] reduced in
      Ok instantiated_body

let rhs th =
  let* _, r = destruct_eq (concl th) in
  Ok r

let lhs th =
  let* l, _ = destruct_eq (concl th) in
  Ok l

(** recursively apply beta conversions *)
let rec deep_beta tm =
  match tm with
  | Var _ | Const _ -> refl tm
  | App (f, x) -> (
      let* f_th = deep_beta f in
      let* x_th = deep_beta x in
      let* app_th = mk_comb f_th x_th in
      let* reduced_tm = rhs app_th in
      let* f', _ = destruct_app reduced_tm in
      match f' with
      | Lam _ ->
          let* beta_th = beta_conv reduced_tm in
          let* combined = trans app_th beta_th in
          let* result_tm = rhs combined in
          let* final_th = deep_beta result_tm in
          trans combined final_th
      | _ -> Ok app_th)
  | Lam (v, body) ->
      let* body_th = deep_beta body in
      lam v body_th

(** obtain equality after applying a conversion to the left side *)
let conv_left conv th =
  let c = concl th in
  let* l, _r = destruct_eq c in
  let* convd = conv l in
  let* rev_convd = sym convd in
  trans rev_convd th

(** obtain equality after applying a conversion to the right side *)
let conv_right conv th =
  let c = concl th in
  let* _l, r = destruct_eq c in
  let* convd = conv r in
  trans th convd

(** obtain equality after applying a converion to both sides *)
let conv_equality conv th =
  let* left_reduced = conv_left conv th in
  let* right_reduced = conv_right conv th in
  let* rev_th = sym th in
  let* l'_eq_r = trans left_reduced rev_th in
  let* l'_eq_r' = trans l'_eq_r right_reduced in
  Ok l'_eq_r'

(* not sure how general this is, but useful for now *)
let unfold_definition def args =
  let apply_and_beta th arg =
    let* applied = ap_thm th arg in
    let* lhs_tm = lhs applied in
    let* beta_th = beta_conv lhs_tm in
    let* rev_beta = sym beta_th in
    trans rev_beta applied
  in
  let* rev_def = sym def in
  fold_left_result apply_and_beta rev_def args

(** [|- p, |- q] should derive [|- p /\ q] *)
let conj thl thr =
  let bool_to_bool = make_fun_ty bool_ty bool_ty in
  let bool_to_bool_to_bool = make_fun_ty bool_ty bool_to_bool in
  let f = make_var "f" bool_to_bool_to_bool in
  (* build up the definition of conjunction from out terms *)
  let* f_refl = refl f in
  let* l_eqt = eq_truth_intro thl in
  let* r_eqt = eq_truth_intro thr in
  let* l_thm1 = mk_comb f_refl l_eqt in
  let* l_thm2 = mk_comb l_thm1 r_eqt in
  let* conj_def = conj_def in
  let* body = lam f l_thm2 in
  (* Need to apply and reduce *)
  let* conj_applied = unfold_definition conj_def [ concl thl; concl thr ] in
  eq_mp conj_applied body

let conj_lr selector th =
  let thl = conj_left_term (concl th) in
  let thr = conj_right_term (concl th) in
  let* conj_def = conj_def in
  let* unfolded_conj = unfold_definition conj_def [ thl; thr ] in
  let* rev_unfolded_conj = sym unfolded_conj in
  let* def = eq_mp rev_unfolded_conj th in
  let* applied = ap_thm def selector in

  let* reduced = conv_equality deep_beta applied in
  let* eq_elim = eq_truth_elim reduced in
  Ok eq_elim

(** [|- p /\ q] should derive [|- p] *)
let conj_left th =
  let* select_fst  =
    let x = make_var "x" bool_ty in
    let y = make_var "y" bool_ty in
    let* inner = make_lam y x in
    make_lam x inner
    (* λx y. x *)
  in
    conj_lr select_fst th

(* [|- p /\ q] should derive [|- q] *)
let conj_right th =
  let* select_snd  =
    let x = make_var "x" bool_ty in
    let y = make_var "y" bool_ty in
    let* inner = make_lam y y in
    make_lam x inner
    (* λx y. y *)
  in
  conj_lr select_snd th

  (** [|- p => q] should derive [{p} |- q]*)
let undisch th = 
    let l_tm = imp_left_term (concl th) in
    let r_tm = imp_right_term (concl th) in
    let* assm_l = assume l_tm in

    let* imp_def = imp_def in
    let* imp_applied = unfold_definition imp_def [l_tm; r_tm] in
    let* rev_imp_applied = sym imp_applied in

    let* l_imp_r_dest = eq_mp rev_imp_applied th in
    let* rev_l_imp_r_dest = sym l_imp_r_dest in
    let* replaced_p = eq_mp rev_l_imp_r_dest assm_l in
    conj_right replaced_p

(** [{p} |- q] should derive [|- p => q]*)
let disch tm th = 
    let* assm_conj = assume (make_conj tm (concl th)) in 
    let* assm_conj_left = conj_left assm_conj in         
    let* assm_tm = assume tm in 
    let* assm_and_th = conj assm_tm th in

    let* imp_def = imp_def in
    let* eq_th = deduct_antisym_rule assm_conj_left assm_and_th in
    let* rev_eq_th = sym eq_th in
    let* imp_unfolded = unfold_definition imp_def [tm; (concl th)] in 
    let* result = eq_mp imp_unfolded rev_eq_th in
    Ok result

let prove_hyp thl thr = 
    let* antisym = (deduct_antisym_rule thl thr) in
    eq_mp antisym thl

(** [|- p => q, |- p] should derive [|- q] *)
let mp th_imp th = 
    let* q_under_p = undisch th_imp in
    prove_hyp th q_under_p

(** [|- x = x] should derive [|- ∀x. x = x] when x is not free in hypotheses *)
let gen tm th = 
    (* don't necessarily need to check hyps, kernel should catch this 
       either way when the lambda rule is run *)
    let* forall_def = forall_def in
    let var_typ = type_of_var tm in
    let* pred_lam = make_lam tm (concl th) in
    let* typed_forall = inst_type ([(make_vartype "a", var_typ)] |> List.to_seq |> Hashtbl.of_seq) forall_def in
    let* eqt_th = eq_truth_intro th in
    let* eqt_lam = lam (tm) eqt_th in
    let* forall_applied = unfold_definition typed_forall [pred_lam] in
    eq_mp forall_applied eqt_lam

(** [|- ∀x. x = x] should derive [|- t = t] for any term t  *)
let spec tm th = 
    let* forall_def = forall_def in
    let quant_over = quantifier_of_forall (concl th) in
    let quant_typ = type_of_var quant_over in
    let* typed_forall = inst_type ([(make_vartype "a", quant_typ)] |> List.to_seq |> Hashtbl.of_seq) forall_def in
    let* _, pred_lam = destruct_app (concl th) in
    let* forall_applied = unfold_definition typed_forall [pred_lam] in
    let* rev_app = sym forall_applied in
    let* inner = eq_mp rev_app th in
    let* with_t = ap_thm inner tm in
    let* redux = conv_equality deep_beta with_t in
    eq_truth_elim redux

(** [⊢ P] should derive [⊢ P ∨ Q] *)
let disj_left tm th = 
    let c = concl th in
    let* disj_def = disj_def in

    let* applied = unfold_definition disj_def [c; tm] in

    let r = make_var "r" bool_ty in
    
    let* r_assumed = assume (make_imp (concl th) r) in

    let* r_th = mp r_assumed th in
    let* tm_disch = disch (make_imp tm r) r_th in
    let* th_disch = disch (make_imp c r) tm_disch in

    let* gen_th = gen r th_disch in

    eq_mp applied gen_th

(** [⊢ Q] should derive [⊢ P ∨ Q] *)
let disj_right th tm = 
    let c = concl th in
    let* disj_def = disj_def in

    let* applied = unfold_definition disj_def [tm; c] in

    let r = make_var "r" bool_ty in
    
    let* r_assumed = assume (make_imp (concl th) r) in

    let* r_th = mp r_assumed th in
    let* th_disch = disch (make_imp c r) r_th in
    let* tm_disch = disch (make_imp tm r) th_disch in

    let* gen_th = gen r tm_disch in
    eq_mp applied gen_th

(** [⊢ P ∨ Q], [{P} ⊢ R], [{Q} ⊢ R] should derive [⊢ R] *)
let disj_cases pq_th pr_th qr_th = 
    let* disj_def = disj_def in
    let p = disj_left_term (concl pq_th) in
    let q = disj_right_term (concl pq_th) in

    let* applied = unfold_definition disj_def [p; q] in
    let* applied_rev = sym applied in
    let* unfolded = eq_mp applied_rev pq_th in

    let* p_imp_r = disch p pr_th in
    let* q_imp_r = disch q qr_th in

    let* specced = spec (concl pr_th) unfolded in
    let* mp1 = mp specced p_imp_r in
    mp mp1 q_imp_r

(** [⊢ ¬P] should derive [{P} ⊢ F] *)
let not_elim th = 
    let* neg_def = neg_def in
    let negated_term = term_of_negation (concl th) in

    let* applied = unfold_definition neg_def [negated_term] in
    let* applied_rev = sym applied in

    let* mp1 = eq_mp applied_rev th in
    undisch mp1

(** [{P} ⊢ F] should derive [⊢ ¬P] *)
let not_intro tm th = 
    let* disch_tm = disch tm th in
    let* neg_def = neg_def in
    let* applied = unfold_definition neg_def [tm] in
    eq_mp applied disch_tm

(** [⊢ F] should derive [⊢ P] (ex falso quodlibet) *)
let contr p th = 
    let* false_def = false_def in
    let* applied = eq_mp false_def th in
    spec p applied

(** [{¬P} ⊢ F] should derive [⊢ P] (classical contradiction) *)
let ccontr p th = 
    let* neg_def = neg_def in
    let neg_p = make_neg p in
    let* undis = disch neg_p th in

    let* applied = unfold_definition neg_def [neg_p] in
    let* double_neg = eq_mp applied undis in

    let* classical_def = classical_def in
    let* speccd = spec p classical_def in

    let* disj_p = assume p in
    let* disj_np = not_elim double_neg in
    let* disj_np_contr = contr p disj_np in

    disj_cases speccd disj_p disj_np_contr

(** [⊢ t = t] should derive [⊢ ∃x. x = x] *)
let exists x tm th =
    let* exists_def = exists_def in
    let* tm_typ = type_of_term tm in
    let* typed_exists_def = inst_type ([(make_vartype "a", tm_typ)] |> List.to_seq |> Hashtbl.of_seq) exists_def in
    
    let* pred_body = vsubst [(x, tm)] (concl th) in
    let* pred_lam = make_lam x pred_body in
    
    let* applied = unfold_definition typed_exists_def [pred_lam] in
    let* applied_normal = conv_equality deep_beta applied in
    
    let* l = lhs applied_normal in
    let inner_forall = term_of_negation l in
    
    let* assm_forall = assume inner_forall in
    let* speccd = spec tm assm_forall in
    let* false_th = not_elim speccd in
    
    let hyps = hyp false_th in
    let p_hyp = List.find (fun h -> alphaorder h inner_forall <> 0) hyps in
    
    let* p_hyp_refl = refl p_hyp in
    let* beta_th = conv_left deep_beta p_hyp_refl in  
    let* p_hyp_th = eq_mp beta_th th in
    
    let* false_th' = prove_hyp p_hyp_th false_th in
    let* neg_forall = not_intro inner_forall false_th' in
    eq_mp applied_normal neg_forall

(** [⊢ ∃x. P(x)], [{P(x)} ⊢ Q] should derive [⊢ Q] (where x not free in Q) *)
let choose x exists_th q_th = 
    let q = concl q_th in
    let x_ty = type_of_var x in
    
    let* _, pred_lam = destruct_app (concl exists_th) in
    
    let p_x_hyp = List.hd (hyp q_th) in
    
    let neg_q = make_neg q in
    let* neg_q_assumed = assume neg_q in
    let* neg_q_elim = not_elim neg_q_assumed in        
    let* false_with_px = prove_hyp q_th neg_q_elim in  
    let* neg_px = not_intro p_x_hyp false_with_px in   
    let* forall_neg_px = gen x neg_px in               
    
    let* exists_def = exists_def in
    let* typed_exists_def = inst_type ([(make_vartype "a", x_ty)] |> List.to_seq |> Hashtbl.of_seq) exists_def in
    let* unfolded = unfold_definition typed_exists_def [pred_lam] in
    let* unfolded_normal = conv_equality deep_beta unfolded in
    let* exists_as_neg = eq_mp (Result.get_ok (sym unfolded_normal)) exists_th in
    
    let* exists_contra = not_elim exists_as_neg in     
    
    let forall_hyp = List.hd (hyp exists_contra) in
    let* forall_refl = refl forall_hyp in
    let* forall_conv = conv_left deep_beta forall_refl in
    let* forall_neg_px_conv = eq_mp forall_conv forall_neg_px in
    
    let* false_from_neg_q = prove_hyp forall_neg_px_conv exists_contra in  
    ccontr q false_from_neg_q
