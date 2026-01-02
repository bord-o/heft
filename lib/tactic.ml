open Kernel
open Derived

type goal = term list * term [@@deriving show]
type _ Effect.t += Subgoals : goal list -> thm list Effect.t

let gconcl = snd

type tactic_name =
  | Assumption
  | Conj
  | Refl
  | Left
  | Right
  | Intro
  | Gen
  | Exists of term
  | EqTac  (* split P = Q into P ==> Q and Q ==> P *)
  | MpTac of thm  (* move theorem into goal as antecedent *)
  | MatchMpTac of thm  (* apply |- P ==> Q to goal Q, creating subgoal P *)
  | SpecTac of term * term  (* generalize goal: replace t with x, wrap in forall *)
  | Induct of term  (* induction on term t *)
  | Rewrite of thm  (* rewrite goal using equality theorem *)
  | RewriteWith of string  (* lookup theorem by name, then rewrite *)
  | RewriteAsm of int  (* rewrite using assumption by index *)
  | Beta  (* beta reduce the goal *)

type tactic = goal -> thm

(* Helper to convert Result to exception *)
exception Kernel_error of kernel_error

let unwrap_result = function Ok x -> x | Error e -> failwith (show_kernel_error e)

(** Collect type variable mappings needed to make pattern types match target types.
    Returns a list of (target_type, TyVar name) pairs. *)
let rec collect_type_subst pat_ty tgt_ty =
  match pat_ty, tgt_ty with
  | TyVar n, t -> [(t, TyVar n)]
  | TyCon (n1, args1), TyCon (n2, args2) when n1 = n2 && List.length args1 = List.length args2 ->
      List.concat (List.map2 collect_type_subst args1 args2)
  | _ -> []

(** Try to match a pattern term against a target term.
    Returns Some (term_subst, type_subst) if successful, None otherwise.
    The pattern may contain variables that get bound to subterms of target.
    type_subst maps pattern type variables to target types. *)
let rec term_match pattern target =
  match pattern, target with
  | Var (n1, ty1), Var (n2, ty2) when n1 = n2 ->
      (* Same variable name, just collect type substitution *)
      Some ([], collect_type_subst ty1 ty2)
  | Var (_, _), _ ->
      (* Pattern variable matches anything *)
      Some ([(target, pattern)], [])
  | Const (n1, ty1), Const (n2, ty2) when n1 = n2 ->
      (* Constants match if names are same, collect type substitution *)
      Some ([], collect_type_subst ty1 ty2)
  | App (f1, x1), App (f2, x2) ->
      (match term_match f1 f2 with
       | None -> None
       | Some (s1, ts1) ->
           match term_match x1 x2 with
           | None -> None
           | Some (s2, ts2) -> Some (s1 @ s2, ts1 @ ts2))
  | Lam (Var (n1, _), b1), Lam (Var (n2, _), b2) when n1 = n2 ->
      term_match b1 b2
  | _ -> None

(* Example tactics *)
let conj_tac (asms, concl) =
  let p, q = destruct_conj concl in
  match Effect.perform (Subgoals [ (asms, p); (asms, q) ]) with
  | [ p_thm; q_thm ] -> conj p_thm q_thm |> unwrap_result
  | _ -> failwith "expected both sides of conj"

let assumption_tac (asms, concl) =
  match List.find_opt (fun t -> alphaorder concl t = 0) asms with
  | Some asm -> assume asm |> unwrap_result
  | None -> failwith "no matching assumption"

let refl_tac : tactic =
 fun (_asms, concl) ->
  match destruct_eq concl with
  | Ok (l, r) when alphaorder l r = 0 -> refl l |> Result.get_ok
  | Ok (l, r) ->
      (* Try polymorphic match - sides might differ only in types *)
      (match term_match l r with
       | Some (term_subst, _ty_subst) when term_subst = [] ->
           (* Structurally identical, just type differences in subterms.
              This shouldn't happen if rewriting preserves type consistency.
              For now, fail clearly to help diagnose issues. *)
           print_endline @@ Printing.pretty_print_hol_term ~with_type:true l;
           print_endline @@ Printing.pretty_print_hol_term ~with_type:true r;
           failwith "REFL_TAC: goal has inconsistent internal types (l and r differ in subterm types)"
       | Some (term_subst, _) ->
           failwith ("REFL_TAC: sides of equality not identical (term_subst has " ^ string_of_int (List.length term_subst) ^ " entries)")
       | None ->
           failwith "REFL_TAC: sides of equality not identical (no match)")
  | Error _ -> failwith "REFL_TAC: goal not an equality"

let left_tac : tactic =
 fun (asms, concl) ->
  let l, r = destruct_disj concl in
  match Effect.perform (Subgoals [ (asms, l) ]) with
  | [ l_thm ] -> disj_left r l_thm |> Result.get_ok
  | _ -> failwith "expected single theorem"

let right_tac : tactic =
 fun (asms, concl) ->
  let l, r = destruct_disj concl in
  match Effect.perform (Subgoals [ (asms, r) ]) with
  | [ r_thm ] -> disj_right r_thm l |> Result.get_ok
  | _ -> failwith "expected single theorem"

(** Prove [P ==> Q] by assuming P and proving Q *)
let intro_tac : tactic =
 fun (asms, concl) ->
  let p = imp_left_term concl in
  let q = imp_right_term concl in
  match Effect.perform (Subgoals [ (p :: asms, q) ]) with
  | [ q_thm ] -> disch p q_thm |> unwrap_result
  | _ -> failwith "expected single theorem"

(** Prove [∀x. P x] by proving [P x] with x arbitrary *)
let gen_tac : tactic =
 fun (asms, concl) ->
  let x = quantifier_of_forall concl in
  let body = body_of_forall concl in
  match Effect.perform (Subgoals [ (asms, body) ]) with
  | [ body_thm ] -> gen x body_thm |> unwrap_result
  | _ -> failwith "expected single theorem"

(** Prove [∃x. P x] by providing a witness term *)
let exists_tac (witness : term) : tactic =
 fun (asms, concl) ->
  let x, body = destruct_exists concl in
  (* Substitute witness for x in the body *)
  let instantiated = vsubst [ (witness, x) ] body |> unwrap_result in
  match Effect.perform (Subgoals [ (asms, instantiated) ]) with
  | [ inst_thm ] -> exists x witness inst_thm |> unwrap_result
  | _ -> failwith "expected single theorem"

(** EQ_TAC: Prove [P = Q] by proving [P ==> Q] and [Q ==> P] *)
let eq_tac : tactic =
 fun (asms, goal_concl) ->
  let p, q = destruct_eq goal_concl |> unwrap_result in
  let p_imp_q = make_imp p q in
  let q_imp_p = make_imp q p in
  match Effect.perform (Subgoals [ (asms, p_imp_q); (asms, q_imp_p) ]) with
  | [ pq_thm; qp_thm ] ->
      (* From |- P ==> Q and |- Q ==> P, derive |- P = Q *)
      let p_thm = undisch pq_thm |> unwrap_result in  (* {P} |- Q *)
      let q_thm = undisch qp_thm |> unwrap_result in  (* {Q} |- P *)
      deduct_antisym_rule p_thm q_thm |> unwrap_result
  | _ -> failwith "EQ_TAC: expected two theorems"

(** MP_TAC thm: Move theorem's conclusion into goal as antecedent.
    Goal [w] becomes [(concl thm) ==> w] *)
let mp_tac (thm : thm) : tactic =
 fun (asms, goal_concl) ->
  let thm_concl = concl thm in
  let new_goal = make_imp thm_concl goal_concl in
  match Effect.perform (Subgoals [ (asms, new_goal) ]) with
  | [ imp_thm ] -> mp imp_thm thm |> unwrap_result
  | _ -> failwith "MP_TAC: expected single theorem"

(** MATCH_MP_TAC thm: Given [|- P ==> Q] and goal [Q], create subgoal [P].
    (Simple version without matching/instantiation) *)
let match_mp_tac (thm : thm) : tactic =
 fun (asms, goal_concl) ->
  let thm_concl = concl thm in
  let p = imp_left_term thm_concl in
  let q = imp_right_term thm_concl in
  if alphaorder q goal_concl <> 0 then
    failwith "MATCH_MP_TAC: theorem conclusion doesn't match goal"
  else
    match Effect.perform (Subgoals [ (asms, p) ]) with
    | [ p_thm ] -> mp thm p_thm |> unwrap_result
    | _ -> failwith "MATCH_MP_TAC: expected single theorem"

(** Replace all occurrences of [old_tm] with [new_tm] in [tm] *)
let rec term_subst old_tm new_tm tm =
  if alphaorder tm old_tm = 0 then new_tm
  else match tm with
    | Var _ | Const _ -> tm
    | App (f, a) -> App (term_subst old_tm new_tm f, term_subst old_tm new_tm a)
    | Lam (v, body) -> Lam (v, term_subst old_tm new_tm body)

(** SPEC_TAC (t, x): Generalize goal by replacing [t] with [x] and wrapping in forall.
    Goal [P[t]] becomes [∀x. P[x]] *)
let spec_tac (t : term) (x : term) : tactic =
 fun (asms, goal_concl) ->
  let generalized = term_subst t x goal_concl in
  let new_goal = make_forall x generalized in
  match Effect.perform (Subgoals [ (asms, new_goal) ]) with
  | [ forall_thm ] -> spec t forall_thm |> unwrap_result
  | _ -> failwith "SPEC_TAC: expected single theorem"

(** Get the type name from a hol_type *)
let type_name_of = function
  | TyCon (name, _) -> name
  | TyVar _ -> failwith "INDUCT: cannot induct on type variable"

(** Collect premises from a chain of implications: A -> B -> C -> D gives [A; B; C] and D *)
let rec collect_premises tm =
  match tm with
  | App (App (Const ("==>", _), left), right) ->
      let rest_premises, concl = collect_premises right in
      (left :: rest_premises, concl)
  | _ -> ([], tm)

(** INDUCT t: Perform structural induction on term t.
    For now, only works on the outermost forall-bound variable.
    Goal ∀v. body becomes subgoals for each case of the induction principle.
    The predicate is λv. body, which includes any inner foralls. *)
let induct_tac (t : term) : tactic =
 fun (asms, goal_concl) ->
  (* Get the type of the term we're inducting on *)
  let t_ty = type_of_term t |> unwrap_result in
  let ty_name = type_name_of t_ty in

  (* Look up the inductive definition *)
  let ind_def = match Hashtbl.find_opt the_inductives ty_name with
    | Some def -> def
    | None -> failwith ("INDUCT: no inductive definition for type " ^ ty_name)
  in

  (* Get the induction theorem: ∀P. premise1 → ... → ∀x. P x *)
  let ind_thm = ind_def.induction in

  (* Build predicate based on whether goal is a forall over t or t is free *)
  let pred, is_forall_case = match goal_concl with
    | App (Const ("!", _), Lam (bound_v, body))
      when alphaorder t bound_v = 0 ->
        (* Goal is ∀t. body - induct on the outermost forall *)
        (* Predicate is λt. body (body may contain more foralls, that's fine) *)
        (Lam (bound_v, body), true)
    | _ ->
        (* t is a free variable in the goal - abstract over it *)
        (Lam (t, goal_concl), false)
  in

  (* Specialize the induction theorem with our predicate *)
  let spec_thm = spec pred ind_thm |> unwrap_result in

  (* The specialized theorem has the form: premise1 → premise2 → ... → ∀x. pred x *)
  let spec_concl = concl spec_thm in
  let premises, _final_concl = collect_premises spec_concl in

  (* Beta-reduce each premise to get the actual goals *)
  let reduce_premise p =
    let beta_thm = deep_beta p |> unwrap_result in
    rhs beta_thm |> unwrap_result
  in
  let subgoal_terms = List.map reduce_premise premises in

  (* Create subgoals with the same assumptions *)
  let subgoals : goal list = List.map (fun g -> (asms, g)) subgoal_terms in

  match Effect.perform (Subgoals subgoals) with
  | thms ->
      (* We have proofs of all the premises.
         Apply MP repeatedly to get the conclusion. *)
      let combined = List.fold_left (fun acc_thm premise_thm ->
        mp acc_thm premise_thm |> unwrap_result
      ) spec_thm thms in
      (* combined now proves ∀x. pred x = ∀x. (λt. body) x *)

      (* Beta-reduce: ∀x. (λt. body) x  =>  ∀x. body[x/t] *)
      let combined_concl = concl combined in
      let beta_thm = deep_beta combined_concl |> unwrap_result in
      let reduced = eq_mp beta_thm combined |> unwrap_result in

      if is_forall_case then
        (* reduced proves ∀x. body where x is the induction theorem's variable.
           We want ∀t. body where t is from our goal. Rename by spec then gen. *)
        let spec_result = spec t reduced |> unwrap_result in
        let spec_concl = concl spec_result in
        let spec_beta = deep_beta spec_concl |> unwrap_result in
        let body_thm = eq_mp spec_beta spec_result |> unwrap_result in
        gen t body_thm |> unwrap_result
      else
        (* For free variable case: spec to remove forall and get back the goal *)
        let spec_result = spec t reduced |> unwrap_result in
        let spec_concl = concl spec_result in
        let spec_beta = deep_beta spec_concl |> unwrap_result in
        eq_mp spec_beta spec_result |> unwrap_result

(** Extract rewrite rules from a theorem, handling conjunctions.
    Keeps foralls intact - they will be instantiated during matching.
    Returns a list of theorems (possibly forall-wrapped equalities). *)
let rec extract_rewrite_rules thm =
  let c = concl thm in
  (* Check if it's a conjunction *)
  match destruct_conj c with
  | (_, _) ->
      let left_thm = conj_left thm |> unwrap_result in
      let right_thm = conj_right thm |> unwrap_result in
      extract_rewrite_rules left_thm @ extract_rewrite_rules right_thm
  | exception _ -> [thm]

(** Strip foralls from a theorem while matching against a target term.
    Returns the instantiated theorem and remaining LHS to match. *)
let rec instantiate_foralls thm target =
  let c = concl thm in
  match c with
  | App (Const ("!", _), Lam (v, body)) ->
      (* Find what the variable should be instantiated to by looking at target structure *)
      (* First, figure out the LHS pattern after stripping this forall *)
      let rec get_lhs_pattern tm =
        match tm with
        | App (Const ("!", _), Lam (_, inner)) -> get_lhs_pattern inner
        | _ -> match destruct_eq tm with
               | Ok (l, _) -> Some l
               | Error _ -> None
      in
      (match get_lhs_pattern body with
       | None -> None
       | Some pattern ->
           (* Try to match pattern against target to find instantiation for v *)
           match term_match pattern target with
           | None -> None
           | Some (subst, ty_subst) ->
               (* Apply type substitution to theorem first *)
               let ty_tbl = Hashtbl.create (List.length ty_subst) in
               List.iter (fun (tgt, src) -> Hashtbl.replace ty_tbl src tgt) ty_subst;
               let thm' = inst_type ty_tbl thm |> unwrap_result in
               (* Find what v maps to in the substitution (v is already a term) *)
               match List.find_opt (fun (_, pat) -> alphaorder pat v = 0) subst with
               | Some (inst, _) ->
                   let spec_thm = spec inst thm' |> unwrap_result in
                   instantiate_foralls spec_thm target
               | None ->
                   (* v doesn't appear in pattern, just use v itself - also need type-instantiated v *)
                   let v' = match v with
                     | Var (name, ty) -> Var (name, type_substitution ty_tbl ty)
                     | _ -> v
                   in
                   let spec_thm = spec v' thm' |> unwrap_result in
                   instantiate_foralls spec_thm target)
  | _ ->
      (* No more foralls, return the theorem *)
      Some thm

(** Try to match any rule at this position.
    Returns Some (instantiated equality theorem, type_subst) if a rule matches, None otherwise.
    The type_subst is returned so callers can accumulate a global substitution. *)
let try_match_rules rules tm =
  let rec try_rules = function
    | [] -> None
    | rule :: rest ->
        match instantiate_foralls rule tm with
        | Some inst_thm ->
            let l = lhs inst_thm |> unwrap_result in
            (* Use term_match for type-polymorphic comparison and get type substitution *)
            (match term_match l tm with
             | Some (_term_subst, ty_subst) ->
                 (* Convert list to hashtable and apply type substitution *)
                 let ty_tbl = Hashtbl.create (List.length ty_subst) in
                 List.iter (fun (tgt, src) -> Hashtbl.replace ty_tbl src tgt) ty_subst;
                 let inst_thm' = inst_type ty_tbl inst_thm |> unwrap_result in
                 Some (inst_thm', ty_subst)
             | None -> try_rules rest)
        | None -> try_rules rest
  in
  try_rules rules

(** Compare two hol_types for equality *)
let rec ty_eq t1 t2 =
  match t1, t2 with
  | TyVar n1, TyVar n2 -> n1 = n2
  | TyCon (n1, args1), TyCon (n2, args2) ->
      n1 = n2 && List.length args1 = List.length args2
      && List.for_all2 ty_eq args1 args2
  | _ -> false

(** Merge type substitution lists, preferring earlier bindings for the same var *)
let merge_ty_subst s1 s2 =
  let existing_vars = List.map snd s1 in
  let new_bindings = List.filter (fun (_, v) -> not (List.exists (fun v' -> ty_eq v v') existing_vars)) s2 in
  s1 @ new_bindings

(** Apply a type substitution to a term *)
let apply_ty_subst_to_term ty_subst tm =
  if ty_subst = [] then tm
  else
    let ty_tbl = Hashtbl.create (List.length ty_subst) in
    List.iter (fun (tgt, src) -> Hashtbl.replace ty_tbl src tgt) ty_subst;
    let rec go = function
      | Var (n, ty) -> Var (n, type_substitution ty_tbl ty)
      | Const (n, ty) -> Const (n, type_substitution ty_tbl ty)
      | App (f, x) -> App (go f, go x)
      | Lam (v, body) -> Lam (go v, go body)
    in
    go tm

(** Rewrite a term using a list of rewrite rules.
    Returns (thm, changed, ty_subst) where:
    - thm is |- tm = tm' with occurrences of l replaced by r
    - changed indicates if any rewriting occurred
    - ty_subst accumulates all type instantiations made during rewriting *)
let rec rewrite_term_acc rules ty_subst tm =
  (* Apply accumulated type substitution to term before matching *)
  let tm' = apply_ty_subst_to_term ty_subst tm in
  (* Try to match any rule at this position *)
  match try_match_rules rules tm' with
  | Some (eq_thm, new_ty_subst) ->
      let combined_subst = merge_ty_subst ty_subst new_ty_subst in
      (eq_thm, true, combined_subst)
  | None ->
      match tm' with
      | Var _ | Const _ ->
          (* No match, return reflexivity *)
          (refl tm' |> unwrap_result, false, ty_subst)
      | App (f, x) ->
          let f_thm, f_changed, ty_subst' = rewrite_term_acc rules ty_subst f in
          let x_thm, x_changed, ty_subst'' = rewrite_term_acc rules ty_subst' x in
          if f_changed || x_changed then
            (mk_comb f_thm x_thm |> unwrap_result, true, ty_subst'')
          else
            (refl tm' |> unwrap_result, false, ty_subst'')
      | Lam (v, body) ->
          let body_thm, changed, ty_subst' = rewrite_term_acc rules ty_subst body in
          if changed then
            (lam v body_thm |> unwrap_result, true, ty_subst')
          else
            (refl tm' |> unwrap_result, false, ty_subst')

(** Rewrite a term using a list of rewrite rules.
    Returns |- tm = tm' where tm' has occurrences of l replaced by r,
    along with a boolean indicating if any rewriting occurred. *)
let rewrite_term rules tm =
  let thm, changed, _ty_subst = rewrite_term_acc rules [] tm in
  (thm, changed)

(** Rewrite a term using all rewrite rules extracted from a theorem *)
let rewrite_term_with_thm thm tm =
  let rules = extract_rewrite_rules thm in
  rewrite_term rules tm

(** Lookup a theorem by name from specifications or definitions *)
let lookup_theorem name =
  match Hashtbl.find_opt the_specifications name with
  | Some thm -> Some thm
  | None ->
      (* Search definitions for one whose LHS constant matches the name *)
      !the_definitions |> List.find_opt (fun thm ->
        match lhs thm with
        | Ok (Const (n, _)) -> n = name
        | Ok (Var (n, _)) -> n = name
        | _ -> false)

(** REWRITE thm: Rewrite the goal using equality theorem.
    Handles conjunctions of equalities and foralls. *)
let rewrite_tac (eq_thm : thm) : tactic =
 fun (asms, goal_concl) ->
  let rw_thm, changed = rewrite_term_with_thm eq_thm goal_concl in
  if not changed then
    failwith "REWRITE: no matching subterm found"
  else
    let new_goal = rhs rw_thm |> unwrap_result in
    match Effect.perform (Subgoals [ (asms, new_goal) ]) with
    | [ new_thm ] ->
        (* We have |- new_goal, and rw_thm is |- goal = new_goal *)
        (* Use sym and eq_mp to get |- goal *)
        let rw_thm_sym = sym rw_thm |> unwrap_result in
        eq_mp rw_thm_sym new_thm |> unwrap_result
    | _ -> failwith "REWRITE: expected single theorem"

(** REWRITE_WITH name: Lookup theorem by name, then rewrite *)
let rewrite_with_tac (name : string) : tactic =
 fun goal ->
  match lookup_theorem name with
  | Some thm -> rewrite_tac thm goal
  | None -> failwith ("REWRITE_WITH: theorem not found: " ^ name)

(** REWRITE_ASM n: Rewrite using assumption at index n *)
let rewrite_asm_tac (n : int) : tactic =
 fun (asms, goal_concl) ->
  if n < 0 || n >= List.length asms then
    failwith ("REWRITE_ASM: invalid assumption index " ^ string_of_int n)
  else
    let asm_tm = List.nth asms n in
    let asm_thm = assume asm_tm |> unwrap_result in
    rewrite_tac asm_thm (asms, goal_concl)

(** BETA: Beta reduce the goal *)
let beta_tac : tactic =
 fun (asms, goal_concl) ->
  let beta_thm = deep_beta goal_concl |> unwrap_result in
  let reduced = rhs beta_thm |> unwrap_result in
  if alphaorder goal_concl reduced = 0 then
    failwith "BETA: no beta redexes found"
  else
    match Effect.perform (Subgoals [ (asms, reduced) ]) with
    | [ reduced_thm ] ->
        let beta_sym = sym beta_thm |> unwrap_result in
        eq_mp beta_sym reduced_thm |> unwrap_result
    | _ -> failwith "BETA: expected single theorem"

let name_of_tactic = function
  | Assumption -> "assumption"
  | Conj -> "conj"
  | Refl -> "refl"
  | Left -> "left"
  | Right -> "right"
  | Intro -> "intro"
  | Gen -> "gen"
  | Exists _ -> "exists"
  | EqTac -> "eq_tac"
  | MpTac _ -> "mp_tac"
  | MatchMpTac _ -> "match_mp_tac"
  | SpecTac _ -> "spec_tac"
  | Induct _ -> "induct"
  | Rewrite _ -> "rewrite"
  | RewriteWith name -> "rewrite " ^ name
  | RewriteAsm n -> "rewrite_asm " ^ string_of_int n
  | Beta -> "beta"

let get_tactic = function
  | Assumption -> assumption_tac
  | Conj -> conj_tac
  | Refl -> refl_tac
  | Left -> left_tac
  | Right -> right_tac
  | Intro -> intro_tac
  | Gen -> gen_tac
  | Exists witness -> exists_tac witness
  | EqTac -> eq_tac
  | MpTac thm -> mp_tac thm
  | MatchMpTac thm -> match_mp_tac thm
  | SpecTac (t, x) -> spec_tac t x
  | Induct t -> induct_tac t
  | Rewrite thm -> rewrite_tac thm
  | RewriteWith name -> rewrite_with_tac name
  | RewriteAsm n -> rewrite_asm_tac n
  | Beta -> beta_tac
