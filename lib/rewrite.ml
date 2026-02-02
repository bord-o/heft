open Kernel
open Result.Syntax
open Derived
(* BEWARE, AI code ahead: *)

let rec type_match (env : (hol_type * hol_type) list) ty_pat ty_target :
    (hol_type * hol_type) list option =
  match (ty_pat, ty_target) with
  | TyVar _, _ -> (
      match List.assoc_opt ty_pat env with
      | Some ty -> if ty = ty_target then Some env else None
      | None -> Some ((ty_pat, ty_target) :: env))
  | TyCon (name1, args1), TyCon (name2, args2) ->
      if name1 <> name2 || List.length args1 <> List.length args2 then None
      else
        List.fold_left2
          (fun acc a1 a2 ->
            match acc with None -> None | Some env' -> type_match env' a1 a2)
          (Some env) args1 args2
  | _ -> None

let rec type_subst (tysub : (hol_type * hol_type) list) ty =
  match ty with
  | TyVar _ -> (
      match List.assoc_opt ty tysub with Some ty' -> ty' | None -> ty)
  | TyCon (name, args) -> TyCon (name, List.map (type_subst tysub) args)

let rec term_type_subst (tysub : (hol_type * hol_type) list) tm =
  match tm with
  | Var (name, ty) -> Var (name, type_subst tysub ty)
  | Const (name, ty) -> Const (name, type_subst tysub ty)
  | App (f, x) -> App (term_type_subst tysub f, term_type_subst tysub x)
  | Lam (v, body) -> Lam (term_type_subst tysub v, term_type_subst tysub body)

type match_result = {
  term_sub : (term * term) list; (* pattern var -> target term *)
  type_sub : (hol_type * hol_type) list; (* pattern type var -> target type *)
}

let empty_match = { term_sub = []; type_sub = [] }

(*
   Term matching: find substitutions such that pattern[subs] = target

   context_vars: variables that appear in theorem hypotheses (must match exactly)
   bound: variables bound by enclosing lambdas (must match exactly)
   env: current match result being built
   pattern: the pattern term
   target: the target term

   Returns None if no match, Some result if match found.

   Based on HOL Light's term_match.
*)
let rec term_match (context_vars : term list) (bound : term list) (env : match_result) (pattern : term)
    (target : term) : match_result option =
  match (pattern, target) with
  (* Bound variables (from lambdas) must match exactly *)
  | Var (_, _), _ when List.exists (fun b -> alphaorder pattern b = 0) bound ->
      let pattern' = term_type_subst env.type_sub pattern in
      if alphaorder pattern' target = 0 then Some env else None
  (* Context variables (from hypotheses) must match exactly *)
  | Var (_, _), _ when List.exists (fun cv -> alphaorder pattern cv = 0) context_vars ->
      let pattern' = term_type_subst env.type_sub pattern in
      if alphaorder pattern' target = 0 then Some env else None
  (* Free variables (pattern variables) can match anything *)
  | Var (name, ty), _ -> (
      let target_ty =
        match type_of_term target with
        | Ok t -> t
        | Error _ -> failwith "term_match: target has no type"
      in
      match type_match env.type_sub ty target_ty with
      | None -> None
      | Some type_sub' -> (
          let pattern' = Var (name, type_subst type_sub' ty) in
          match List.assoc_opt pattern' env.term_sub with
          | Some existing ->
              if alphaorder existing target = 0 then
                Some { env with type_sub = type_sub' }
              else None
          | None ->
              Some
                {
                  term_sub = (pattern', target) :: env.term_sub;
                  type_sub = type_sub';
                }))
  | Const (name1, ty1), Const (name2, ty2) -> (
      if name1 <> name2 then None
      else
        match type_match env.type_sub ty1 ty2 with
        | None -> None
        | Some type_sub' -> Some { env with type_sub = type_sub' })
  | App (f1, x1), App (f2, x2) -> (
      match term_match context_vars bound env f1 f2 with
      | None -> None
      | Some env' -> term_match context_vars bound env' x1 x2)
  | Lam ((Var (_, ty1) as v1), body1), Lam ((Var (_, ty2) as v2), body2) -> (
      match type_match env.type_sub ty1 ty2 with
      | None -> None
      | Some type_sub' -> (
          let env' = { env with type_sub = type_sub' } in
          let body1_typed = term_type_subst type_sub' body1 in
          let v1_typed = term_type_subst type_sub' v1 in
          match vsubst [ (v2, v1_typed) ] body1_typed with
          | Error _ -> None
          | Ok body1' -> term_match context_vars (v2 :: bound) env' body1' body2))
  | _, _ -> None

(* Get all free variables from a list of terms (the hypotheses) *)
let context_vars_of_hyps hyps =
  let rec frees_acc bound acc tm =
    match tm with
    | Var _ ->
        if List.exists (fun b -> alphaorder tm b = 0) bound then acc
        else if List.exists (fun v -> alphaorder tm v = 0) acc then acc
        else tm :: acc
    | Const _ -> acc
    | App (f, x) -> frees_acc bound (frees_acc bound acc f) x
    | Lam (v, body) -> frees_acc (v :: bound) acc body
  in
  List.fold_left (fun acc hyp -> frees_acc [] acc hyp) [] hyps

(* Convenience wrapper - no context variables *)
let match_term pattern target = term_match [] [] empty_match pattern target

(* Match with context from theorem hypotheses *)
let match_term_with_hyps hyps pattern target =
  let ctx_vars = context_vars_of_hyps hyps in
  term_match ctx_vars [] empty_match pattern target

(*


add 0 n = n
add (Suc m) n = Suc (add m n)

add 0 5

rw add
matches add 0 5 with the left side of add 0 n = n giving n->5
How do I now get a theorem when replace n with 5 giving add 0 5 = 5
What if add 0 n = n isn't explicitely quantified forall n?

use inst!

ok so moving forward:
    1. rewrite_exact_tac 
        handles when the goal exactly matches a rule
        uses choice to pick a rule
        need to handle theorem buliding
    2. rewrite_tac 
        uses choice among the possible rewrite locations
        need to look for possible matching subterms and build theorems
    3. simp_tac 
        repeats rewriting until failure

 *)

let rec subterms tm =
  tm
  ::
  (match tm with
  | Var _ | Const _ -> []
  | App (func, arg) -> subterms func @ subterms arg
  | Lam (_, bod) -> subterms bod)

(* does lhs of rule match any subterms of t? *)
let rec matches (rule : term) = function
  | [] -> []
  | tm :: tms -> (
      match match_term rule tm with
      | Some m -> m :: matches rule tms
      | None -> matches rule tms)

let subterm_matches (rule : thm) (tm : term) =
  let* rule_lhs, _ = destruct_eq (concl rule) in
  let subt = subterms tm in
  Ok (matches rule_lhs subt)

(*
  add (S m) n = S (add m n)

  add (add 1 2) 3 = 6

  when rewriting, what subterms do we get for lhs of goal?
    add (add 1 2) 3
    add 1 2
    3
    1
    2
  how do we know how to relate each of these back to the goal for thm construction?
  what are the other situations of inner rewrites to worry about?

*)

(* Instantiate a rewrite rule with a match result.
   Given rule: |- lhs = rhs and match_result from matching lhs against target,
   returns |- target = rhs[substituted] *)
let instantiate_rule (rule : thm) (env : match_result) =
  let* type_inst_rule = inst_type env.type_sub rule in
  (* inst expects (replacement, target_var), but match_result has (pattern_var, target_term) *)
  let term_sub_flipped = List.map (fun (v, t) -> (t, v)) env.term_sub in
  inst term_sub_flipped type_inst_rule

(* Try to rewrite tm at the root using rule.
   Returns Some (|- tm = tm') if lhs of rule matches tm, None otherwise.
   Variables that appear free in the rule's hypotheses must match exactly. *)
let rewrite_at_root (rule : thm) (tm : term) =
  let* rule_lhs, _ = destruct_eq (concl rule) in
  let hyps = hyp rule in
  match match_term_with_hyps hyps rule_lhs tm with
  | Some env ->
      let* inst_rule = instantiate_rule rule env in
      Ok (Some inst_rule)
  | None -> Ok None

(* Rewrite once somewhere in tm using rule.
   Tries root first, then recursively descends into subterms.
   Returns |- tm = tm' if successful. *)
let rec rewrite_once (rule : thm) (tm : term) =
  (* First, try to match at the root *)
  let* root_result = rewrite_at_root rule tm in
  match root_result with
  | Some thm -> Ok thm
  | None -> (
      (* Try subterms *)
      match tm with
      | Var _ | Const _ -> Error `NoRewriteMatch
      | App (f, x) -> (
          (* Try rewriting in function position first *)
          match rewrite_once rule f with
          | Ok f_eq ->
              (* f_eq : |- f = f', need |- f x = f' x *)
              ap_thm f_eq x
          | Error `NoRewriteMatch -> (
              (* Try rewriting in argument position *)
              match rewrite_once rule x with
              | Ok x_eq ->
                  (* x_eq : |- x = x', need |- f x = f x' *)
                  ap_term f x_eq
              | Error `NoRewriteMatch -> Error `NoRewriteMatch
              | Error e -> Error e)
          | Error e -> Error e)
      | Lam (v, body) -> (
          match rewrite_once rule body with
          | Ok body_eq ->
              (* body_eq : |- body = body', need |- λv.body = λv.body' *)
              lam v body_eq
          | Error e -> Error e))

(* Rewrite repeatedly until no more rewrites apply *)
let rec rewrite_all (rule : thm) (tm : term) =
  match rewrite_once rule tm with
  | Error `NoRewriteMatch ->
      refl tm (* No rewrite possible, return reflexivity *)
  | Error e -> Error e
  | Ok step_thm ->
      (* step_thm : |- tm = tm' *)
      let* _, tm' = destruct_eq (concl step_thm) in
      let* rest_thm = rewrite_all rule tm' in
      (* rest_thm : |- tm' = tm'' *)
      trans step_thm rest_thm

(* Rewrite using multiple rules, trying each in order until one works *)
let rec rewrite_once_with_rules (rules : thm list) (tm : term) =
  match rules with
  | [] -> Error `NoRewriteMatch
  | rule :: rest -> (
      match rewrite_once rule tm with
      | Ok thm -> Ok thm
      | Error `NoRewriteMatch -> rewrite_once_with_rules rest tm
      | Error e -> Error e)

(* Repeatedly rewrite using multiple rules until no more apply *)
let rec rewrite_all_with_rules (rules : thm list) (tm : term) =
  match rewrite_once_with_rules rules tm with
  | Error `NoRewriteMatch -> refl tm
  | Error e -> Error e
  | Ok step_thm ->
      let* _, tm' = destruct_eq (concl step_thm) in
      let* rest_thm = rewrite_all_with_rules rules tm' in
      trans step_thm rest_thm

(* Strip outer universal quantifiers from a theorem, leaving free variables
   that will be matched/instantiated during rewriting *)
let rec strip_forall thm =
  match destruct_forall (concl thm) with
  | Ok (var, _body) ->
      let* thm' = spec var thm in
      strip_forall thm'
  | Error _ -> Ok thm

(* Split a conjunction theorem into its components.
   Only splits at the top level - does not recurse into conjuncts.

   E.g., ⊢ A ∧ B ∧ C becomes [⊢ A; ⊢ B; ⊢ C]

   This is safe for recursive function definitions where each conjunct
   is a separate equation for one constructor case. *)
let rec split_conj_thm thm =
  match destruct_conj (concl thm) with
  | Ok _ ->
      (* It's a conjunction, split it *)
      let* left_thm = conj_left thm in
      let* right_thm = conj_right thm in
      (* Recurse on right side to handle A ∧ B ∧ C = A ∧ (B ∧ C) *)
      let* right_rules = split_conj_thm right_thm in
      Ok (left_thm :: right_rules)
  | Error _ ->
      (* Not a conjunction, this is a single rule *)
      Ok [ thm ]

(* Convert a recursive function definition theorem into a list of rewrite rules.
   Splits top-level conjunctions and strips foralls from each rule. *)
let rules_of_def thm =
  let* conjuncts = split_conj_thm thm in
  let strip_each thm = strip_forall thm in
  List.fold_right
    (fun th acc ->
      let* acc_list = acc in
      let* stripped = strip_each th in
      Ok (stripped :: acc_list))
    conjuncts (Ok [])
