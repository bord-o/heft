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

type tactic = goal -> thm

(* Helper to convert Result to exception *)
exception Kernel_error of kernel_error

let unwrap_result = function Ok x -> x | Error e -> failwith (show_kernel_error e)

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
  | Ok _ -> failwith "REFL_TAC: sides of equality not identical"
  | Error _ -> failwith "REFL_TAC: goal not an equalit"

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
