open Kernel
open Derived
open Printing
open Effect
open Effect.Deep
open Result.Syntax
open Rewrite

type goal = term list * term [@@deriving show]
(** a list of assumptions and a term to prove under them *)

(** [level] is used to distinguish between different types of traces *)
type level = Debug | Info | Warn | Error | Proof | Search

(** [proof_state] is used by the ambient handler [prove] to represent the result
    of applying a tactic *)
type proof_state = Incomplete of goal | Complete of thm [@@deriving show]

type tactic = goal -> thm
(** a [tactic] is a function that works on a goal, possibly performing effects
*)

type tactic_combinator = tactic -> tactic
(** a [tactic_combinator] is a function between tactics. It has many uses like
    sequencing tactics ([then_one], [then_all]), handling specific effects
    ([with_no_trace], [with_fuel_limit]), or managing search over a tactics
    choices ([with_dfs], [with_best_first]. *)

type cost = Safe of int | Unsafe of int

type choice_kind =
  | CTerm of (goal * term)
  | CTheorem of goal * thm
  | CTactic of goal * cost * tactic
  | CUnknown of goal

(** [search_metadata] is used by [with_best_first] to sort a priority queue,
    deciding which path of a proof space to explore next *)
type search_metadata = MSubgoal of goal | MChoice of choice_kind | MResume

(** in search [tactic_combinator]s, [step_result] is used to represent possible
    continuations of a search *)
type step_result =
  | Cont of (choice_kind * (unit -> step_result)) list
  | Need of goal * (thm -> step_result)
  | Done of thm
  | Dead

module Priority = struct
  type t =
    search_metadata
    * (unit -> step_result)
    * (thm -> step_result) list
    * string list

  let compare : t -> t -> int =
   fun (a, _, _, _) (b, _, _, _) ->
    match (a, b) with
    | MSubgoal _, MResume -> 1
    | MSubgoal _, MChoice _ -> 1
    | MResume, MChoice _ -> 1
    | MChoice m1, MChoice m2 -> (
        match (m1, m2) with
        | CTactic (_, c1, _), CTactic (_, c2, _) -> (
            match (c1, c2) with
            | Safe _, Unsafe _ -> 1
            | Unsafe _, Safe _ -> -1
            | Safe n, Safe m -> compare m n
            | Unsafe n, Unsafe m -> compare m n)
        | _ -> 0)
    | m1, m2 when m1 = m2 -> 0
    | _ -> -1
end

module PriorityQueue = Pqueue.MakeMax (Priority)

module type Frontier = sig
  type t

  val create : unit -> t
  val pop : t -> Priority.t option
  val add : t -> Priority.t -> unit
  val stats : t -> string
end

(** the [rankable] GADT is used to allow both agnostic treatment of the [Rank]
    effect as well as deeper introspection into the underlying data when needed
*)
type _ rankable =
  | Term : term list -> term rankable
  | Goal : goal list -> goal rankable
  | Tactic : tactic list -> tactic rankable
  | Unknown : 'a list -> 'a rankable

(** the [choosable] GADT is used to allow both agnostic treatment of the
    [Choose] effect as well as deeper introspection into the underlying data
    when needed *)
type _ choosable =
  | Term : term list -> term choosable
  | Theorem : thm list -> thm choosable
  | Tactic : tactic list -> tactic choosable
  | Unknown : 'a list -> 'a choosable

exception Out_of_fuel
(** [Out_of_fuel] is performed by the [with_fuel_limit] [tactic_combinator] to
    indicate that a tactic has gone over its limit *)

type _ Effect.t +=
  | Subgoal : goal -> thm Effect.t
  | Choose : 'a choosable -> 'a Effect.t
  | Rank : 'a rankable -> 'a list Effect.t
  | Fail : 'a Effect.t
  | Trace : (level * string) -> unit Effect.t
  | Burn : (string * cost) -> unit Effect.t
  | Rules : thm list Effect.t

(** [as_ranked_list] extracts the underlying type from the [rankable] GADT *)
let as_ranked_list : type a. a rankable -> a list = function
  | Term ts -> ts
  | Goal gs -> gs
  | Tactic tacs -> tacs
  | Unknown xs -> xs

(** [as_chosen_list] extracts the underlying type from the [choosable] GADT *)
let as_chosen_list : type a. a choosable -> a list = function
  | Term ts -> ts
  | Theorem thms -> thms
  | Tactic tacs -> tacs
  | Unknown xs -> xs
(** [step] performs one expansion of the proof tree and aggregates the results
    along with their continuations *)

let cost_of_tactic (tac : tactic) (goal : goal) =
  match tac goal with
  | effect Burn (name, cost), _k -> (name, cost)
  | _ -> failwith "Burn must be first call of tactic"

let step (tac : tactic) (goal : goal) : step_result =
  match tac goal with
  | effect Choose cs, k ->
      let r = Multicont.Deep.promote k in
      let choosable =
        as_chosen_list cs |> List.map (fun c () -> Multicont.Deep.resume r c)
      in
      let real_choices =
        match cs with
        | Term ts ->
            List.combine (ts |> List.map @@ fun t -> CTerm (goal, t)) choosable
        | Theorem ts ->
            List.combine
              (ts |> List.map @@ fun t -> CTheorem (goal, t))
              choosable
        | Tactic ts ->
            List.combine
              (ts
              |> List.map @@ fun t ->
                 let _, cost = cost_of_tactic t goal in
                 CTactic (goal, cost, t))
              choosable
        | Unknown _ ->
            List.combine
              (List.init (List.length choosable) (fun _ -> CUnknown goal))
              choosable
      in
      Cont real_choices
  | effect Subgoal g, k ->
      let r = Multicont.Deep.promote k in
      Need (g, fun (v : thm) -> Multicont.Deep.resume r v)
  | effect Fail, _ -> Dead
  | v -> Done v

(** [fail] performs the [Fail] effect. This is used to signal when a tactic
    doesn't apply or doesn't make progress *)
let fail () = perform Fail

(** [burn] performs the [Burn] effect. This is used to signal the 'cost' of a
    tactic relative to other tactics *)
let burn name cost = perform (Burn (name, cost))

(** [trace_dbg] emits a debug-level trace message

    Effects: Trace *)
let trace_dbg a = perform (Trace (Debug, a))

(** [trace_info] emits an info-level trace message

    Effects: Trace *)
let trace_info a = perform (Trace (Info, a))

(** [trace_error] emits an error-level trace message

    Effects: Trace *)
let trace_error a = perform (Trace (Error, a))

(** [trace_proof] emits a proof-level trace message, used by tactics to record
    their name in the proof path

    Effects: Trace *)
let trace_proof a = perform (Trace (Proof, a))

(** [choose_terms] requests a choice among a list of terms

    Effects: Choose *)
let choose_terms gs = perform (Choose (Term gs))

(** [choose_theorems] requests a choice among a list of theorems

    Effects: Choose *)
let choose_theorems gs = perform (Choose (Theorem gs))

(** [choose_tactics] requests a choice among a list of tactics

    Effects: Choose *)
let choose_tactics gs = perform (Choose (Tactic gs))

(** [choose_unknowns] requests a choice among a list of unknown type

    Effects: Choose *)
let choose_unknowns gs = perform (Choose (Unknown gs))

(** [rank_terms] requests a ranking/sorting of terms by some heuristic

    Effects: Rank *)
let rank_terms ts = perform (Rank (Term ts))

(** [return_thm] is used by tactics to handle failure and trace information
    about which tactic was run *)
let return_thm ?(from = "unknown") = function
  | Ok thm ->
      perform (Trace (Proof, from));
      thm
  | Error e ->
      trace_error @@ print_error e;
      fail ()

(** [left_tac] takes goals like [P \/ Q] and creates the subgoal [P]. It fails
    if the goals conclusion is not a conjunction. This tactic is [not safe], as
    it is not true that [P] is always provable when [P \/ Q] is

    Effects
    + Fail
    + Subgoal
    + Burn
    + Trace *)
let left_tac : tactic =
 fun (asms, concl) ->
  burn "left_tac" (Unsafe 6);
  let thm =
    let* l, r = destruct_disj concl in
    let l_thm = perform (Subgoal (asms, l)) in
    let t = disj_left r l_thm in
    trace_dbg "disj_left success";
    t
  in
  return_thm ~from:"left_tac" thm

(** [right_tac] takes goals like [P \/ Q] and creates the subgoal [Q]. It fails
    if the goals conclusion is not a conjunction. This tactic is [not safe], as
    it is not true that [Q] is always provable when [P \/ Q] is

    Effects
    + Subgoal
    + Burn
    + Fail
    + Trace *)
let right_tac : tactic =
 fun (asms, concl) ->
  burn "right_tac" (Unsafe 6);
  let thm =
    let* l, r = destruct_disj concl in
    let r_thm = perform (Subgoal (asms, r)) in
    let t = disj_right r_thm l in
    trace_dbg "disj_right success";
    t
  in
  return_thm ~from:"right_tac" thm

(** [or_tac] chooses between [left_tac] and [right_tac], ensuring both sides are
    attempted if used under a search combinator

    Effects: Choose, Fail, Burn, Trace *)
let or_tac : tactic =
 fun (asms, concl) ->
  burn "or_tac" (Unsafe 6);
  let tac = choose_tactics [ left_tac; right_tac ] in
  let thm = Ok (tac (asms, concl)) in
  return_thm ~from:"or_tac" thm

(** [apply_asm_tac] finds assumptions of the form [P -> Q] for the goal [Q] and
    creates a subgoal [P]

    Effects: Rank, Choose, Burn, Fail, Subgoal *)
let apply_asm_tac : tactic =
 fun (asms, concl) ->
  burn "apply_asm_tac" (Unsafe 4);
  let matching =
    asms
    |> List.filter_map (fun asm ->
        match destruct_imp asm with
        | Ok (prem, conc) when conc = concl -> Some (asm, prem)
        | _ -> None)
  in
  let choices = rank_terms (List.map fst matching) in
  let chosen = choose_terms choices in
  let h = matching |> List.assoc chosen in
  let thm =
    let* assumed = assume chosen in
    trace_dbg "assume chosen h success";
    let sub_thm = perform (Subgoal (asms, h)) in
    let thm = mp assumed sub_thm in
    trace_dbg "mp success";
    thm
  in
  return_thm ~from:"apply_asm_tac" thm

(** [apply_thm_tac] applies a chosen theorem from [Rules] by stripping foralls
    and matching the conclusion against the goal

    Effects: Rules, Choose, Burn, Trace, Subgoal, Fail *)
let apply_thm_tac : tactic =
 fun (asms, conc) ->
  burn "apply_thm_tac" (Unsafe 5);
  let lemmas = perform Rules in
  let chosen_thm = choose_theorems lemmas in

  let rec strip_foralls_acc thm vars =
    match destruct_forall (concl thm) with
    | Ok (var, _body) -> (
        let thm' = Derived.spec var thm in
        match thm' with
        | Ok thm' -> strip_foralls_acc thm' (var :: vars)
        | Error _ -> (thm, List.rev vars))
    | Error _ -> (thm, List.rev vars)
  in
  let stripped_thm, quant_vars = strip_foralls_acc chosen_thm [] in

  let thm =
    match destruct_imp (concl stripped_thm) with
    | Ok (_prem, thm_conc) -> (
        match Rewrite.match_term thm_conc conc with
        | Some env ->
            let all_vars_bound =
              List.for_all
                (fun v ->
                  let v_typed = Rewrite.term_type_subst env.type_sub v in
                  List.exists
                    (fun (pat, _) -> alphaorder pat v_typed = 0)
                    env.term_sub)
                quant_vars
            in
            if not all_vars_bound then fail ();

            let* type_inst = inst_type env.type_sub stripped_thm in
            let term_sub_flipped =
              List.map (fun (v, t) -> (t, v)) env.term_sub
            in
            let* fully_inst = inst term_sub_flipped type_inst in

            let* inst_prem, _ = destruct_imp (concl fully_inst) in
            let sub_thm = perform (Subgoal (asms, inst_prem)) in
            mp fully_inst sub_thm
        | None -> fail ())
    | Error _ -> (
        match Rewrite.match_term (concl stripped_thm) conc with
        | Some env ->
            let* type_inst = inst_type env.type_sub stripped_thm in
            let term_sub_flipped =
              List.map (fun (v, t) -> (t, v)) env.term_sub
            in
            inst term_sub_flipped type_inst
        | None -> fail ())
  in
  return_thm ~from:"apply_thm_tac" thm

(** [apply_thm_asm_tac] applies a chosen theorem from [Rules] to a chosen
    assumption. If theorem is [P ==> Q] and assumption is [P], replaces the
    assumption with [Q] and creates a subgoal with the updated assumptions

    Effects: Rules, Choose, Burn, Trace, Subgoal, Fail *)
let apply_thm_asm_tac : tactic =
 fun (asms, conc) ->
  burn "apply_thm_asm_tac" (Unsafe 6);
  let lemmas = perform Rules in
  let chosen_thm = choose_theorems lemmas in
  let chosen_asm = choose_terms asms in

  let rec strip_foralls_acc thm vars =
    match destruct_forall (concl thm) with
    | Ok (var, _body) -> (
        let thm' = Derived.spec var thm in
        match thm' with
        | Ok thm' -> strip_foralls_acc thm' (var :: vars)
        | Error _ -> (thm, List.rev vars))
    | Error _ -> (thm, List.rev vars)
  in
  let stripped_thm, quant_vars = strip_foralls_acc chosen_thm [] in

  let thm =
    match destruct_imp (concl stripped_thm) with
    | Ok (prem, _thm_conc) -> (
        match Rewrite.match_term prem chosen_asm with
        | Some env ->
            let all_vars_bound =
              List.for_all
                (fun v ->
                  let v_typed = Rewrite.term_type_subst env.type_sub v in
                  List.exists
                    (fun (pat, _) -> alphaorder pat v_typed = 0)
                    env.term_sub)
                quant_vars
            in
            if not all_vars_bound then fail ();

            let* type_inst = inst_type env.type_sub stripped_thm in
            let term_sub_flipped =
              List.map (fun (v, t) -> (t, v)) env.term_sub
            in
            let* fully_inst = inst term_sub_flipped type_inst in

            let* _, new_asm = destruct_imp (concl fully_inst) in

            let asms' = new_asm :: List.filter (( <> ) chosen_asm) asms in
            let sub_thm = perform (Subgoal (asms', conc)) in

            let* asm_thm = assume chosen_asm in
            let* new_asm_thm = mp fully_inst asm_thm in
            prove_hyp new_asm_thm sub_thm
        | None -> fail ())
    | Error _ -> fail ()
  in
  return_thm ~from:"apply_thm_asm_tac" thm

(** [apply_neg_asm_tac] proves [F] by finding a negation [~P] in assumptions and
    creating a subgoal to prove [P]. Fails if the goal is not [F] or no suitable
    negation exists

    Effects: Choose, Burn, Trace, Subgoal, Fail *)
let apply_neg_asm_tac : tactic =
 fun (asms, concl) ->
  burn "apply_neg_asm_tac" (Unsafe 5);
  let false_tm = make_false () in
  if concl <> false_tm then fail ()
  else
    let negs = List.filter is_neg asms in
    if List.is_empty negs then fail ()
    else
      let thm =
        let chosen = choose_terms negs in
        let* p = term_of_negation chosen in
        if List.mem p asms then fail ()
        else
          let* neg_thm = assume chosen in
          let* elim = not_elim neg_thm in
          let sub_thm = perform (Subgoal (asms, p)) in
          prove_hyp sub_thm elim
      in
      return_thm ~from:"apply_neg_asm_tac" thm

(** [assume_tac] proves any goal by assuming it. This creates a theorem with the
    goal as a hypothesis

    Effects: Burn, Trace *)
let assume_tac : tactic =
 fun (_asms, conc) ->
  burn "assume_tac" (Unsafe 2);
  return_thm ~from:"assume_tac" @@ assume conc

(** [sym_tac] transforms a goal [l = r] into [r = l]

    Effects: Burn, Trace, Subgoal, Fail *)
let sym_tac : tactic =
 fun (asms, conc) ->
  burn "sym_tac" (Safe 1);
  let thm =
    let* l, r = destruct_eq conc in
    let* flipped = safe_make_eq r l in
    let flip_thm = perform @@ Subgoal (asms, flipped) in
    sym flip_thm
  in
  return_thm ~from:"sym_tac" thm

(** [rewrite_tac] rewrites the goal using a chosen theorem from [Rules].
    Performs subterm matching and fails if no progress is made

    Effects: Rules, Choose, Burn, Trace, Subgoal, Fail *)
let rewrite_tac : tactic =
 fun (asms, conc) ->
  burn "rewrite_tac" (Unsafe 5);
  let thm =
    let rules = perform Rules in
    let* chosen_rule = strip_forall (choose_theorems rules) in
    (* print_thm chosen_rule; *)

    let* rw_thm = rewrite_once chosen_rule conc in
    let* _, conc_rewritten = destruct_eq (concl rw_thm) in
    (* Fail if no progress was made *)
    if alphaorder conc conc_rewritten = 0 then fail ();
    let subthm = perform @@ Subgoal (asms, conc_rewritten) in
    let* rw_sym = sym rw_thm in
    eq_mp rw_sym subthm
  in
  return_thm ~from:"rewrite_tac" thm

(** [rewrite_asm_tac] rewrites a chosen assumption using a theorem from [Rules].
    Fails if no progress is made

    Effects: Rules, Choose, Burn, Trace, Subgoal, Fail *)
let rewrite_asm_tac : tactic =
 fun (asms, conc) ->
  burn "rewrite_asm_tac" (Unsafe 5);
  let thm =
    let rules = perform Rules in
    let* chosen_rule = strip_forall (choose_theorems rules) in
    let chosen_asm = choose_terms asms in

    let* rw_thm = rewrite_once chosen_rule chosen_asm in
    let* _, asm_rewritten = destruct_eq (concl rw_thm) in
    if alphaorder chosen_asm asm_rewritten = 0 then fail ();

    let asms' = asm_rewritten :: List.filter (( <> ) chosen_asm) asms in
    let sub_thm = perform @@ Subgoal (asms', conc) in

    let* asm_thm = assume chosen_asm in
    let* new_asm_thm = eq_mp rw_thm asm_thm in
    prove_hyp new_asm_thm sub_thm
  in
  return_thm ~from:"rewrite_asm_tac" thm

(** [beta_tac] performs deep beta reduction on the goal and creates a subgoal
    with the reduced term

    Effects: Burn, Trace, Subgoal, Fail *)
let beta_tac : tactic =
 fun (asms, conc) ->
  burn "beta_tac" (Safe 1);
  let thm =
    let* beta_thm = deep_beta conc in
    let* _, conc_reduced = destruct_eq (concl beta_thm) in
    let subthm = perform @@ Subgoal (asms, conc_reduced) in
    let* beta_sym = sym beta_thm in
    eq_mp beta_sym subthm
  in
  return_thm ~from:"beta_tac" thm

(** [beta_asm_tac] performs deep beta reduction on a chosen assumption. Fails if
    no progress is made

    Effects: Choose, Burn, Trace, Subgoal, Fail *)
let beta_asm_tac : tactic =
 fun (asms, conc) ->
  burn "beta_asm_tac" (Safe 1);
  let thm =
    let chosen_asm = choose_terms asms in
    let* beta_thm = deep_beta chosen_asm in
    let* _, asm_reduced = destruct_eq (concl beta_thm) in
    if alphaorder chosen_asm asm_reduced = 0 then fail ();

    let asms' = asm_reduced :: List.filter (( <> ) chosen_asm) asms in
    let sub_thm = perform @@ Subgoal (asms', conc) in

    let* asm_thm = assume chosen_asm in
    let* new_asm_thm = eq_mp beta_thm asm_thm in
    prove_hyp new_asm_thm sub_thm
  in
  return_thm ~from:"beta_asm_tac" thm

(** [mp_asm_tac] finds an implication [P ==> Q] in assumptions where [P] is also
    an assumption, and adds [Q] to the assumptions. Fails if no such implication
    exists or [Q] is already present

    Effects: Choose, Burn, Trace, Subgoal, Fail *)
let mp_asm_tac : tactic =
 fun (asms, concl) ->
  burn "mp_asm_tac" (Unsafe 3);
  let imps = List.filter is_imp asms in
  if List.is_empty imps then fail ()
  else
    let thm =
      let chosen_imp = choose_terms imps in
      let* prem, conc = destruct_imp chosen_imp in
      if List.mem prem asms && not (List.mem conc asms) then
        let asms' = conc :: asms in
        let sub_thm = perform (Subgoal (asms', concl)) in
        let* imp_thm = assume chosen_imp in
        let* prem_thm = assume prem in
        let* conc_thm = mp imp_thm prem_thm in
        prove_hyp conc_thm sub_thm
      else fail ()
    in
    return_thm ~from:"mp_asm_tac" thm

(** [intro_tac] transforms a goal [P ==> Q] into a subgoal [Q] with [P] added to
    the assumptions. Fails if goal is not an implication

    Effects: Burn, Trace, Subgoal, Fail *)
let intro_tac : tactic =
 fun (asms, concl) ->
  burn "intro_tac" (Safe 1);
  let thm =
    let* hyp = side_of_op "==>" Left concl in
    let* conc = side_of_op "==>" Right concl in
    trace_dbg "destruct success";

    let body_thm = perform (Subgoal (hyp :: asms, conc)) in
    let t = disch hyp body_thm in
    trace_dbg "disch success";
    t
  in
  return_thm ~from:"intro_tac" thm

(** [refl_tac] proves goals of the form [t = t] by reflexivity. Fails if the
    goal is not an equality or the sides are not identical

    Effects: Burn, Trace, Fail *)
let refl_tac : tactic =
 fun (_asms, concl) ->
  burn "refl_tac" (Safe 1);
  let thm =
    let* l, r = destruct_eq concl in
    trace_dbg "destruct success";
    if l = r then (
      let t = refl l in
      trace_dbg "refl success";
      t)
    else (
      trace_error "refl failure: left and right not eq";
      fail ())
  in
  return_thm ~from:"refl_tac" thm

(** [assumption_tac] proves the goal if it matches one of the assumptions. Fails
    if no matching assumption is found

    Effects: Choose, Burn, Trace, Fail *)
let assumption_tac : tactic =
 fun (asms, concl) ->
  burn "assumption_tac" (Safe 1);
  let asm = choose_terms asms in
  if concl <> asm then (
    trace_error "assumption doesn't match the goal";
    fail ())
  else (
    trace_dbg "Found matching assumption";
    let t = assume concl in
    trace_dbg "Assumption succeeded";
    return_thm ~from:"assumption_tac" t)

(** [conj_tac] transforms a goal [P /\ Q] into two subgoals [P] and [Q]. Fails
    if the goal is not a conjunction

    Effects: Burn, Trace, Subgoal, Fail *)
let conj_tac : tactic =
 fun (asms, concl) ->
  burn "conj_tac" (Safe 1);
  let thm =
    let* l, r = destruct_conj concl in
    trace_dbg "Destruct succeeded";

    let lthm = perform (Subgoal (asms, l)) in
    let rthm = perform (Subgoal (asms, r)) in

    let* thm = conj lthm rthm in

    trace_dbg "conj success";
    Ok thm
  in
  return_thm ~from:"conj_tac" thm

(** [elim_disj_asm_tac] eliminates a disjunction [P \/ Q] in the assumptions by
    case splitting, creating two subgoals: one with [P] and one with [Q]

    Effects: Choose, Burn, Trace, Subgoal, Fail *)
let elim_disj_asm_tac : tactic =
 fun (asms, concl) ->
  burn "elim_disj_asm_tac" (Unsafe 5);
  let disjs = List.filter is_disj asms in
  if List.is_empty disjs then fail ()
  else
    let thm =
      let chosen = choose_terms disjs in
      let* l, r = destruct_disj chosen in
      let asms' = List.filter (( <> ) chosen) asms in

      let left_goal = (l :: asms', concl) in
      let right_goal = (r :: asms', concl) in

      let lthm = perform (Subgoal left_goal) in
      let rthm = perform (Subgoal right_goal) in

      let* disj_asm = assume chosen in
      disj_cases disj_asm lthm rthm
    in
    return_thm ~from:"elim_disj_asm_tac" thm

(** [elim_conj_asm_tac] eliminates a conjunction [P /\ Q] in the assumptions by
    replacing it with both [P] and [Q] as separate assumptions

    Effects: Choose, Burn, Trace, Subgoal, Fail *)
let elim_conj_asm_tac : tactic =
 fun (asms, concl) ->
  burn "elim_conj_asm_tac" (Safe 1);
  let conjs = List.filter is_conj asms in
  if List.is_empty conjs then fail ()
  else
    let thm =
      let chosen = choose_terms conjs in
      let* l, r = destruct_conj chosen in
      let asms' = l :: r :: List.filter (( <> ) chosen) asms in
      let sub_thm = perform (Subgoal (asms', concl)) in
      let* conj_asm = assume chosen in
      let* l_thm = conj_left conj_asm in
      let* r_thm = conj_right conj_asm in
      let* p_1 = prove_hyp r_thm sub_thm in
      prove_hyp l_thm p_1
    in
    return_thm ~from:"elim_conj_asm_tac" thm

(** [neg_elim_tac] proves any goal when both [P] and [~P] are in assumptions,
    deriving a contradiction. Fails if no such pair exists

    Effects: Choose, Burn, Trace, Fail *)
let neg_elim_tac : tactic =
 fun (asms, concl) ->
  burn "neg_elim_tac" (Unsafe 3);
  let negs = List.filter is_neg asms in
  if List.is_empty negs then fail ()
  else
    let thm =
      let chosen_neg = choose_terms negs in
      let* p = term_of_negation chosen_neg in
      if List.mem p asms then
        let* neg_thm = assume chosen_neg in
        let* p_thm = assume p in
        let* false_thm = not_elim neg_thm in
        let* false_proved = prove_hyp p_thm false_thm in
        contr concl false_proved
      else fail ()
    in
    return_thm ~from:"neg_elim_tac" thm

(** [neg_intro_tac] transforms a goal [~P] into a subgoal [F] with [P] added to
    the assumptions. Fails if goal is not a negation or [P] is already an
    assumption

    Effects: Burn, Trace, Subgoal, Fail *)
let neg_intro_tac : tactic =
 fun (asms, concl) ->
  burn "neg_intro_tac" (Unsafe 4);
  let thm =
    let* p = term_of_negation concl in
    if List.mem p asms then fail ()
    else
      let f = make_false () in
      let goal' = (p :: asms, f) in
      let sub_thm = perform (Subgoal goal') in
      not_intro p sub_thm
  in
  return_thm ~from:"neg_intro_tac" thm

(** [ccontr_tac] proves [P] by classical contradiction: assumes [~P] and derives
    [F]. This is a classical (non-intuitionistic) tactic

    Effects: Burn, Trace, Subgoal, Fail *)
let ccontr_tac : tactic =
 fun (asms, concl) ->
  burn "ccontr_tac" (Unsafe 10);
  let false_tm = make_false () in
  let neg_concl = make_neg concl in
  if concl = false_tm || List.mem neg_concl asms then fail ()
  else
    let thm =
      let goal' = (neg_concl :: asms, false_tm) in
      let sub_thm = perform (Subgoal goal') in
      ccontr concl sub_thm
    in
    return_thm ~from:"ccontr_tac" thm

(** [false_elim_tac] proves any goal when [F] (false) is in the assumptions.
    Fails if [F] is not present

    Effects: Burn, Trace, Fail *)
let false_elim_tac : tactic =
 fun (asms, concl) ->
  burn "false_elim_tac" (Safe 1);
  let false_tm = make_false () in
  if List.mem false_tm asms then
    let thm =
      let* false_thm = assume false_tm in
      contr concl false_thm
    in
    return_thm ~from:"false_elim_tac" thm
  else fail ()

(** [gen_tac] transforms a goal [forall x. P] into a subgoal [P]. Fails if the
    goal is not a universal quantification

    Effects: Burn, Trace, Subgoal, Fail *)
let gen_tac : tactic =
 fun (asms, concl) ->
  burn "gen_tac" (Safe 1);
  let thm =
    let* x, body = destruct_forall concl in
    let body_thm = perform (Subgoal (asms, body)) in
    let hyps_with_x = List.filter (fun h -> var_free_in x h) (hyp body_thm) in
    let* discharged =
      List.fold_left
        (fun acc h ->
          let* thm = acc in
          disch h thm)
        (Ok body_thm) hyps_with_x
    in
    gen x discharged
  in
  return_thm ~from:"gen_tac" thm

(** [induct_tac] applies structural induction on the quantified variable of a
    goal [forall x. P]. Creates subgoals for each constructor case of the
    inductive type. Fails if the goal is not universally quantified or the type
    is not inductive

    Effects: Burn, Trace, Subgoal, Fail *)
let induct_tac : tactic =
 fun (asms, concl) ->
  burn "induct_tac" (Unsafe 8);
  let thm =
    let* induction_var, bod = destruct_forall concl in
    let* ty = type_of_term induction_var in
    let* ty_name, ty_args = destruct_type ty in

    let inductive_def =
      match Hashtbl.find_opt the_inductives ty_name with
      | None ->
          trace_error "quantified type is not an inductive";
          fail ()
      | Some d -> d
    in

    let* _, def_ty_params = destruct_type inductive_def.ty in

    let type_sub = List.combine def_ty_params ty_args in

    let* typed_induction = inst_type type_sub inductive_def.induction in

    let binder = make_var "pred_binder" ty in
    let* bod_with_binder = vsubst [ (binder, induction_var) ] bod in
    let* p = make_lam binder bod_with_binder in

    let* inst_induction = spec p typed_induction in

    let rec collect_premises tm acc =
      match destruct_imp tm with
      | Ok (premise, rest) -> collect_premises rest (premise :: acc)
      | Error _ -> (List.rev acc, tm)
    in
    let cases, _conclusion =
      collect_premises (Kernel.concl inst_induction) []
    in

    let solved =
      cases
      |> List.map (fun case -> ((asms, case), perform (Subgoal (asms, case))))
    in

    let* result =
      List.fold_left
        (fun acc_thm (_goal, case_thm) ->
          let* acc = acc_thm in
          mp acc case_thm)
        (Ok inst_induction) solved
    in
    Ok result
  in
  return_thm ~from:"induction_tac" thm

(** [prove] is the main effect handler that runs a tactic on a goal. It provides
    default interpretations for all effects: printing traces, taking first
    choices, ignoring fuel costs, etc. Returns [Complete thm] on success or
    [Incomplete goal] on failure *)
let prove ?(name = "") (goal : goal) (tactic : tactic) =
  match tactic goal with
  (* Burn is used for resource tracking/limiting *)
  | effect Burn _, k -> continue k ()
  (* Rules is used for passing rewrites and lemmas to different tactics *)
  | effect Rules, k -> continue k []
  (* Trace is a unified interface for logs and errors *)
  | effect Trace (_, v), k ->
      print_endline v;
      continue k ()
  (* Rank is used to sort terms by an undetermined heuristic *)
  | effect Rank (Term terms), k -> continue k terms
  (* This represents failure for any reason *)
  | effect Fail, _k -> Incomplete goal
  (* Choose is used to decide how to explore options *)
  | effect Choose choices, k -> (
      match as_chosen_list choices with
      | [] ->
          print_endline "no choices available";
          Incomplete goal
      | c :: _ -> continue k c)
  (* Subgoal is used for branching the proof state,
         but prove should solve the goal completely *)
  | effect Subgoal g', _k -> Incomplete g'
  (* When a proof is complete we extract the theorem *)
  | exception Out_of_fuel ->
      print_endline "Out of fuel";
      Incomplete goal
  | thm ->
      Rules.add_proven name thm;
      Complete thm

(** [then_one] sequences two tactics: applies [tac1] then applies [tac] to only
    the first subgoal. Remaining subgoals bubble up. Infix: [>>] *)
let then_one (tac1 : tactic) : tactic_combinator =
 fun tac goal ->
  let handled_first = ref false in
  let rec handler f =
    match f () with
    | effect Subgoal g, k when not !handled_first ->
        let r = Multicont.Deep.promote k in
        handled_first := true;
        let thm : thm = tac g in
        handler (fun () -> Multicont.Deep.resume r thm)
    | v -> v
  in
  handler (fun () -> tac1 goal)

let ( >> ) = then_one

(** [then_all] sequences two tactics: applies [tac1] then applies [tac] to all
    subgoals. Infix: [>>>] *)
let then_all (tac1 : tactic) : tactic_combinator =
 fun tac goal ->
  let rec handler f =
    match f () with
    | effect Subgoal g, k ->
        let r = Multicont.Deep.promote k in
        let thm : thm = tac g in
        handler (fun () -> Multicont.Deep.resume r thm)
    | v -> v
  in
  handler (fun () -> tac1 goal)

let ( >>> ) = then_all

(** [then_each] applies a list of tactics to subgoals in order. Fails if there
    are more subgoals than tactics provided. Infix: [>>=] *)
let then_each (tacs : tactic list) : tactic_combinator =
  let tacs = ref tacs in
  fun tac goal ->
    match tac goal with
    | effect Subgoal g, k -> (
        let r = Multicont.Deep.promote k in
        match !tacs with
        | [] ->
            trace_proof "more subgoals than provided tactics";
            fail ()
        | next :: rest ->
            tacs := rest;
            Multicont.Deep.resume r @@ next g)
    | v -> v

let ( >>= ) = Fun.flip then_each

(** [with_first_success] handles [Choose] by trying each choice in order until
    one succeeds. Only handles choices at one level; for recursive search use
    [with_dfs] or [with_best_first] *)
let with_first_success : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Choose choices, k ->
      let r = Multicont.Deep.promote k in
      let rec try_each = function
        | [] ->
            trace_error "no choices available";
            fail ()
        | c :: cs -> (
            match Multicont.Deep.resume r c with
            | effect Fail, _ -> try_each cs
            | thm -> thm)
      in
      try_each (as_chosen_list choices)
  | v -> v

(** [with_term] forces a specific term to be chosen when a [Choose (Term _)]
    effect is performed. Fails if the term is not among the choices *)
let with_term (t : term) : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Choose (Term terms), k ->
      if List.mem t terms then continue k t else fail ()
  | x -> x

(** [try_] converts failure into a subgoal request, a tactics sequence to be
    used in situations where one or more intermediate tactics could fail *)
let try_ : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Fail, _ -> perform (Subgoal goal) | v -> v

(** [pick_tac] creates a tactic that chooses among the given tactics. Used with
    search combinators to explore different proof strategies

    Effects: Choose *)
let pick_tac (tacs : tactic list) : tactic =
 fun goal ->
  let tac = choose_tactics tacs in
  tac goal

(** [solve] requires a tactic to completely solve the goal without leaving
    subgoals. Fails if any subgoals remain *)
let solve : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Subgoal _g', _k -> fail () | v -> v

(** [run_thunk_with_path] executes a thunk while capturing [Trace (Proof, _)]
    effects into the provided path reference. Used by search combinators to
    track the winning proof sequence *)
let run_thunk_with_path (path : string list ref) (thunk : unit -> 'a) : 'a =
  let rec loop f =
    match f () with
    | effect Trace (Proof, name), k ->
        path := name :: !path;
        loop (fun () -> continue k ())
    | v -> v
  in
  loop thunk

(** [emit_proof_path] formats a proof path as a tactic script and emits it as a
    [Trace (Search, _)] effect

    Effects: Trace *)
let emit_proof_path (path : string list) : unit =
  let rec format_path = function
    | [] -> ""
    | [ last ] -> "  " ^ last
    | t :: rest -> "  " ^ t ^ " >>\n" ^ format_path rest
  in
  let proof_str = "Proof:\n" ^ format_path path in
  perform (Trace (Search, proof_str))

let stats_of_list l =
  List.fold_left
    (fun (sub, choice, res) (e, _, _, _) ->
      match e with
      | MResume -> (sub, choice, res + 1)
      | MSubgoal _ -> (sub + 1, choice, res)
      | MChoice _ -> (sub, choice + 1, res))
    (0, 0, 0) l
  |> fun (s, c, r) ->
  Printf.sprintf "Subgoals: %d | Choices: %d | Resumptions: %d\n" s c r

module StackFrontier : Frontier = struct
  type t = Priority.t Stack.t

  let create () = Stack.create ()
  let pop = Stack.pop_opt
  let add s x = Stack.push x s
  let stats (s : t) = s |> Stack.to_seq |> List.of_seq |> stats_of_list
end

let make_search (module F : Frontier) : tactic_combinator =
 fun tac goal ->
  let s = F.create () in
  F.add s (MSubgoal goal, (fun () -> step tac goal), [], []);
  let rec aux () =
    (* print_endline (F.stats s); *)
    match F.pop s with
    | None -> fail ()
    | Some (_, thunk, parents, path) -> (
        let current_path = ref path in
        match run_thunk_with_path current_path thunk with
        | Done v -> (
            match parents with
            | [] ->
                emit_proof_path !current_path;
                v
            | resume :: rest ->
                F.add s (MResume, (fun () -> resume v), rest, !current_path);
                aux ())
        | Need (g, resume) ->
            F.add s
              ( MSubgoal g,
                (fun () -> step tac g),
                resume :: parents,
                !current_path );
            aux ()
        | Dead -> aux ()
        | Cont thunks ->
            thunks |> List.rev
            |> List.iter (fun (m, t) ->
                F.add s (MChoice m, t, parents, !current_path));
            aux ())
  in
  aux ()

(** [with_dfs] performs depth-first search over choices and subgoals. Explores
    the proof space using a stack, backtracking on failure. Emits the winning
    proof path on success

    Effects: Trace (Search) on success, Fail if no proof found *)
let with_dfs : tactic_combinator = make_search (module StackFrontier)

module PQueueFrontier : Frontier = struct
  type t = PriorityQueue.t

  let create = PriorityQueue.create
  let pop = PriorityQueue.pop_max
  let add q x = PriorityQueue.add q x

  let stats (s : t) =
    s
    |> PriorityQueue.fold_unordered (fun acc a -> a :: acc) []
    |> stats_of_list
end

(** [with_best_first] performs best-first search over choices and subgoals. Uses
    a priority queue ordered by [search_metadata] to explore promising paths
    first (resumes before choices, choices before subgoals). Emits the winning
    proof path on success

    Effects: Trace (Search) on success, Fail if no proof found *)
let with_best_first : tactic_combinator = make_search (module PQueueFrontier)

module QueueFrontier : Frontier = struct
  type t = Priority.t Queue.t

  let create () = Queue.create ()
  let pop = Queue.take_opt
  let add q x = Queue.add x q
  let stats (s : t) = s |> Queue.to_seq |> List.of_seq |> stats_of_list
end

(** [with_bfs] performs breadth-first search over choices and subgoals. Uses a
    queue to explore paths level by level. Emits the winning proof path on
    success

    Effects: Trace (Search) on success, Fail if no proof found *)
let with_bfs : tactic_combinator = make_search (module QueueFrontier)

(** [with_dfs''] is an alternative DFS implementation using an explicit stack
    for choice points. Does not track proof paths *)
let with_dfs'' : tactic_combinator =
 fun tac goal ->
  let rec handler s f =
    match f () with
    | effect Choose choices, k ->
        let r = Multicont.Deep.promote k in
        (choices |> as_chosen_list |> List.rev
        |> List.iter @@ fun c ->
           Stack.push (fun () -> Multicont.Deep.resume r c) s);
        next s
    | effect Subgoal g, k -> (
        let s' = Stack.create () in
        match handler s' (fun () -> tac g) with
        | effect Fail, _ -> next s
        | (thm : thm) -> handler s (fun () -> continue k thm))
    | effect Fail, _ -> next s
    | v -> v
  and next s =
    match Stack.pop_opt s with None -> fail () | Some thunk -> handler s thunk
  in
  handler (Stack.create ()) (fun () -> tac goal)

(** [with_dfs'] is a recursive DFS implementation that uses the call stack for
    backtracking. Simpler but may overflow on deep searches. Does not track
    proof paths *)
let with_dfs' : tactic_combinator =
 fun tac goal ->
  let rec handler f =
    match f () with
    | effect Choose choices, k ->
        let r = Multicont.Deep.promote k in
        let rec try_each = function
          | [] -> fail ()
          | c :: cs -> (
              match handler (fun () -> Multicont.Deep.resume r c) with
              | effect Fail, _ -> try_each cs
              | thm -> thm)
        in
        try_each (as_chosen_list choices)
    | effect Subgoal g, k ->
        let thm : thm = handler (fun () -> tac g) in
        handler (fun () -> continue k thm)
    | effect Fail, _ -> fail ()
    | v -> v
  in
  handler (fun () -> tac goal)

(** [with_repeat] repeatedly applies a tactic until it fails or makes no
    progress. On failure after progress, emits a subgoal for the current state
*)
let with_repeat : tactic_combinator =
 fun tac goal ->
  let made_progress = ref false in
  let rec aux goal =
    match tac goal with
    | effect Fail, _ ->
        if !made_progress then perform (Subgoal goal) else fail ()
    | effect Subgoal g, _k when g = goal ->
        if !made_progress then perform (Subgoal goal) else fail ()
    | effect Subgoal g, k ->
        made_progress := true;
        continue k (aux g)
    | v -> v
  in
  aux goal

(** [itauto_tac] is a complete automation tactic for intuitionistic
    propositional logic. Chooses among various introduction and elimination
    tactics. Use with a search combinator like [with_dfs] or [with_best_first]

    Effects: Choose *)
let itauto_tac : tactic =
  pick_tac
    [
      assumption_tac;
      intro_tac;
      neg_intro_tac;
      gen_tac;
      conj_tac;
      elim_conj_asm_tac;
      elim_disj_asm_tac;
      false_elim_tac;
      neg_elim_tac;
      apply_asm_tac;
      apply_neg_asm_tac;
      mp_asm_tac;
      left_tac;
      right_tac;
    ]

(** [ctauto_tac] is a complete automation tactic for classical propositional
    logic. Chooses among various introduction and elimination tactics. Use with
    a search combinator like [with_dfs] or [with_best_first]

    Effects: Choose *)
let ctauto_tac : tactic =
  pick_tac
    [
      assumption_tac;
      intro_tac;
      neg_intro_tac;
      gen_tac;
      conj_tac;
      elim_conj_asm_tac;
      elim_disj_asm_tac;
      false_elim_tac;
      neg_elim_tac;
      apply_asm_tac;
      apply_neg_asm_tac;
      mp_asm_tac;
      left_tac;
      right_tac;
      ccontr_tac;
    ]

(** [ctauto_dfs_tac] is [ctauto_tac] wrapped with [with_dfs] for automatic
    depth-first proof search *)
let ctauto_dfs_tac : tactic = with_dfs ctauto_tac

(** [with_interactive_choice] handles [Choose] effects by prompting the user to
    select from the available options via stdin *)
let with_interactive_choice : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Trace (_, s), k ->
      print_endline s;
      continue k ()
  | effect Choose choices, k ->
      if List.is_empty (as_chosen_list choices) then fail ()
      else
        let rec get_choice cs =
          let idx = read_int () in
          match List.nth_opt cs idx with
          | Some c -> c
          | None ->
              print_endline "Invalid choice";
              get_choice cs
        in
        continue k (get_choice (as_chosen_list choices))
  | v -> v

(** [with_nth_choice n] always selects the [n]th option from any [Choose]
    effect. Fails if [n] is out of bounds *)
let with_nth_choice n : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Choose cs, k -> (
      match List.nth_opt (as_chosen_list cs) n with
      | None -> fail ()
      | Some c -> continue k c)
  | v -> v

(** [with_term_size_ranking] handles [Rank (Term _)] effects by sorting terms
    from smallest to largest based on AST size *)
let with_term_size_ranking : tactic_combinator =
  let rec term_size (t : term) =
    match t with
    | Var (_, _) -> 1
    | Const (_, _) -> 1
    | App (l, r) -> 1 + term_size l + term_size r
    | Lam (bind, bod) -> 1 + term_size bind + term_size bod
  in
  fun tac goal ->
    match tac goal with
    | effect Rank (Term terms), k ->
        let sorted =
          List.stable_sort
            (fun l r -> compare (term_size l) (term_size r))
            terms
        in
        continue k sorted
    | v -> v

let cost_value = function Safe n | Unsafe n -> n

let with_added_fuel extra : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Burn (name, cost), k ->
      let new_cost =
        match cost with
        | Safe n -> Safe (n + extra)
        | Unsafe n -> Unsafe (n + extra)
      in
      burn name new_cost;
      continue k ()
  | v -> v

(** [with_fuel_limit] tracks fuel consumption and raises [Out_of_fuel] when the
    limit is exceeded. The limit is a mutable reference that decreases with each
    [Burn] effect *)
let with_fuel_limit limit : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Burn (name, cost), k ->
      let n = cost_value cost in
      limit := !limit - n;
      if !limit <= 0 then discontinue k Out_of_fuel
      else (
        burn name cost;
        continue k ())
  | v -> v

(** [with_fuel_counter] tracks total fuel consumed by incrementing a mutable
    reference for each [Burn] effect *)
let with_fuel_counter r : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Burn (name, cost), k ->
      r := !r + cost_value cost;
      burn name cost;
      continue k ()
  | v -> v

(** [with_no_trace] suppresses trace messages. By default suppresses all except
    [Search]. Set [show_proof:true] to also show [Proof] traces *)
let with_no_trace ?(show_proof = false) : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Trace (Info, _), k -> continue k ()
  | effect Trace (Debug, _), k -> continue k ()
  | effect Trace (Error, _), k -> continue k ()
  | effect Trace (Warn, _), k -> continue k ()
  | effect Trace (Proof, _), k when not show_proof -> continue k ()
  | v -> v

(** [with_assumptions] provides the goal's assumptions as theorems when a
    [Rules] effect is performed *)
let with_assumptions : tactic_combinator =
 fun tac (asms, concl) ->
  let asm_thms =
    List.filter_map
      (fun asm -> match assume asm with Ok thm -> Some thm | Error _ -> None)
      asms
  in
  match tac (asms, concl) with effect Rules, k -> continue k asm_thms | v -> v

(** [with_rules] provides a fixed list of theorems when a [Rules] effect is
    performed *)
let with_rules (rules : thm list) : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Rules, k -> continue k rules | v -> v

(** [with_rule] provides a single theorem when a [Rules] effect is performed *)
let with_rule (rule : thm) : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Rules, k -> continue k [ rule ] | v -> v

(** [with_proven] looks up previously proven theorems by name and provides them
    when a [Rules] effect is performed. Fails if any name is not found *)
let with_proven (names : string list) : tactic_combinator =
  let rules =
    names
    |> List.map @@ fun n ->
       match Rules.get_proven n with
       | None ->
           trace_error (Printf.sprintf "Couldn't find rule with name %s\n" n);
           fail ()
       | Some rule -> rule
  in
  fun tac goal ->
    match tac goal with effect Rules, k -> continue k rules | v -> v

(** [with_rules_and_assumptions] provides both the given rules and the goal's
    assumptions as theorems when a [Rules] effect is performed *)
let with_rules_and_assumptions (rules : thm list) : tactic_combinator =
 fun tac (asms, concl) ->
  let asm_thms =
    List.filter_map
      (fun asm -> match assume asm with Ok thm -> Some thm | Error _ -> None)
      asms
  in
  match tac (asms, concl) with
  | effect Rules, k -> continue k (rules @ asm_thms)
  | v -> v

(** [intros_tac] repeatedly applies [intro_tac] and [gen_tac] until neither
    makes progress. Useful for introducing all hypotheses at once *)
let intros_tac : tactic =
 fun goal ->
  with_repeat (with_first_success (pick_tac [ intro_tac; gen_tac ])) goal

(** [simp_tac] simplifies the goal using rewrite rules from definitions and
    registered simp lemmas. Set [with_asms:false] to exclude assumptions

    Effects: Rules, Choose, Burn, Trace, Subgoal, Fail *)
let simp_tac ?(with_asms = true) : tactic =
 fun goal ->
  (* TODO: get the base simp set here. The effect for rules should return proper rules not just unprocessed thms *)
  let add = perform Rules in
  let definitions = !Rules.definitions |> List.map snd in
  let simps = !Rules.simps |> List.map snd in
  let rules =
    definitions |> List.append add |> List.append simps
    |> List.filter_map (fun d -> Result.to_option @@ rules_of_def d)
    |> List.flatten
  in

  let with_rw = if with_asms then with_rules_and_assumptions else with_rules in

  let thm =
    with_repeat
      (with_first_success
      @@ pick_tac [ with_rw rules rewrite_tac; with_repeat beta_tac; refl_tac ]
      )
      goal
  in
  thm

(** [auto_tac] is an automation tactic combining simplification with basic
    logical tactics. Use with a search combinator for full automation

    Effects: Choose *)
let auto_tac : tactic =
  pick_tac
    [
      simp_tac ~with_asms:true;
      gen_tac;
      intro_tac;
      assumption_tac;
      neg_intro_tac;
      conj_tac;
      elim_conj_asm_tac;
      false_elim_tac;
      mp_asm_tac;
    ]

(** [auto_dfs_tac] is [auto_tac] wrapped with [with_dfs] for automatic
    depth-first proof search *)
let auto_dfs_tac : tactic = with_dfs @@ auto_tac

(** [simp_asm_tac] simplifies assumptions using rewrite rules from definitions.
    Use [add] to provide additional rules. Set [with_asms:false] to exclude
    other assumptions as rewrite rules

    Effects: Rules, Choose, Burn, Trace, Subgoal, Fail *)
let simp_asm_tac ?(with_asms = true) ?(add = []) : tactic =
 fun goal ->
  let definitions =
    the_specifications |> Hashtbl.to_seq |> List.of_seq |> List.map snd
  in
  let rules =
    definitions
    |> List.filter_map (fun d -> Result.to_option @@ rules_of_def d)
    |> List.flatten |> List.append add
  in

  let with_rw = if with_asms then with_rules_and_assumptions else with_rules in

  let thm =
    with_repeat
      (with_first_success
      @@ pick_tac
           [
             with_rw rules rewrite_asm_tac;
             with_repeat beta_asm_tac;
             assumption_tac;
           ])
      goal
  in
  thm

let run_proof ?(notrace = true) ?(name = "") goal tac =
  let fuel_count = ref 0 in
  let limit = ref 1_000_000 in
  let wrapped =
    (if notrace then with_no_trace ~show_proof:false else Fun.id)
    @@ (with_fuel_limit limit) (with_fuel_counter fuel_count tac)
  in
  match prove ~name goal wrapped with
  | Complete thm ->
      print_thm thm;
      print_endline "Proof Complete!";
      Printf.printf "with fuel: %d\n" !fuel_count
  | Incomplete (asms, c) ->
      List.iter print_term asms;
      print_term c;
      print_endline "Proof Incomplete";
      Printf.printf "with fuel: %d\n" !fuel_count
