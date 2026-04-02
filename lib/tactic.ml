open Kernel
open Derived
open Printing
open Effect
open Effect.Deep
open Result.Syntax
open Rewrite

type goal = term list * term [@@deriving show]

let make_goal ?(asms = []) t = (asms, t)

type level = Debug | Info | Warn | Error | Proof | Search
type proof_state = Incomplete of goal | Complete of thm [@@deriving show]
type tactic = goal -> thm
type tactic_combinator = tactic -> tactic
type cost = Safe of int | Unsafe of int

type choice_kind =
  | CTerm of (goal * term)
  | CTheorem of goal * thm
  | CTactic of goal * cost * tactic
  | CUnknown of goal

type search_metadata = MSubgoal of goal | MChoice of choice_kind | MResume

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
        | CTerm (_, t1), CTerm (_, t2) ->
            let s1, s2 = (term_size t1, term_size t2) in
            compare s2 s1
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

type _ rankable =
  | Term : term list -> term rankable
  | Goal : goal list -> goal rankable
  | Tactic : tactic list -> tactic rankable
  | Unknown : 'a list -> 'a rankable

type _ choosable =
  | Term : term list -> term choosable
  | Theorem : thm list -> thm choosable
  | Tactic : tactic list -> tactic choosable
  | Unknown : 'a list -> 'a choosable

exception Out_of_fuel

type _ Effect.t +=
  | Subgoal : goal -> thm Effect.t
  | Choose : 'a choosable -> 'a Effect.t
  | Rank : 'a rankable -> 'a list Effect.t
  | Fail : 'a Effect.t
  | Trace : (level * string) -> unit Effect.t
  | Burn : (string * cost) -> unit Effect.t
  | Rules : thm list Effect.t

let as_ranked_list : type a. a rankable -> a list = function
  | Term ts -> ts
  | Goal gs -> gs
  | Tactic tacs -> tacs
  | Unknown xs -> xs

let as_chosen_list : type a. a choosable -> a list = function
  | Term ts -> ts
  | Theorem thms -> thms
  | Tactic tacs -> tacs
  | Unknown xs -> xs

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

let fail () = perform Fail
let burn name cost = perform (Burn (name, cost))
let trace_dbg a = perform (Trace (Debug, a))
let trace_info a = perform (Trace (Info, a))
let trace_error a = perform (Trace (Error, a))
let trace_proof a = perform (Trace (Proof, a))
let choose_terms gs = perform (Choose (Term gs))
let choose_theorems gs = perform (Choose (Theorem gs))
let choose_tactics gs = perform (Choose (Tactic gs))
let choose_unknowns gs = perform (Choose (Unknown gs))
let rank_terms ts = perform (Rank (Term ts))

let return_thm ?(from = "unknown") = function
  | Ok thm ->
      perform (Trace (Proof, from));
      thm
  | Error e ->
      trace_error @@ print_error e;
      fail ()

(* let noop_tac : tactic = fun goal -> perform (Subgoal goal) *)

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

let or_tac : tactic =
 fun (asms, concl) ->
  burn "or_tac" (Unsafe 6);
  let tac = choose_tactics [ left_tac; right_tac ] in
  let thm = Ok (tac (asms, concl)) in
  return_thm ~from:"or_tac" thm

let apply_asm_tac : tactic =
 fun (asms, concl) ->
  burn "apply_asm_tac" (Unsafe 4);
  let rec collect_premises tm acc =
    match destruct_imp tm with
    | Ok (premise, rest) -> collect_premises rest (premise :: acc)
    | Error _ -> (List.rev acc, tm)
  in
  let matching =
    asms
    |> List.filter_map (fun asm ->
        let prems, final_conc = collect_premises asm [] in
        if prems <> [] && final_conc = concl then Some (asm, prems) else None)
  in
  let choices = rank_terms (List.map fst matching) in
  let chosen = choose_terms choices in
  let prems = matching |> List.assoc chosen in
  let thm =
    let* assumed = assume chosen in
    List.fold_left
      (fun acc_thm prem ->
        let* acc = acc_thm in
        let sub_thm = perform (Subgoal (asms, prem)) in
        mp acc sub_thm)
      (Ok assumed) prems
  in
  return_thm ~from:"apply_asm_tac" thm

let apply_thm_tac : tactic =
 fun (asms, conc) ->
  burn "apply_thm_tac" (Unsafe 5);
  let lemmas = perform Rules in
  let chosen_thm = choose_theorems lemmas in

  let avoid = conc :: asms in
  let rec strip_foralls_acc thm vars avoid =
    match destruct_forall (concl thm) with
    | Ok (var, _body) -> (
        let fresh_var =
          match variant avoid var with Ok v -> v | Error _ -> var
        in
        let thm' = Derived.spec fresh_var thm in
        match thm' with
        | Ok thm' ->
            strip_foralls_acc thm' (fresh_var :: vars) (fresh_var :: avoid)
        | Error _ -> (thm, List.rev vars))
    | Error _ -> (thm, List.rev vars)
  in
  let stripped_thm, quant_vars = strip_foralls_acc chosen_thm [] avoid in

  let rec collect_premises tm acc =
    match destruct_imp tm with
    | Ok (premise, rest) -> collect_premises rest (premise :: acc)
    | Error _ -> (List.rev acc, tm)
  in
  let prems, final_conc = collect_premises (concl stripped_thm) [] in

  let extend_env_from_asms env =
    List.fold_left
      (fun env prem ->
        List.fold_left
          (fun env asm ->
            match Rewrite.term_match [] [] env prem asm with
            | Some env' -> env'
            | None -> env)
          env asms)
      env prems
  in
  let all_vars_bound env =
    List.for_all
      (fun v ->
        let v_typed = Rewrite.term_type_subst env.type_sub v in
        List.exists (fun (pat, _) -> alphaorder pat v_typed = 0) env.term_sub)
      quant_vars
  in

  let thm =
    match Rewrite.match_term final_conc conc with
    | Some env ->
        let env = extend_env_from_asms env in
        if not (all_vars_bound env) then fail ();

        let* type_inst = inst_type env.type_sub stripped_thm in
        let term_sub_flipped = List.map (fun (v, t) -> (t, v)) env.term_sub in
        let* fully_inst = inst term_sub_flipped type_inst in

        if prems = [] then Ok fully_inst
        else
          let inst_prems, _ = collect_premises (concl fully_inst) [] in
          List.fold_left
            (fun acc_thm prem ->
              let* acc = acc_thm in
              let sub_thm = perform (Subgoal (asms, prem)) in
              mp acc sub_thm)
            (Ok fully_inst) inst_prems
    | None -> fail ()
  in
  return_thm ~from:"apply_thm_tac" thm

let apply_thm_asm_tac : tactic =
 fun (asms, conc) ->
  burn "apply_thm_asm_tac" (Unsafe 6);
  let lemmas = perform Rules in
  let chosen_thm = choose_theorems lemmas in
  let chosen_asm = choose_terms asms in

  let avoid = conc :: asms in
  let rec strip_foralls_acc thm vars avoid =
    match destruct_forall (concl thm) with
    | Ok (var, _body) -> (
        let fresh_var =
          match variant avoid var with Ok v -> v | Error _ -> var
        in
        let thm' = Derived.spec fresh_var thm in
        match thm' with
        | Ok thm' ->
            strip_foralls_acc thm' (fresh_var :: vars) (fresh_var :: avoid)
        | Error _ -> (thm, List.rev vars))
    | Error _ -> (thm, List.rev vars)
  in
  let stripped_thm, quant_vars = strip_foralls_acc chosen_thm [] avoid in

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

let assume_tac : tactic =
 fun (_asms, conc) ->
  burn "assume_tac" (Unsafe 2);
  return_thm ~from:"assume_tac" @@ assume conc

let sorry_tac : tactic =
 fun (_, conc) ->
  burn "sorry_tac" (Unsafe 1);
  let thm = new_axiom conc in
  return_thm ~from:"sorry_tac" thm

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

let rewrite_asm_tac : tactic =
 fun (asms, conc) ->
  burn "rewrite_asm_tac" (Unsafe 5);
  let thm =
    let rules = perform Rules in
    let* chosen_rule = strip_forall (choose_theorems rules) in
    let chosen_asm = choose_terms asms in

    (* prevent an assumption from being used as a rule to rewrite itself *)
    if List.mem chosen_asm (hyp chosen_rule) then fail ();

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

let assert_tac : tactic =
 fun (asms, concl) ->
  burn "assert_tac" (Unsafe 5);
  let thm =
    let assertion = choose_terms [] in
    let asserted_thm = perform (Subgoal (asms, assertion)) in
    let with_assertion_thm = perform (Subgoal (assertion :: asms, concl)) in
    prove_hyp asserted_thm with_assertion_thm
  in
  return_thm ~from:"assert_tac" thm

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

(* need to make an arbitrary term of the same type as the
   equality, and make subgoals for both sides then use
   the trans derived rule to make a thm. fail if not an eq *)
let trans_tac : tactic =
 fun (asms, concl) ->
  burn "trans_tac" (Safe 1);
  let thm =
    let* l, r = destruct_eq concl in
    let s = choose_terms [] in
    let* leq = safe_make_eq l s in
    let* req = safe_make_eq s r in
    let lthm = perform (Subgoal (asms, leq)) in
    let rthm = perform (Subgoal (asms, req)) in
    trans lthm rthm
  in
  return_thm ~from:"refl_tac" thm

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

let spec_asm_tac (tm : term) : tactic =
 fun (asms, concl) ->
  burn "spec_asm_tac" (Unsafe 3);
  let foralls =
    List.filter
      (fun a -> match destruct_forall a with Ok _ -> true | _ -> false)
      asms
  in
  if List.is_empty foralls then fail ()
  else
    let thm =
      let chosen = choose_terms foralls in
      let* asm_thm = assume chosen in
      let* specialized = spec tm asm_thm in
      let spec_concl = Kernel.concl specialized in
      if List.mem spec_concl asms then fail ()
      else
        let asms' = spec_concl :: asms in
        let sub_thm = perform (Subgoal (asms', concl)) in
        prove_hyp specialized sub_thm
    in
    return_thm ~from:"spec_asm_tac" thm

let sym_asm_tac : tactic =
 fun (asms, concl) ->
  burn "sym_asm_tac" (Safe 2);
  let eqs = List.filter is_eq asms in
  if List.is_empty eqs then fail ()
  else
    let thm =
      let chosen = choose_terms eqs in
      let* asm_thm = assume chosen in
      let* flipped = sym asm_thm in
      let flipped_concl = Kernel.concl flipped in
      if List.mem flipped_concl asms then fail ()
      else
        let asms' = flipped_concl :: asms in
        let sub_thm = perform (Subgoal (asms', concl)) in
        prove_hyp flipped sub_thm
    in
    return_thm ~from:"sym_asm_tac" thm

let eq_true_asm_tac : tactic =
 fun (asms, concl) ->
  burn "eq_true_asm_tac" (Safe 2);
  let thm =
    let chosen = choose_terms asms in
    let* asm_thm = assume chosen in
    let* eq_t = eq_truth_intro asm_thm in
    let new_asm = Kernel.concl eq_t in
    let asms' = new_asm :: asms in
    let sub_thm = perform (Subgoal (asms', concl)) in
    prove_hyp eq_t sub_thm
  in
  return_thm ~from:"eq_true_asm_tac" thm

let eq_true_elim_asm_tac : tactic =
 fun (asms, concl) ->
  burn "eq_true_elim_asm_tac" (Safe 2);
  let thm =
    let chosen = choose_terms asms in
    let* asm_thm = assume chosen in
    let* p = eq_truth_elim asm_thm in
    let new_asm = Kernel.concl p in
    let asms' = new_asm :: asms in
    let sub_thm = perform (Subgoal (asms', concl)) in
    prove_hyp p sub_thm
  in
  return_thm ~from:"eq_true_elim_asm_tac" thm

let eq_true_elim_tac : tactic =
 fun (asms, concl) ->
  burn "eq_true_elim_tac" (Safe 2);
  let thm =
    let* l, _r = destruct_eq concl in
    let elim_thm = perform (Subgoal (asms, l)) in
    eq_truth_intro elim_thm
  in
  return_thm ~from:"eq_true_elim_tac" thm

let eq_false_elim_tac : tactic =
 fun (asms, concl) ->
  burn "eq_false_elim_tac" (Safe 2);
  let thm =
    let* l, _r = destruct_eq concl in
    let elim_thm = perform (Subgoal (asms, make_neg l)) in
    eq_false_intro elim_thm
  in
  return_thm ~from:"eq_false_elim_tac" thm

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

let rec all_var_names = function
  | Var (n, _) -> [ n ]
  | Const _ -> []
  | App (s, t) -> all_var_names s @ all_var_names t
  | Lam (bv, bod) -> all_var_names bv @ all_var_names bod

let elim_exists_asm_tac : tactic =
 fun (asms, concl) ->
  burn "elim_exists_asm_tac" (Safe 2);
  let exists_asms = List.filter is_exists asms in
  if List.is_empty exists_asms then fail ()
  else
    let thm =
      let chosen = choose_terms exists_asms in
      let* var, body = destruct_exists chosen in
      let other_asms = List.filter (( <> ) chosen) asms in
      (* Rename witness variable if it's already free in other assumptions
         or conclusion, to avoid capture when choose calls gen *)
      let avoid = concl :: other_asms in
      let used_names =
        List.concat_map all_var_names avoid |> List.sort_uniq String.compare
      in
      let var_name = match var with Var (n, _) -> n | _ -> "" in
      let needs_rename = var_name <> "" && List.mem var_name used_names in
      if needs_rename then
        let fresh_name =
          let n = ref var_name in
          while List.mem !n used_names do
            n := !n ^ "'"
          done;
          !n
        in
        let var' =
          match var with Var (_, ty) -> Var (fresh_name, ty) | _ -> var
        in
        let* body' = vsubst [ (var', var) ] body in
        let asms' = body' :: other_asms in
        let sub_thm = perform (Subgoal (asms', concl)) in
        let* exists_assumed = assume chosen in
        choose var' exists_assumed sub_thm
      else
        let asms' = body :: other_asms in
        let sub_thm = perform (Subgoal (asms', concl)) in
        let* exists_assumed = assume chosen in
        choose var exists_assumed sub_thm
    in
    return_thm ~from:"elim_exists_asm_tac" thm

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

let exists_tac : tactic =
 fun (asms, concl) ->
  burn "exists_tac" (Unsafe 8);
  let thm =
    let* x, body = destruct_exists concl in
    let chosen = choose_terms [] in
    let* chosen_sub_raw = vsubst [ (chosen, x) ] body in
    let* beta_eq = deep_beta chosen_sub_raw in
    let* chosen_sub = rhs beta_eq in
    let body_thm = perform (Subgoal (asms, chosen_sub)) in
    let* thm = exists_p x body chosen body_thm in
    trace_info
      (Printf.sprintf "success with chosen term: %s"
         (pretty_print_hol_term chosen));
    Ok thm
  in
  return_thm ~from:"exists_tac" thm

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

let rec induct_tac : tactic =
 fun (asms, concl) ->
  burn "induct_tac" (Unsafe 8);
  match destruct_forall concl with
  | Ok _ ->
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
          |> List.map (fun case ->
              ((asms, case), perform (Subgoal (asms, case))))
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
  | Error _ ->
      let thm =
        let var = choose_terms [] in
        let mentioning = List.filter (fun h -> var_free_in var h) asms in
        let discharged_concl =
          List.fold_left (fun c asm -> make_imp asm c) concl mentioning
        in
        let forall_concl = make_forall var discharged_concl in
        let non_mentioning =
          List.filter (fun h -> not (var_free_in var h)) asms
        in
        let induct_thm = induct_tac (non_mentioning, forall_concl) in
        let* specced = spec var induct_thm in
        List.fold_left
          (fun acc asm ->
            let* th = acc in
            let* assumed = assume asm in
            mp th assumed)
          (Ok specced) mentioning
      in
      return_thm ~from:"induction_tac" thm

let truth_tac : tactic =
 fun (_asms, concl) ->
  burn "truth_tac" (Safe 1);
  let t = make_true () in
  if t <> concl then (
    trace_error "goal is not T";
    fail ())
  else truth

let cases_tac : tactic =
 fun (asms, concl) ->
  burn "cases_tac" (Unsafe 8);
  let bool_case_branch var bod value asms =
    let* var_eq_val = safe_make_eq var value in
    let* bod_subst = vsubst [ (value, var) ] bod in
    let subgoal_thm = perform (Subgoal (var_eq_val :: asms, bod_subst)) in
    let* pred_lam = make_lam var bod in
    let* var_eq_val_assumed = assume var_eq_val in
    let* val_eq_var = sym var_eq_val_assumed in
    let* lam_eq = mk_comb (refl pred_lam |> Result.get_ok) val_eq_var in
    let* beta_eq = conv_equality deep_beta lam_eq in
    eq_mp beta_eq subgoal_thm
  in
  let bool_forall_cases asms var bod =
    let* bc = spec var bool_cases in
    let* case_t = bool_case_branch var bod (make_true ()) asms in
    let* case_f = bool_case_branch var bod (make_false ()) asms in
    let* result = disj_cases bc case_t case_f in
    gen var result
  in
  let bool_expr_cases asms concl tm =
    let* bc = spec tm bool_cases in
    let* tm_eq_t = safe_make_eq tm (make_true ()) in
    let* tm_eq_f = safe_make_eq tm (make_false ()) in
    let t_thm = perform (Subgoal (tm_eq_t :: asms, concl)) in
    let f_thm = perform (Subgoal (tm_eq_f :: asms, concl)) in
    disj_cases bc t_thm f_thm
  in
  let thm =
    match destruct_forall concl with
    | Ok (var, bod) ->
        let ty = type_of_var var in
        if compare ty bool_ty = 0 then bool_forall_cases asms var bod
        else Ok (induct_tac (asms, concl))
    | Error _ ->
        let tm = perform (Choose (Term [ concl ])) in
        bool_expr_cases asms concl tm
  in
  return_thm ~from:"cases_tac" thm

let destruct_tac : tactic =
 fun (asms, concl) ->
  burn "destruct_tac" (Unsafe 6);
  let thm =
    let tm = choose_terms [] in
    let* ty = type_of_term tm in
    let* ty_name, ty_args = destruct_type ty in
    let ind_def =
      match Hashtbl.find_opt the_inductives ty_name with
      | None ->
          trace_error
            (Printf.sprintf "destruct: %s is not an inductive type" ty_name);
          fail ()
      | Some d -> d
    in
    let* _, def_ty_params = destruct_type ind_def.ty in
    let type_sub = List.combine def_ty_params ty_args in
    let* typed_exhaust = inst_type type_sub ind_def.exhaustiveness in
    let* specced = spec tm typed_exhaust in
    let exhaust_fact = Kernel.concl specced in
    let sub_thm = perform (Subgoal (exhaust_fact :: asms, concl)) in
    prove_hyp specced sub_thm
  in
  return_thm ~from:"destruct_tac" thm

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

let ( >>>> ) = then_all

let then_all_direct (tac1 : tactic) : tactic_combinator =
 fun tac goal ->
  let depth = ref 0 in
  let rec handler f =
    match f () with
    | effect Subgoal g, k when !depth = 0 ->
        let r = Multicont.Deep.promote k in
        incr depth;
        let thm : thm = handler (fun () -> tac g) in
        decr depth;
        handler (fun () -> Multicont.Deep.resume r thm)
    | effect Subgoal g, k when !depth > 0 ->
        (* Re-emit for the outer handler *)
        let r = Multicont.Deep.promote k in
        let thm : thm = perform (Subgoal g) in
        handler (fun () -> Multicont.Deep.resume r thm)
    | v -> v
  in
  handler (fun () -> tac1 goal)

let ( >>> ) = then_all_direct

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

let with_first : tactic_combinator =
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

let with_arbitrary_term (t : term) : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Choose (Term _), k -> continue k t | x -> x

let with_term (t : term) : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Choose (Term terms), k ->
      if List.mem t terms then continue k t else fail ()
  | x -> x

let cond_tac : tactic =
 fun (asms, concl) ->
  let rec collect_cond_args tm acc =
    match tm with
    | App (App (App (Const ("COND", _), b), t), e) ->
        let acc = collect_cond_args b acc in
        let acc = collect_cond_args t acc in
        collect_cond_args e (b :: acc)
    | App (f, x) ->
        let acc = collect_cond_args f acc in
        collect_cond_args x acc
    | Lam (_, body) -> collect_cond_args body acc
    | _ -> acc
  in
  let cond_args = collect_cond_args concl [] in
  match cond_args with
  | [] ->
      trace_error "no COND expressions found in goal";
      fail ()
  | terms ->
      let tm = choose_terms terms in
      with_arbitrary_term tm cases_tac (asms, concl)

let try_ : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Fail, _ -> perform (Subgoal goal) | v -> v

let pick_tac (tacs : tactic list) : tactic =
 fun goal ->
  let tac = choose_tactics tacs in
  tac goal

let solve : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Subgoal _g', _k -> fail () | v -> v

let run_thunk_with_path (path : string list ref) (thunk : unit -> 'a) : 'a =
  let rec loop f =
    match f () with
    | effect Trace (Proof, name), k ->
        path := name :: !path;
        loop (fun () -> continue k ())
    | v -> v
  in
  loop thunk

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

let with_best_first : tactic_combinator = make_search (module PQueueFrontier)

module QueueFrontier : Frontier = struct
  type t = Priority.t Queue.t

  let create () = Queue.create ()
  let pop = Queue.take_opt
  let add q x = Queue.add x q
  let stats (s : t) = s |> Queue.to_seq |> List.of_seq |> stats_of_list
end

let with_bfs : tactic_combinator = make_search (module QueueFrontier)

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

let ctauto_dfs_tac : tactic = with_dfs ctauto_tac

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

let with_nth_choice n : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Choose cs, k -> (
      match List.nth_opt (as_chosen_list cs) n with
      | None -> fail ()
      | Some c -> continue k c)
  | v -> v

let with_nth_term n : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Choose (Term ts), k -> (
      match List.nth_opt ts n with None -> fail () | Some c -> continue k c)
  | v -> v

let with_term_size_ranking : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Rank (Term terms), k ->
      let sorted =
        List.stable_sort (fun l r -> compare (term_size l) (term_size r)) terms
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

let with_fuel_limit' (limit : int) : tactic_combinator =
  let fuel = ref limit in
  fun tac goal ->
    match tac goal with
    | effect Burn (name, cost), k ->
        let n = cost_value cost in
        fuel := !fuel - n;
        if !fuel <= 0 then fail ()
        else (
          burn name cost;
          continue k ())
    | v -> v

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

let with_fuel_counter r : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Burn (name, cost), k ->
      r := !r + cost_value cost;
      burn name cost;
      continue k ()
  | v -> v

let show_tac : tactic =
 fun goal ->
  print_endline "Current subgoal:";
  List.iter print_term (fst goal);
  print_endline "-------------------------";
  print_term @@ snd goal;
  fail ()

let with_show_subgoal : tactic_combinator =
 fun tac goal ->
  print_endline "Current subgoal:";
  List.iter print_term (fst goal);
  print_endline "-------------------------";
  print_term @@ snd goal;
  tac goal

let with_info_trace : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Trace (Info, t), k ->
      print_endline t;
      continue k ()
  | v -> v

let with_no_automation_trace : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Trace (Search, _), k -> continue k () | v -> v

let with_no_trace ?(show_proof = false) : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Trace (Info, _), k -> continue k ()
  | effect Trace (Debug, _), k -> continue k ()
  | effect Trace (Error, _), k -> continue k ()
  | effect Trace (Warn, _), k -> continue k ()
  | effect Trace (Proof, _), k when not show_proof -> continue k ()
  | v -> v

let with_assumptions : tactic_combinator =
 fun tac (asms, concl) ->
  let asm_thms =
    List.filter_map
      (fun asm -> match assume asm with Ok thm -> Some thm | Error _ -> None)
      asms
  in
  match tac (asms, concl) with effect Rules, k -> continue k asm_thms | v -> v

let with_rules (rules : thm list) : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Rules, k -> continue k rules | v -> v

let with_flip_rules : tactic_combinator =
 fun tac goal ->
  let rules = perform Rules in
  let flipped =
    List.filter_map
      (fun r ->
        let r' =
          let* stripped = strip_forall r in
          sym stripped
        in
        Result.to_option r')
      rules
  in
  match tac goal with effect Rules, k -> continue k flipped | v -> v

let with_rule (rule : thm) : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Rules, k -> continue k [ rule ] | v -> v

let with_definition (names : string list) : tactic_combinator =
  let rules =
    names
    |> List.map (fun n ->
        match Rules.get_def n with
        | None ->
            trace_error (Printf.sprintf "Couldn't find def with name %s\n" n);
            fail ()
        | Some rule -> Rewrite.rules_of_def rule)
    |> List.filter_map Result.to_option
    |> List.flatten
  in
  fun tac goal ->
    match tac goal with effect Rules, k -> continue k rules | v -> v

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

let intros_tac : tactic =
 fun goal -> with_repeat (with_first (pick_tac [ intro_tac; gen_tac ])) goal

let simp_tac ?(exclude = []) ?(with_asms = true) : tactic =
 fun goal ->
  let add = perform Rules in
  let definitions =
    !Rules.definitions
    |> List.filter (fun (n, _) -> not @@ List.mem n exclude)
    |> List.map snd
  in
  let simps =
    !Rules.simps
    |> List.filter (fun (n, _) -> not @@ List.mem n exclude)
    |> List.map snd
  in
  let rules =
    definitions |> List.append add |> List.append simps
    |> List.filter_map (fun d -> Result.to_option @@ rules_of_def d)
    |> List.flatten
  in

  let with_rw = if with_asms then with_rules_and_assumptions else with_rules in

  let thm =
    with_repeat
      (with_first
      @@ pick_tac
           [
             with_rw rules rewrite_tac;
             with_repeat beta_tac;
             refl_tac;
             truth_tac;
           ])
      goal
  in
  thm

let auto_tac : tactic =
  pick_tac
    [
      simp_tac ~with_asms:true;
      gen_tac;
      intro_tac;
      truth_tac;
      assumption_tac;
      neg_intro_tac;
      conj_tac;
      elim_conj_asm_tac;
      elim_exists_asm_tac;
      false_elim_tac;
      mp_asm_tac;
    ]

let auto_dfs_tac : tactic =
 fun goal ->
  let thm = with_dfs auto_tac goal in
  return_thm ~from:"auto_dfs_tac" (Ok thm)

let simp_asm_tac ?(exclude = []) ?(with_asms = true) ?(add = []) : tactic =
 fun goal ->
  let extra = perform Rules in
  let definitions =
    !Rules.definitions
    |> List.filter (fun (n, _) -> not @@ List.mem n exclude)
    |> List.map snd
  in
  let simps =
    !Rules.simps
    |> List.filter (fun (n, _) -> not @@ List.mem n exclude)
    |> List.map snd
  in
  let rules =
    definitions |> List.append extra |> List.append simps |> List.append add
    |> List.filter_map (fun d -> Result.to_option @@ rules_of_def d)
    |> List.flatten
  in

  let with_rw = if with_asms then with_rules_and_assumptions else with_rules in

  let thm =
    with_repeat
      (with_first
      @@ pick_tac
           [
             with_rw rules rewrite_asm_tac;
             with_repeat beta_asm_tac;
             assumption_tac;
           ])
      goal
  in
  thm

let with_synthetic_term ?(extra = []) (depth : int) : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Choose (Term _), k ->
      let r = Multicont.Deep.promote k in
      let ty = type_of_existential goal |> Result.get_ok in
      let terms = Synth.enumerate ~extra [] ty depth in
      trace_info
        (Printf.sprintf "enumerated %d unique terms" (List.length terms));

      List.iter
        (fun t ->
          trace_dbg (Printf.sprintf "term: %s" (pretty_print_hol_term t)))
        terms;
      let t = choose_terms (List.rev terms) in
      trace_info (Printf.sprintf "chose synth: %s" (pretty_print_hol_term t));
      Multicont.Deep.resume r t
  | v -> v

let run_proof ?(pretty = false) ?(notrace = true) ?(name = "") ?(simp = false)
    ?(quiet = false) goal tac =
  let fuel_count = ref 0 in
  let limit = ref 1_000_000 in
  let wrapped =
    (if notrace then with_no_trace ~show_proof:false else Fun.id)
    @@ (with_fuel_limit limit) (with_fuel_counter fuel_count tac)
  in
  match prove ~name goal wrapped with
  | Complete thm ->
      if simp then Rules.add_simp name thm;
      if not quiet then (
        print_thm ~pretty thm;
        print_endline "Proof Complete!";
        Printf.printf "with fuel: %d\n" !fuel_count)
  | Incomplete (asms, c) ->
      if not quiet then (
        List.iter (print_term ~pretty) asms;
        print_endline "--------------";
        print_term ~pretty c;
        print_endline "Proof Incomplete";
        Printf.printf "with fuel: %d\n" !fuel_count)
