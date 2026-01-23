open Kernel
open Derived
open Printing
open Effect
open Effect.Deep
open Result.Syntax

type goal = term list * term [@@deriving show]
type level = Debug | Info | Warn | Error | Proof
type proof_state = Incomplete of goal | Complete of thm [@@deriving show]
type tactic = goal -> thm

type _ choosable =
  | Term : term list -> term choosable
  | Goal : goal list -> goal choosable
  | Tactic : tactic list -> tactic choosable
  | Unknown : 'a list -> 'a choosable

type _ Effect.t +=
  | Subgoal : goal -> thm Effect.t
  | Choose : 'a choosable -> 'a Effect.t
  | Rank : term list -> term list Effect.t
  | Fail : 'a Effect.t
  | Trace : (level * string) -> unit Effect.t
  | TacticQueue : (goal -> thm) Queue.t Effect.t

let as_list : type a. a choosable -> a list = function
  | Term ts -> ts
  | Goal gs -> gs
  | Tactic tacs -> tacs
  | Unknown xs -> xs

let fail () = perform Fail
let trace_dbg a = perform (Trace (Debug, a))
let trace_info a = perform (Trace (Info, a))
let trace_error a = perform (Trace (Error, a))
let trace_proof a = perform (Trace (Proof, a))

let return_thm ?(from = "unknown") = function
  | Ok thm ->
      perform (Trace (Proof, from));
      thm
  | Error e ->
      trace_error @@ print_error e;
      fail ()

let choose_goals gs = perform (Choose (Goal gs))
let choose_terms gs = perform (Choose (Term gs))
let choose_tactics gs = perform (Choose (Tactic gs))
let choose_unknowns gs = perform (Choose (Unknown gs))

let rec choose_subgoals acc = function
  | [] -> List.rev acc
  | goals ->
      (goals
      |> List.iteri @@ fun idx g ->
         trace_info (string_of_int idx ^ ": " ^ pretty_print_hol_term (snd g));
         ());
      let chosen = perform @@ Choose (Goal goals) in

      let thm = perform (Subgoal chosen) in
      let rest = List.filter (( <> ) chosen) goals in
      choose_subgoals ((chosen, thm) :: acc) rest

let wrap_all handler = List.map @@ fun t -> handler t

let left_tac (asms, concl) =
  let thm =
    let* l = side_of_op "\\/" Left concl in
    let* r = side_of_op "\\/" Right concl in
    let l_thm = perform (Subgoal (asms, l)) in
    let t = disj_left r l_thm in
    trace_dbg "disj_left success";
    t
  in
  return_thm ~from:"left_tac" thm

let right_tac (asms, concl) =
  let thm =
    let* l = side_of_op "\\/" Left concl in
    let* r = side_of_op "\\/" Right concl in
    let r_thm = perform (Subgoal (asms, r)) in
    let t = disj_right r_thm l in
    trace_dbg "disj_right success";
    t
  in
  return_thm ~from:"right_tac" thm

let or_tac (asms, concl) =
  let tac = choose_tactics [ left_tac; right_tac ] in
  let thm = Ok (tac (asms, concl)) in
  return_thm ~from:"or_tac" thm

let apply_tac (asms, concl) =
  (* Find implications in the asms that match the conclusion *)
  let matching =
    asms
    |> List.filter_map (fun asm ->
        match destruct_imp asm with
        | Ok (prem, conc) when conc = concl -> Some (prem, asm)
        | _ -> None)
  in

  let premises = perform (Rank (List.map fst matching)) in
  let h = choose_terms premises in
  let chosen = matching |> List.assoc h in

  let thm =
    let* assumed = assume chosen in
    trace_dbg "assume chosen h success";
    let sub_thm = perform (Subgoal (asms, h)) in
    let thm = mp assumed sub_thm in
    trace_dbg "mp success";
    thm
  in
  return_thm ~from:"apply_tac" thm

let apply_neg_tac : goal -> thm =
 fun (asms, concl) ->
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
      return_thm ~from:"apply_neg_tac" thm

let mp_asm_tac : goal -> thm =
 fun (asms, concl) ->
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

let intro_tac (asms, concl) =
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

let refl_tac (_asms, concl) =
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

let assumption_tac (asms, concl) =
  let asm = choose_terms asms in
  if concl <> asm then (
    trace_error "assumption doesn't match the goal";
    fail ())
  else (
    trace_dbg "Found matching assumption";
    let t = assume concl in
    trace_dbg "Assumption succeeded";
    return_thm ~from:"assumption_tac" t)

let conj_tac : goal -> thm =
 fun (asms, concl) ->
  let thm =
    let* l, r = destruct_conj concl in
    trace_dbg "Destruct succeeded";

    let goals = [ (asms, l); (asms, r) ] in
    let solved = choose_subgoals [] goals in
    let lthm = solved |> List.assoc (asms, l) in
    let rthm = solved |> List.assoc (asms, r) in

    let* thm = conj lthm rthm in

    trace_dbg "conj success";
    Ok thm
  in
  return_thm ~from:"conj_tac" thm

let elim_disj_asm_tac : goal -> thm =
 fun (asms, concl) ->
  let disjs = List.filter is_disj asms in
  if List.is_empty disjs then fail ()
  else
    let thm =
      let chosen = choose_terms disjs in
      let* l, r = destruct_disj chosen in
      let asms' = List.filter (( <> ) chosen) asms in

      let left_goal = (l :: asms', concl) in
      let right_goal = (r :: asms', concl) in
      let goals = [ left_goal; right_goal ] in

      let solved = choose_subgoals [] goals in
      let left_thm = solved |> List.assoc left_goal in
      let right_thm = solved |> List.assoc right_goal in

      let* disj_asm = assume chosen in
      disj_cases disj_asm left_thm right_thm
    in
    return_thm ~from:"elim_disj_asm_tac" thm

let elim_conj_asm_tac (asms, concl) =
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

let neg_elim_tac : goal -> thm =
 fun (asms, concl) ->
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

let neg_intro_tac : goal -> thm =
 fun (asms, concl) ->
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

let ccontr_tac : goal -> thm =
 fun (asms, concl) ->
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

let false_elim_tac : goal -> thm =
 fun (asms, concl) ->
  let false_tm = make_false () in
  if List.mem false_tm asms then
    let thm =
      let* false_thm = assume false_tm in
      contr concl false_thm
    in
    return_thm ~from:"false_elim_tac" thm
  else fail ()

let gen_tac : goal -> thm =
 fun (asms, concl) ->
  let thm =
    let* x, body = destruct_forall concl in
    let body_thm = perform (Subgoal (asms, body)) in
    let* thm = gen x body_thm in
    Ok thm
  in
  return_thm ~from:"gen_tac" thm

(* 
   need to fetch the appropriate induction definition of the type we are 
   inducting on (the general var)
 *)
let induct_tac : goal -> thm =
 fun (asms, concl) ->
  let thm =
    let* induction_var, bod = destruct_forall concl in
    let* ty = type_of_term induction_var in
    let* ty_name, _ = destruct_type ty in

    let inductive_def =
      match Hashtbl.find_opt the_inductives ty_name with
      | None ->
          trace_error "quantified type is not an inductive";
          fail ()
      | Some d -> d
    in

    let binder = make_var "pred_binder" ty in
    let* p = make_lam binder bod in

    let* inst_induction = spec p inductive_def.induction in
    (* print_endline @@ pretty_print_thm ~with_type:true inductive_def.induction; *)

    (*TODO this all needs to be a loop to account for multiple cases*)
    let* base_case, rest = destruct_imp (Kernel.concl inst_induction) in
    let* inductive_case, _ = destruct_imp rest in
    let thms =
      choose_subgoals [] [ (asms, base_case); (asms, inductive_case) ]
    in
    let base_thm = thms |> List.assoc (asms, base_case) in
    let ind_thm = thms |> List.assoc (asms, inductive_case) in

    let* base_sat = mp inst_induction base_thm in
    let* thm = mp base_sat ind_thm in

    Ok thm
  in
  return_thm ~from:"induction_tac" thm

(* Complete automation for propositional logic goals *)
let pauto_tac : goal -> thm =
 fun goal ->
  let tac =
    choose_tactics
      [
        assumption_tac;
        intro_tac;
        neg_intro_tac;
        conj_tac;
        elim_conj_asm_tac;
        elim_disj_asm_tac;
        false_elim_tac;
        neg_elim_tac;
        apply_tac;
        apply_neg_tac;
        mp_asm_tac;
        left_tac;
        right_tac;
        ccontr_tac;
      ]
  in
  tac goal

(* 
   As a general rule, custom handlers should handle the least amount of 
   effects possible. The main handler captures all effects, but implements only basic
   interpretations of them.
*)
let rec prove g tactic_queue =
  match Queue.take_opt tactic_queue with
  | None ->
      print_endline "Out of tactics";
      Incomplete g
  | Some tactic -> (
      match tactic g with
      (* TacticQueue gives the current tactics waiting to be applied *)
      | effect TacticQueue, k -> continue k tactic_queue
      (* Trace is a unified interface for logs and errors *)
      | effect Trace (_, v), k ->
          print_endline v;
          continue k ()
      (* Rank is used to sort terms by an undetermined heuristic *)
      | effect Rank terms, k -> continue k terms
      (* This represents failure for any reason *)
      | effect Fail, _k -> Incomplete g
      (* Choose is used to decide how to explore options *)
      | effect Choose choices, k -> (
          match as_list choices with
          | [] ->
              print_endline "no choices available";
              Incomplete g
          | c :: _ -> continue k c)
      (* Subgoal is used for branching the proof state *)
      | effect Subgoal g', k -> (
          match prove g' tactic_queue with
          | Complete thm -> continue k thm
          | incomplete -> incomplete)
      (* When a proof is complete we extract the theorem *)
      | thm -> Complete thm)

let with_skip_fail tac =
 fun goal ->
  match tac goal with effect Fail, _ -> perform (Subgoal goal) | thm -> thm

let with_repeat tac =
  let rec aux (asms, concl) =
    match tac (asms, concl) with
    | effect Fail, _ -> perform (Subgoal (asms, concl))
    | effect Subgoal g, k ->
        let r = Multicont.Deep.promote k in
        let thm = aux g in
        (* idk man *)
        Multicont.Deep.resume r thm
    | thm -> thm
  in
  aux

let rec prove_dfs_traced g tactic_queue trace_ref =
  match Queue.take_opt tactic_queue with
  | None -> Incomplete g
  | Some tactic ->
      let rec handler (f : unit -> proof_state) =
        match f () with
        | effect TacticQueue, k -> continue k tactic_queue
        | effect Trace (Proof, v), k ->
            trace_ref := v :: !trace_ref;
            continue k ()
        | effect Trace (_, v), k ->
            print_endline v;
            continue k ()
        | effect Rank terms, k -> continue k terms
        | effect Fail, _k -> Incomplete g
        | effect Choose choices, k ->
            let r = Multicont.Deep.promote k in
            let rec try_each = function
              | [] -> Incomplete g
              | c :: cs -> (
                  let snapshot = !trace_ref in
                  let result = handler (fun () -> Multicont.Deep.resume r c) in
                  match result with
                  | Complete thm -> Complete thm
                  | Incomplete _ ->
                      trace_ref := snapshot;
                      try_each cs)
            in
            try_each (as_list choices)
        | effect Subgoal g', k -> (
            match prove_dfs_traced g' (Queue.copy tactic_queue) trace_ref with
            | Complete thm -> continue k thm
            | incomplete -> incomplete)
        | thm -> thm
      in
      handler (fun () -> Complete (tactic g))

let prove_dfs g tactic_queue =
  let trace_ref = ref [] in
  prove_dfs_traced g tactic_queue trace_ref

let prove_dfs_with_trace g tactic_queue =
  let trace_ref = ref [] in
  let result = prove_dfs_traced g tactic_queue trace_ref in
  (!trace_ref, result)

let next_tactic_of_list l =
  let q = Queue.of_seq (List.to_seq l) in
  q

(* this only trys choices at one level, for actual dfs we need a full handler *)
let with_first_success tac =
 fun goal ->
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
      try_each (as_list choices)
  | v -> v

let with_interactive_choice tac =
 fun goal ->
  match tac goal with
  | effect Trace (_, s), k ->
      print_endline s;
      continue k ()
  | effect Choose choices, k ->
      if List.is_empty (as_list choices) then fail ()
      else
        let rec get_choice cs =
          let idx = read_int () in
          match List.nth_opt cs idx with
          | Some c -> c
          | None ->
              print_endline "Invalid choice";
              get_choice cs
        in
        continue k (get_choice (as_list choices))
  | v -> v

let with_nth_choice n tac =
 fun goal ->
  match tac goal with
  | effect Choose cs, k -> (
      match List.nth_opt (as_list cs) n with
      | None -> fail ()
      | Some c -> continue k c)
  | v -> v

let with_term_choice (t : term) tac =
 fun goal ->
  match tac goal with
  | effect Choose (Term terms), k ->
      if List.mem t terms then continue k t else fail ()
  | x -> x

let with_term_size_ranking tac =
  let rec term_size (t : term) =
    match t with
    | Var (_, _) -> 1
    | Const (_, _) -> 1
    | App (l, r) -> 1 + term_size l + term_size r
    | Lam (bind, bod) -> 1 + term_size bind + term_size bod
  in
  fun goal ->
    match tac goal with
    | effect Rank terms, k ->
        let sorted =
          List.stable_sort
            (fun l r -> compare (term_size l) (term_size r))
            terms
        in
        continue k sorted
    | v -> v

let with_no_trace ?(show_proof = false) tac =
 fun goal ->
  match tac goal with
  | effect Trace (Info, _), k -> continue k ()
  | effect Trace (Debug, _), k -> continue k ()
  | effect Trace (Error, _), k -> continue k ()
  | effect Trace (Warn, _), k -> continue k ()
  | effect Trace (Proof, _), k when not show_proof -> continue k ()
  | v -> v
