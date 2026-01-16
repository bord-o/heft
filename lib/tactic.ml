open Kernel
open Derived
open Printing
open Effect
open Effect.Deep
open Result.Syntax

type goal = term list * term [@@deriving show]
type level = Debug | Info | Warn | Error
type proof_state = Incomplete of goal | Complete of thm [@@deriving show]

type _ Effect.t +=
  | Subgoal : goal -> thm Effect.t
  | Choose : 'a list -> 'a Effect.t
  | Rank : term list -> term list Effect.t
  | Fail : 'a Effect.t
  | Trace : (level * string) -> unit Effect.t
  | TacticQueue : (goal -> thm) Queue.t Effect.t

let fail () = perform Fail
let trace_dbg a = perform (Trace (Debug, a))
let trace_info a = perform (Trace (Info, a))
let trace_error a = perform (Trace (Error, a))

let return_thm = function
  | Ok thm -> thm
  | Error e ->
      trace_error @@ print_error e;
      fail ()

let rec choose_subgoals acc = function
  | [] -> List.rev acc
  | goals ->
      (goals
      |> List.iteri @@ fun idx g ->
         trace_info (string_of_int idx ^ ": " ^ pretty_print_hol_term (snd g));
         ());
      let chosen = perform (Choose goals) in
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
  return_thm thm

let right_tac (asms, concl) =
  let thm =
    let* l = side_of_op "\\/" Left concl in
    let* r = side_of_op "\\/" Right concl in
    let r_thm = perform (Subgoal (asms, r)) in
    let t = disj_right r_thm l in
    trace_dbg "disj_right success";
    t
  in
  return_thm thm

let or_tac (asms, concl) =
  let tac = perform (Choose [ left_tac; right_tac ]) in
  tac (asms, concl)

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
  let h = perform (Choose premises) in
  let chosen = matching |> List.assoc h in

  let thm =
    let* assumed = assume chosen in
    trace_dbg "assume chosen h success";
    let sub_thm = perform (Subgoal (asms, h)) in
    let thm = mp assumed sub_thm in
    trace_dbg "mp success";
    thm
  in
  return_thm thm

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
  return_thm thm

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
  return_thm thm

let assumption_tac (asms, concl) =
  let asm = perform (Choose asms) in
  if concl <> asm then (
    trace_error "assumption doesn't match the goal";
    fail ())
  else (
    trace_dbg "Found matching assumption";
    let t = assume concl in
    trace_dbg "Assumption succeeded";
    return_thm t)

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
  return_thm thm

let elim_conj_asm_tac (asms, concl) =
  let conjs = List.filter is_conj asms in
  if List.is_empty conjs then fail ()
  else
    let thm =
      let chosen = perform (Choose conjs) in
      let* l, r = destruct_conj chosen in
      let asms' = l :: r :: List.filter (( <> ) chosen) asms in
      let sub_thm = perform (Subgoal (asms', concl)) in
      let* conj_asm = assume chosen in
      let* l_thm = conj_left conj_asm in
      let* r_thm = conj_right conj_asm in
      let* p_1 = prove_hyp r_thm sub_thm in
      prove_hyp l_thm p_1
    in
    return_thm thm

let contr_tac : goal -> thm =
 fun (asms, concl) ->
  let thm =
    let false_tm = make_false () in
    let fthm = perform (Subgoal (asms, false_tm)) in
    let* thm = contr concl fthm in
    Ok thm
  in
  return_thm thm

let gen_tac : goal -> thm =
 fun (asms, concl) ->
  let thm =
    let* x, body = destruct_forall concl in
    let body_thm = perform (Subgoal (asms, body)) in
    let* thm = gen x body_thm in
    Ok thm
  in
  return_thm thm

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
  return_thm thm

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
          match choices with
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
        let thm = aux g in
        continue k thm
    | thm -> thm
  in
  aux

let rec prove_dfs g tactic_queue =
  match Queue.take_opt tactic_queue with
  | None ->
      print_endline "Out of tactics";
      Incomplete g
  | Some tactic ->
      let rec handler (f : unit -> proof_state) =
        match f () with
        | effect TacticQueue, k -> continue k tactic_queue
        | effect Trace (_, v), k ->
            print_endline v;
            continue k ()
        | effect Rank terms, k -> continue k terms
        | effect Fail, _k -> Incomplete g
        | effect Choose choices, k ->
            let r = Multicont.Deep.promote k in
            let rec try_each = function
              | [] -> Incomplete g
              | c :: cs ->
                  let t =
                    match handler @@ fun () -> Multicont.Deep.resume r c with
                    | Complete thm -> Complete thm
                    | Incomplete _ -> try_each cs
                  in
                  t
            in
            try_each choices
        | effect Subgoal g', k -> (
            match prove_dfs g' (Queue.copy tactic_queue) with
            | Complete thm -> continue k thm
            | incomplete -> incomplete)
        | thm -> thm
      in
      handler (fun () -> Complete (tactic g))

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
      try_each choices
  | v -> v

let with_interactive_choice tac =
 fun goal ->
  match tac goal with
  | effect Trace (_, s), k ->
      print_endline s;
      continue k ()
  | effect Choose choices, k ->
      if List.is_empty choices then fail ()
      else
        let rec get_choice cs =
          let idx = read_int () in
          match List.nth_opt cs idx with
          | Some c -> c
          | None ->
              print_endline "Invalid choice";
              get_choice cs
        in
        continue k (get_choice choices)
  | v -> v

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

let with_no_trace tac =
 fun goal -> match tac goal with effect Trace _, k -> continue k () | v -> v
