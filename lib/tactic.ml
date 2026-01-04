open Kernel
open Derived
open Printing
open Effect
open Effect.Deep
open Result.Syntax

type goal = term list * term [@@deriving show]
type level = Debug | Info | Warn | Error

type _ Effect.t +=
  | Subgoal : goal -> thm Effect.t
  | Choose : 'a list -> 'a Effect.t
  | Fail : 'a Effect.t
  | Trace : (level * string) -> unit Effect.t
  | Rank : term list -> term list Effect.t

let fail () = perform Fail
let trace_dbg a = perform (Trace (Debug, a))
let trace_error a = perform (Trace (Error, a))

let return_thm = function
  | Ok thm -> thm
  | Error e ->
      trace_error @@ print_error e;
      fail ()

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
  if not @@ List.mem concl asms then (
    trace_error "goal not in assumptions";
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
    let lthm = perform (Subgoal (asms, l)) in
    trace_dbg "left proved";
    let rthm = perform (Subgoal (asms, r)) in
    trace_dbg "right proved";
    let* thm = conj lthm rthm in
    trace_dbg "conj success";
    Ok thm
  in
  return_thm thm

type proof_state = Incomplete of goal | Complete of thm [@@deriving show]

let rec prove g next_tactic =
  match next_tactic () with
  | None -> Incomplete g
  | Some tactic -> (
      match tactic g with
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
              trace_error "no choices available";
              fail ()
          | c :: _ -> continue k c)
      (* Subgoal is used for branching the proof state *)
      | effect Subgoal g', k -> (
          match prove g' next_tactic with
          | Complete thm -> continue k thm
          | incomplete -> incomplete)
      (* When a proof is complete we extract the theorem *)
      | thm -> Complete thm)

let next_tactic_of_list l =
  let q = Queue.of_seq (List.to_seq l) in
  fun () -> Queue.take_opt q

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
