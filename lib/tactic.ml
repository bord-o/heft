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
  | Fail : 'a Effect.t
  | Trace : (level * string) -> unit Effect.t

let fail () = perform Fail
let trace_dbg a = perform (Trace (Debug, a))
let trace_error a = perform (Trace (Error, a))

let return_thm = function
  | Ok thm -> thm
  | Error e ->
      trace_error @@ print_error e;
      fail ()

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
      | effect Trace (_, v), k ->
          print_endline v;
          continue k ()
      | effect Fail, _k -> Incomplete g
      | effect Subgoal g', k -> (
          match prove g' next_tactic with
          | Complete thm -> continue k thm
          | incomplete -> incomplete)
      | thm -> Complete thm)

let next_tactic_of_list l =
  let q = Queue.of_seq (List.to_seq l) in
  fun () -> Queue.take_opt q
