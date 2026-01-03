open Kernel
open Derived
open Effect
open Effect.Deep

type goal = term list * term [@@deriving show]
type level = Debug | Info | Warn | Error
type _ Effect.t += Subgoal : goal -> thm Effect.t
type _ Effect.t += Fail : 'a Effect.t
type _ Effect.t += Trace : (level * string) -> unit Effect.t

let print_kerror e = print_endline @@ show_kernel_error e
let fail () = perform Fail
let trace_dbg a = perform (Trace (Debug, a))
let trace_error a = perform (Trace (Error, a))

let assumption_tac (asms, concl) =
  if List.mem concl asms then (
    trace_dbg "Found matching assumption";
    match assume concl with
    | Ok thm ->
        trace_dbg "Assumption succeeded";
        thm
    | Error e ->
        trace_error (show_kernel_error e);
        fail ())
  else (trace_error "goal not in assumptions"; fail ())

let conj_tac : goal -> thm =
 fun (asms, concl) ->
  try
    let l, r = destruct_conj concl in
    trace_dbg "Destruct succeeded";
    let lthm = perform (Subgoal (asms, l)) in
    trace_dbg "left proved";
    let rthm = perform (Subgoal (asms, r)) in
    trace_dbg "right proved";
    match conj lthm rthm with
    | Ok thm ->
        trace_dbg "conj success";
        thm
    | Error e ->
        trace_error (show_kernel_error e);
        fail ()
  with _ ->
    trace_error "failed to destruct";
    fail ()

type proof_state = Incomplete of goal | Complete of thm [@@deriving show]

let rec prove g next_tactic =
  match next_tactic () with
  | None -> Incomplete g
  | Some tactic -> (
      match tactic g with
      | effect (Trace (_, v)), k -> print_endline v; continue k ()
      | effect Fail, _k -> Incomplete g
      | effect Subgoal g', k -> (
          match prove g' next_tactic with
          | Complete thm -> continue k thm
          | incomplete -> incomplete)
      | thm -> Complete thm)

let next_tactic_of_list l =
  let q = Queue.of_seq (List.to_seq l) in
  fun () -> Queue.take_opt q
