open Kernel
open Printing
open Multicont.Deep
open Tactic
open Effect

type _ t += CurrentProb : float t
(*
Proof search with a flat fontier

what is a node?
    Right now a node is a suspended computation, marking a subgoal, concrete choice, or completed theorem

what does it mean to expand a node?
    Run it and serialize the effects into new nodes
    This implies that a node is an effect producing thunk, aka fun () -> tactic + goal  or maybe fun () -> resume k data
    In order to have value in arbitrary choices as nodes, I would need a way to actually rank them.
        Is there a case where we can say a choice resumption is better than a tactic resumption?

how do I control commit vs backtrack? Do I need to?

where is it meaningful to suspend computation, vs eagerly trying all choices?
    Is there ever a case whre I need to actually prioritize a term choice over a subgoal or something?
    Abstractly it seems like this might be a good thing, as tactics can progress in parallel, but when would I want to
        say stop halfway through this tactic, and try the other easy ones, then switch back?
        Maybe an experiment where nodes are only subgoals would make sense to try it out

is fuel a useful concept, is depth of tactic application better?

Do I need to track which rapp each node came from? 

Main idea: capture what a human would do by exposing each choice point to the search algorithm

Maybe the list of tactics should be an argument to the search rather than just a tactic itself?

inputs:
    tactic
    goal

Problems so far:
    Small changes to ordering make drastic changes in fuel
    Search can get stuck with dfs and bfs uses more fuel
    Already resumed continuation errors around simp

An experiment:
    Nodes are tactic*goal
    inter tactic choices are tagged with the node they originated from, and their priority is tied to that node so they get solved first

going to need:

type node
expand : tactic -> goal -> node

search : node queue -> tactic -> goal -> thm
 *)

let prob_of_tactic (tac : tactic) (goal : goal) =
  match tac goal with
  | effect Register info, _k -> (info.name, info.prob)
  | _ -> failwith "Register must be first call of tactic"

(** an expansion represents the search space. An edge is a potential tactic*goal
    combo to expand, and a choice is any other choice *)
type expansion =
  | Edge of string
  | Choice of string
  | Done of thm
      [@printer fun fmt t -> Format.fprintf fmt "%s" (pretty_print_thm t)]
[@@deriving show]

let thm_of_expansion = function Done thm -> Some thm | _ -> None

type node = {
  root_tactic : tactic; [@printer fun fmt _ -> Format.fprintf fmt "<tactic>"]
  down : (unit -> node list) option;
  up : (thm -> node list) option;
  expansion : expansion;
  goal : goal;
      [@printer
        fun fmt (_, conc) ->
          Format.fprintf fmt "%s" (pretty_print_hol_term conc)]
  id : Uuidm.t; [@opaque]
  prob : float;
}
[@@deriving show]
(** A node has an expansion type as well as some other data. *)

let uuid = Uuidm.v4_gen (Random.State.make_self_init ())
let test_id = uuid ()

module Priority = struct
  type t = node

  let compare : t -> t -> int = fun n1 n2 -> compare n1.prob n2.prob
end

module Frontier = Pqueue.MakeMax (Priority)

let make_node ?down ?up root_tactic goal id prob expansion =
  { down; up; expansion; id; goal; root_tactic; prob }

(** Wrap a thunk so that any CurrentProb requests inside it (including those
    from reinstalled deep handlers) receive [prob]. Because this is a deep
    handler, it reinstalls itself on each resume, so every request gets the same
    value without any extra plumbing. *)
let with_prob (prob : float) thunk =
  match thunk () with
  | effect CurrentProb, k -> resume (promote k) prob
  | v -> v

let rec expand dead (node : node) =
  with_prob node.prob (fun () ->
      match node.down with
      | Some r -> r ()
      | None -> (
          match node.root_tactic node.goal with
          | effect Choose cs, k -> (
              let r = Multicont.Deep.promote k in
              match cs with
              | Term ts ->
                  ts
                  |> List.concat_map (fun t ->
                      expand dead
                        (make_node
                           ~down:(fun () -> resume r t)
                           node.root_tactic node.goal node.id
                           (perform CurrentProb)
                           (Choice (pretty_print_hol_term t))))
              | Theorem ts ->
                  ts
                  |> List.concat_map (fun t ->
                      expand dead
                        (make_node
                           ~down:(fun () -> resume r t)
                           node.root_tactic node.goal node.id
                           (perform CurrentProb)
                           (Choice (pretty_print_hol_term (concl t)))))
              | Unknown us ->
                  us
                  |> List.concat_map (fun u ->
                      expand dead
                        (make_node
                           ~down:(fun () -> resume r u)
                           node.root_tactic node.goal node.id
                           (perform CurrentProb) (Choice "unknown")))
              | Tactic ts ->
                  ts
                  |> List.map (fun t ->
                      let n, next_prob = prob_of_tactic t node.goal in
                      make_node
                        ~down:(fun () -> resume r t)
                        node.root_tactic node.goal node.id
                        (perform CurrentProb *. next_prob)
                        (* next_prob  *)
                        (Edge n)))
          | effect Subgoal g, k ->
              let parent = Multicont.Deep.promote k in
              let up = fun v -> resume parent v in
              expand dead
                (make_node ~up node.root_tactic g (uuid ())
                   (perform CurrentProb) (Edge "root"))
          | effect Fail, _ -> []
          | v -> (
              match node.up with
              (* Done nodes get max priority *)
              | None ->
                  [ make_node node.root_tactic node.goal node.id 1.1 (Done v) ]
              | Some r' ->
                  Hashtbl.replace dead node.id ();
                  r' v)))

let rec search dead (q : Frontier.t) depth =
  if depth = 0 then (
    let f = Frontier.fold_unordered (fun acc x -> x :: acc) [] q in
    (* let probs = Frontier.fold_unordered (fun acc x -> x.prob :: acc) [] q |> List.sort_uniq compare in *)

    f
    (* |> List.sort (fun a b -> compare b.prob a.prob) *)
    (* |> List.take 10 *)
    |> List.iter (fun n -> print_endline (show_node n));
    let top = Frontier.get_max_elt q in
    print_endline "TOP NODE: ";
    print_endline (show_node top);

    (* print_endline "unique probs: "; *)
    (* List.iter (fun p -> Printf.printf "%f\n" p) probs; *)
    trace_error "at depth";
    fail ())
  else
    match Frontier.pop_max q with
    | None -> failwith "empty"
    | Some head when Hashtbl.mem dead head.id -> search dead q depth
    | Some head -> (
        match head.expansion with
        | Done v -> v
        | _ ->
            expand dead head |> List.iter (fun n -> Frontier.add q n);
            search dead q (depth - 1))

let frontier_of_goal root_tac goal =
  let root_id = uuid () in
  let root_node = make_node root_tac goal root_id 1. (Edge "root") in
  Frontier.of_list [ root_node ]

let with_grimm ?(depth = max_int) : tactic_combinator =
 fun tac goal ->
  let dead = Hashtbl.create 16 in
  search dead (frontier_of_goal tac goal) depth
