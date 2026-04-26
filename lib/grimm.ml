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
type choiceKind =
  | CTerm of term
      [@printer fun fmt t -> Format.fprintf fmt "%s" (pretty_print_hol_term t)]
  | CTheorem of thm
      [@printer fun fmt t -> Format.fprintf fmt "%s" (pretty_print_thm t)]
  | CTactic of (tactic[@opaque])
  | CUnknown
[@@deriving show]

type expansion =
  | Edge of string
  | Choice of choiceKind
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
                  |> List.map (fun (t : term) ->
                      make_node
                        ~down:(fun () -> resume r t)
                        node.root_tactic node.goal node.id (perform CurrentProb)
                        (Choice (CTerm t)))
              | Theorem ts ->
                  ts
                  |> List.map (fun t ->
                      make_node
                        ~down:(fun () -> resume r t)
                        node.root_tactic node.goal node.id (perform CurrentProb)
                        (Choice (CTheorem t)))
              | Unknown us ->
                  us
                  |> List.map (fun u ->
                      make_node
                        ~down:(fun () -> resume r u)
                        node.root_tactic node.goal node.id (perform CurrentProb)
                        (Choice CUnknown))
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
  let size = Frontier.length q in
  let e, c =
    Frontier.fold_unordered
      (fun (edges, choices) n ->
        match n.expansion with
        | Edge _ -> (edges + 1, choices)
        | Choice _ -> (edges, choices + 1)
        | _ -> (edges, choices))
      (0, 0) q
  in
  trace_info @@ Printf.sprintf "Edges: %d, Choices: %d\n" e c;
  let q =
    if size mod 1000 = 0 then (
      trace_info "cleanup";
      let l = Frontier.fold_unordered (fun acc n -> n :: acc) [] q in
      let filtered = List.filter (fun n -> not (Hashtbl.mem dead n.id)) l in
      Frontier.of_list filtered)
    else q
  in
  if depth = 0 then (
    let top = Frontier.get_max_elt q in
    print_endline "at depth limit, TOP NODE: ";
    print_endline (show_node top);
    fail ())
  else
    match Frontier.pop_max q with
    | None -> failwith "empty"
    | Some head when Hashtbl.mem dead head.id -> search dead q depth
    | Some head -> (
        match head.expansion with
        | Done v -> v
        | _ ->
            trace_info (Printf.sprintf "size: %d\n" size);
            expand dead head |> List.iter (fun n -> Frontier.add q n);
            search dead q (depth - 1))

let frontier_of_goal root_tac goal =
  let root_id = uuid () in
  let root_node = make_node root_tac goal root_id 1. (Edge "root") in
  Frontier.of_list [ root_node ]

let with_grimm ?(depth = max_int) : tactic_combinator =
 (* print_endline (Printf.sprintf "called with depth %d\n" depth); *)
 fun tac goal ->
  let dead = Hashtbl.create 16 in

  search dead (frontier_of_goal tac goal) depth

let gauto =
  with_grimm
    (pick
       [
         simp;
         with_assumptions rewrite;
         with_flip_rules (with_assumptions rewrite);
         gen;
         intro;
         truth;
         assumption;
         neg_intro;
         conj;
         elim_conj_asm;
         eq_false_elim;
         eq_true_elim;
         elim_disj_asm;
         elim_exists_asm;
         false_elim;
         with_assumptions (with_first_term apply_asm);
       ])
