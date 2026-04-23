open Kernel
open Multicont.Deep
open Tactic
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

type expansion = Edge | Choice | Done of thm [@@deriving show]

type node = {
  up : (unit -> node list) option;
  down : (unit -> node list) option;
  expansion : expansion;
  id : Uuidm.t [@show fun u -> Uuidm.to_string u];
} [@@deriving show]

let uuid = Uuidm.v4_gen (Random.State.make_self_init ())

let test_id = uuid ()

let make_node ?up ?down id expansion=
  {
    up;
    down;
    expansion;
    id
  }

let rec expand ?(parent : (thm, node list) resumption option) (root : tactic)
    (tac : tactic) (goal : goal) (id : Uuidm.t) =
  match tac goal with
  | effect Choose cs, k -> (
      let r = Multicont.Deep.promote k in
      match cs with
      | Term ts ->
          ts
          |> List.map (fun t -> make_node ~down:(fun () -> resume r t) id Choice )
      | Theorem ts ->
          ts
          |> List.map (fun t -> make_node ~down:(fun () -> resume r t) id  Choice )
      | Unknown us ->
          us
          |> List.map (fun u -> make_node ~down:(fun () -> resume r u) id Choice )
      | Tactic ts ->
          ts |> List.map (fun t -> make_node ~down:(fun () -> resume r t) id Edge ))
  | effect Subgoal g, k ->
      let parent = Multicont.Deep.promote k in
      expand ~parent root root g  (uuid ())
  | effect Fail, _ -> [ ]
  | v -> (
      match parent with
      | None -> [ make_node id (Done v) ]
      | Some r' -> resume r' v)
