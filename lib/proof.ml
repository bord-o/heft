open Kernel
open Effect.Deep
open Printing
open Tactic

exception Subgoals_pending

type command =
  | SetGoal of goal
  | Apply of tactic_name
  | ShowGoal
  | ShowSpecs
  | ShowInductives
  | ShowDefs
type tactic_application = { tactic : tactic_name; goal : goal }

type proof_session = {
  mutable goal_stack : goal list;
  mutable script : tactic_application list;
  mutable cache : (goal, thm) Hashtbl.t;
}

let create_session () =
  { goal_stack = []; script = []; cache = Hashtbl.create 16 }

let goal_is_cached session g = Hashtbl.mem session.cache g
let cache_lookup session g = Hashtbl.find session.cache g
let cache_add session g thm = Hashtbl.add session.cache g thm

(** Compare goals using alpha-equivalence *)
let goals_equal (asms1, concl1) (asms2, concl2) =
  alphaorder concl1 concl2 = 0
  && List.length asms1 = List.length asms2
  && List.for_all2 (fun a b -> alphaorder a b = 0) asms1 asms2

(** Handle the Subgoals effect during tactic execution. If [push_unsolved] is
    true, unsolved subgoals are added to the goal stack. *)
let handle_tactic_effects ~push_unsolved session tactic goal =
  match tactic goal with
  | effect Subgoals subgoals, k ->
      let _cached, uncached =
        List.partition (goal_is_cached session) subgoals
      in
      if uncached = [] then
        let thms = List.map (cache_lookup session) subgoals in
        continue k thms
      else (
        if push_unsolved then
          session.goal_stack <- uncached @ session.goal_stack;
        raise Subgoals_pending)
  | thm -> thm

(** Try to complete pending goals by re-running their tactics. Called after a
    goal is solved to propagate completions. Keeps iterating until no more
    progress can be made. *)
let retry_pending session =
  let made_progress = ref true in
  while !made_progress do
    made_progress := false;
    session.script
    |> List.iter (fun app ->
        if not (goal_is_cached session app.goal) then begin
          let tactic = get_tactic app.tactic in
          match
            handle_tactic_effects ~push_unsolved:false session tactic app.goal
          with
          | thm ->
              print_endline "Goal completed:";
              print_thm thm;
              cache_add session app.goal thm;
              session.goal_stack <-
                List.filter
                  (fun g -> not (goals_equal g app.goal))
                  session.goal_stack;
              made_progress := true
          | exception Subgoals_pending -> ()
        end)
  done

type tactic_result = Solved of thm | Pending

let apply_tactic session tac_name =
  match session.goal_stack with
  | [] -> failwith "No goals to work on"
  | goal :: rest -> (
      session.goal_stack <- rest;
      session.script <- session.script @ [ { tactic = tac_name; goal } ];

      let tactic = get_tactic tac_name in
      match handle_tactic_effects ~push_unsolved:true session tactic goal with
      | thm ->
          cache_add session goal thm;
          Solved thm
      | exception Subgoals_pending -> Pending)

let set_goal session g = session.goal_stack <- [ g ]

let exec_command session = function
  | SetGoal g ->
      print_endline "Set goal:";
      print_term (gconcl g);
      set_goal session g
  | ShowGoal ->
      Printf.printf "Goal stack (%d goals):\n" (List.length session.goal_stack);
      session.goal_stack
      |> List.iteri (fun i (asms, g) ->
          Printf.printf "  %d: " i;
          asms |> List.iter print_term;
          print_term g)
          (* print_endline @@ pretty_print_hol_term ~with_type:true (g)) *)
  | Apply tac_name -> (
      Printf.printf "Applying %s\n" (name_of_tactic tac_name);
      match apply_tactic session tac_name with
      | Solved thm ->
          print_endline "Goal solved!";
          print_thm thm;
          retry_pending session
      | Pending -> ())
  | ShowSpecs ->
      print_endline "Specifications:";
      the_specifications |> Hashtbl.iter (fun name thm ->
        Printf.printf "  %s:\n" name;
        print_thm thm)
  | ShowInductives ->
      print_endline "Inductive types:";
      the_inductives |> Hashtbl.iter (fun name def ->
        Printf.printf "  %s:\n" name;
        print_endline "    induction:";
        print_thm def.induction;
        print_endline "    recursion:";
        print_thm def.recursion;
        if def.distinct <> [] then begin
          print_endline "    distinct:";
          List.iter print_thm def.distinct
        end;
        if def.injective <> [] then begin
          print_endline "    injective:";
          List.iter print_thm def.injective
        end)
  | ShowDefs ->
      print_endline "Definitions:";
      !the_definitions |> List.iter (fun thm ->
        print_thm thm)

let show_session session =
  Printf.printf "\n=== Session State ===\n";
  Printf.printf "Goal stack: %d\n" (List.length session.goal_stack);
  session.goal_stack
  |> List.iteri (fun i g ->
      Printf.printf "  %d: " i;
      print_term (gconcl g));
  Printf.printf "Cached: %d\n" (Hashtbl.length session.cache);
  Printf.printf "Script length: %d\n" (List.length session.script);
  Printf.printf "=====================\n\n"

(** Get the proven theorem for a goal, if complete *)
let get_thm session goal =
  Hashtbl.find_opt session.cache goal

(** Check if proof is complete (no pending goals) and return the theorem *)
let result session =
  if session.goal_stack <> [] then
    None
  else
    (* Find the first goal in the script - that's our top-level goal *)
    match session.script with
    | [] -> None
    | first :: _ -> Hashtbl.find_opt session.cache first.goal
