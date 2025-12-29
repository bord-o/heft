open Kernel
open Derived
open Effect.Deep
open Printing

type goal = term list * term [@@deriving show]

let gconcl = snd

type _ Effect.t += Subgoals : goal list -> thm list Effect.t
type tactic_name = Assumption | Conj | Refl
type command = SetGoal of goal | Apply of tactic_name | ShowGoal
type tactic = goal -> thm

(* Exception for kernel errors *)
exception Kernel_error of kernel_error
exception Subgoals_not_ready

(* Helper to convert Result to exception *)
let unwrap_result = function Ok x -> x | Error e -> raise (Kernel_error e)

(* Example tactics *)
let conj_tac (asms, concl) =
  let p, q = destruct_conj concl in
  match Effect.perform (Subgoals [ (asms, p); (asms, q) ]) with
  | [ p_thm; q_thm ] -> conj p_thm q_thm |> unwrap_result
  | _ -> failwith "expected both sides of conj"

let assumption_tac (asms, concl) =
  match List.find_opt (fun t -> alphaorder concl t = 0) asms with
  | Some asm -> assume asm |> unwrap_result
  | None -> failwith "no matching assumption"

let refl_tac : tactic =
 fun (_asms, concl) ->
  match destruct_eq concl with
  | Ok (l, r) when alphaorder l r = 0 -> refl l |> Result.get_ok
  | Ok _ -> failwith "REFL_TAC: sides of equality not identical"
  | Error _ -> failwith "REFL_TAC: goal not an equalit"

let get_tactic = function
  | Assumption -> assumption_tac
  | Conj -> conj_tac
  | Refl -> refl_tac

(* Proof state *)
type tactic_application = { tactic : tactic_name; goal : goal }

type proof_session = {
  mutable goal_stack : goal list;
  mutable proof_script : tactic_application list;
  mutable cache : (goal, thm) Hashtbl.t;
}

let create_session () =
  { goal_stack = []; proof_script = []; cache = Hashtbl.create 10 }

(* Handler for running tactics *)
let run_tactic session tactic goal =
  match tactic goal with
  | effect Subgoals gs, k ->
      Printf.printf "Tactic needs subgoals: %d\n" (List.length gs);
      List.iteri
        (fun i g ->
          Printf.printf "  %d: " i;
          print_term (gconcl g))
        gs;

      (* Check if all subgoals are in cache *)
      let all_cached = List.for_all (fun g -> Hashtbl.mem session.cache g) gs in

      if all_cached then begin
        Printf.printf "All subgoals cached, resuming\n";
        let thms = List.map (fun g -> Hashtbl.find session.cache g) gs in
        continue k thms
      end
      else begin
        Printf.printf "Subgoals not ready, aborting\n";
        (* Add unsolved subgoals to stack *)
        let unsolved =
          List.filter (fun g -> not (Hashtbl.mem session.cache g)) gs
        in
        session.goal_stack <- unsolved @ session.goal_stack;
        raise Subgoals_not_ready
      end
  | thm ->
      Printf.printf "Tactic completed directly\n";
      thm

(* Version of run_tactic that doesn't modify the goal stack *)
let run_tactic_no_stack_modification session tactic goal =
  match tactic goal with
  | effect Subgoals gs, k ->
      let all_cached = List.for_all (fun g -> Hashtbl.mem session.cache g) gs in
      if all_cached then begin
        Printf.printf "All subgoals cached, resuming\n";
        let thms = List.map (fun g -> Hashtbl.find session.cache g) gs in
        continue k thms
      end
      else begin
        Printf.printf "Subgoals not ready, aborting\n";
        raise Subgoals_not_ready
      end
  | thm ->
      Printf.printf "Tactic completed directly\n";
      thm

(* Try to complete goals by re-running tactics *)
let retry_script session =
  List.iter
    (fun app ->
      if not (Hashtbl.mem session.cache app.goal) then begin
        Printf.printf "Retrying tactic on goal: ";
        print_term (gconcl app.goal);
        let tactic = get_tactic app.tactic in
        try
          let thm = run_tactic_no_stack_modification session tactic app.goal in
          Printf.printf "SUCCESS! Goal completed:\n";
          print_thm thm;
          Hashtbl.add session.cache app.goal thm;
          session.goal_stack <- List.filter (( <> ) app.goal) session.goal_stack
        with Subgoals_not_ready -> Printf.printf "Still waiting on subgoals\n"
      end)
    session.proof_script

(* Execute a command *)
let exec_command session command =
  match command with
  | SetGoal g ->
      print_endline "Set goal:";
      print_term (gconcl g);
      session.goal_stack <- [ g ]
  | ShowGoal ->
      Printf.printf "Goal stack (%d goals):\n" (List.length session.goal_stack);
      List.iteri
        (fun i g ->
          Printf.printf "  %d: " i;
          print_term (gconcl g))
        session.goal_stack
  | Apply tac_name -> (
      match session.goal_stack with
      | [] -> failwith "no goals to work on"
      | goal :: rest -> (
          Printf.printf "Applying %s\n"
            (match tac_name with
            | Assumption -> "assumption"
            | Conj -> "conj"
            | Refl -> "ref");

          (* Update stack to remove current goal *)
          session.goal_stack <- rest;

          (* Add to proof script *)
          let app = { tactic = tac_name; goal } in
          session.proof_script <- session.proof_script @ [ app ];

          (* Try to run it *)
          let tactic = get_tactic tac_name in
          try
            let thm = run_tactic session tactic goal in
            print_endline "Goal solved!";
            print_thm thm;
            Hashtbl.add session.cache goal thm;
            retry_script session
          with Subgoals_not_ready -> ()))

let show_session session =
  Printf.printf "\n=== Session State ===\n";
  Printf.printf "Goal stack: %d\n" (List.length session.goal_stack);
  List.iteri
    (fun i g ->
      Printf.printf "  %d: " i;
      print_term (gconcl g))
    session.goal_stack;
  Printf.printf "Cached: %d\n" (Hashtbl.length session.cache);
  Printf.printf "Script length: %d\n" (List.length session.proof_script);
  Printf.printf "=====================\n\n"

(* Test *)
let test_interactive () =
  let session = create_session () in
  let p = make_var "p" bool_ty in
  let q = make_var "q" bool_ty in

  print_endline "=== Step 1: Set goal ===";
  exec_command session (SetGoal ([ p; q ], make_conj p q));
  show_session session;

  print_endline "=== Step 2: Apply Conj ===";
  exec_command session (Apply Conj);
  show_session session;

  print_endline "=== Step 3: Apply Assumption (first subgoal) ===";
  exec_command session (Apply Assumption);
  show_session session;

  print_endline "=== Step 4: Apply Assumption (second subgoal) ===";
  exec_command session (Apply Assumption);
  show_session session
