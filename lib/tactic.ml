open Kernel
open Derived
open Effect.Deep
open Printing

type goal = term list * term
[@@deriving show]
let gconcl = snd

type _ Effect.t += 
  | Subgoals : goal list -> thm list Effect.t

type tactic_name = 
  | Assumption
  | Conj

type command =
  | SetGoal of goal
  | Apply of tactic_name
  | ShowGoal

type tactic = goal -> thm

(* Exception for kernel errors *)
exception Kernel_error of kernel_error

(* Helper to convert Result to exception *)
let unwrap_result = function
  | Ok x -> x
  | Error e -> raise (Kernel_error e)

(* Example tactics - all return thm *)
let conj_tac (asms, concl) =
  let p, q = destruct_conj concl in
  match Effect.perform (Subgoals [(asms, p); (asms, q)]) with
  | [p_thm; q_thm] -> conj p_thm q_thm |> unwrap_result
  | _ -> failwith "expected both sides of conj"

let assumption_tac (asms, concl) =
  match List.find_opt (fun t -> alphaorder concl t = 0) asms with
  | Some asm -> assume asm |> unwrap_result
  | None -> failwith "no matching assumption"

let get_tactic = function
  | Assumption -> assumption_tac
  | Conj -> conj_tac

(* Handler that processes commands *)
let rec solve_with_commands (commands : command list ref) tactic goal =
  match tactic goal with
  | effect (Subgoals gs), k ->
      Printf.printf "Created %d subgoals\n" (List.length gs);
      List.iteri (fun i g -> (Printf.printf "  %d: \n" i;  (print_term (gconcl g)))) gs;
      
      (* Solve each subgoal using commands *)
      let thms = List.map (fun subgoal ->
        (* Pop next command *)
        match !commands with
        | [] -> failwith "ran out of commands"
        | Apply tac_name :: rest ->
            commands := rest;
            Printf.printf "Applying %s\n" (match tac_name with Assumption -> "assumption" | Conj -> "conj");
            let tactic = get_tactic tac_name in
            solve_with_commands commands tactic subgoal
        | _ -> failwith "expected Apply command"
      ) gs in
      
      continue k thms
  | thm -> 
      Printf.printf "Goal solved!\n";
      thm

(* Top-level handler *)
let run_commands (commands : command list) =
  let commands_ref = ref commands in
  let goal_ref = ref None in
  
  let rec process_commands () =
    match !commands_ref with
    | [] -> 
        Printf.printf "All commands processed\n";
        !goal_ref
    | cmd :: rest ->
        commands_ref := rest;
        (match cmd with
         | SetGoal g ->
                 (print_endline "Set goal" ;
                (print_term (gconcl g)));
             goal_ref := Some g;
             process_commands ()
         | ShowGoal ->
             (match !goal_ref with
              | None -> Printf.printf "No goal set\n"
              | Some g -> 
                      (print_endline "Current goal: ";
                      (print_term (gconcl g))));
             process_commands ()
         | Apply tac_name ->
             (match !goal_ref with
              | None -> failwith "no goal set"
              | Some g ->
                  Printf.printf "Applying %s to goal\n" (match tac_name with Assumption -> "assumption" | Conj -> "conj");
                  let tactic = get_tactic tac_name in
                  let thm = solve_with_commands commands_ref tactic g in
                  (print_endline "Final theorem:";
                  (print_thm thm));
                  goal_ref := None;
                  process_commands ()))
  in
  process_commands ()

(* Test *)
let p = make_var "p" bool_ty
let q = make_var "q" bool_ty

(* Test: prove p ∧ q from assumptions p and q *)
let test_commands = [
  SetGoal ([p; q], make_conj p q);
  Apply Conj;        (* splits into two subgoals: p and q *)
  Apply Assumption;  (* solves first subgoal p *)
  Apply Assumption;  (* solves second subgoal q *)
]

let result = run_commands test_commands
