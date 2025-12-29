open Kernel
open Derived

type goal = term list * term [@@deriving show]
type _ Effect.t += Subgoals : goal list -> thm list Effect.t

let gconcl = snd

type tactic_name = Assumption | Conj | Refl | Left | Right
type tactic = goal -> thm


(* Helper to convert Result to exception *)
exception Kernel_error of kernel_error
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

let left_tac : tactic = fun (asms, concl) ->
    let l, r =  destruct_disj concl in
    match Effect.perform (Subgoals [ (asms, l)]) with
    | [l_thm] -> disj_left r l_thm |> Result.get_ok
    | _ -> failwith "expected single theorem"

let right_tac : tactic = fun (asms, concl) ->
    let l, r =  destruct_disj concl in
    match Effect.perform (Subgoals [ (asms, r)]) with
    | [r_thm] -> disj_right r_thm l |> Result.get_ok
    | _ -> failwith "expected single theorem"

let name_of_tactic = 
           function 
            | Assumption -> "assumption"
            | Conj -> "conj"
            | Refl -> "refl"
            | Left -> "left"
            | Right -> "right"

let get_tactic = function
  | Assumption -> assumption_tac
  | Conj -> conj_tac
  | Refl -> refl_tac
  | Left -> left_tac
  | Right -> right_tac


