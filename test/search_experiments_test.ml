open Effect
open Effect.Deep

type _ Effect.t +=
  | Choose : string * (string * 'a) list -> 'a Effect.t
  | Subgoal : int -> int Effect.t
  | Fail : 'a Effect.t

type tactic = int -> int

let subtract : tactic =
 fun n ->
  let k = perform (Choose ("amount", [ ("1", 1); ("2", 2); ("3", 3) ])) in
  if n - k >= 0 then perform (Subgoal (n - k)) else perform Fail

let done_ : tactic = fun n -> if n = 0 then 0 else perform Fail

let solve : tactic =
 fun n ->
  let tac =
    perform (Choose ("tactic", [ ("done", done_); ("subtract", subtract) ]))
  in
  tac n

let with_dfs =
 fun tac goal ->
  let depth = ref 0 in
  let indent () = String.make (!depth * 2) ' ' in
  let rec handler f =
    match f () with
    | effect Choose (name, choices), k ->
        let r = Multicont.Deep.promote k in
        let n = List.length choices in
        let rec try_each = function
          | [] ->
              Printf.printf "%s%s: all %d failed ← backtrack\n" (indent ()) name
                n;
              perform Fail
          | (label, c) :: cs -> (
              Printf.printf "%s%s: try %s\n" (indent ()) name label;
              match handler (fun () -> Multicont.Deep.resume r c) with
              | effect Fail, _ ->
                  Printf.printf "%s%s: %s failed\n" (indent ()) name label;
                  try_each cs
              | (v : int) ->
                  Printf.printf "%s%s: %s succeeded → %d\n" (indent ()) name
                    label v;
                  v)
        in
        try_each choices
    | effect Subgoal g, k ->
        Printf.printf "%s→ subgoal: solve %d\n" (indent ()) g;
        incr depth;
        let (v : int) = handler (fun () -> tac g) in
        decr depth;
        Printf.printf "%s← subgoal %d solved → %d\n" (indent ()) g v;
        handler (fun () -> continue k v)
    | effect Fail, _ -> perform Fail
    | (v : int) -> v
  in
  Printf.printf "GOAL: solve %d\n" goal;
  handler (fun () -> tac goal)

(*
    The goal is now to create a step function. For choose it will return all the choices, for subgoal it will return the subgoal, all suspended 
    computations.
*)

let step cont tac goal =
  match tac goal with
  | effect Fail, _ -> []
  | effect Choose (name, cs), k -> cs |> List.map @@ fun c -> (cont, c, k)
  | _ -> []

let%expect_test "redesign" =
  print_int @@ with_dfs solve 3;
  [%expect {|test|}]
