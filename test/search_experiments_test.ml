open Effect
open Effect.Deep

type _ Effect.t +=
  | Choose : 'a list -> 'a Effect.t
  | Subgoal : int -> int Effect.t
  | Fail : 'a Effect.t

(* A "tactic" takes a problem (int) and returns a solution (int) *)
type tactic = int -> int

(* Reduce n toward 0 by subtracting 1, 2, or 3 *)
let subtract : tactic =
 fun n ->
  let k = perform (Choose [ 1; 2; 3 ]) in
  if n - k >= 0 then perform (Subgoal (n - k)) else perform Fail

let done_ : tactic = fun n -> if n = 0 then 0 else perform Fail

let solve : tactic =
 fun n ->
  let tac = perform (Choose [ done_; subtract ]) in
  tac n

let with_dfs =
 fun tac goal ->
  let rec handler f =
    match f () with
    | effect Choose choices, k ->
        let r = Multicont.Deep.promote k in
        let rec try_each = function
          | [] -> perform Fail
          | c :: cs -> (
              match handler (fun () -> Multicont.Deep.resume r c) with
              | effect Fail, _ -> try_each cs
              | thm -> thm)
        in
        try_each choices
    | effect Subgoal g, k ->
        let thm : int = handler (fun () -> tac g) in
        handler (fun () -> continue k thm)
    | effect Fail, _ -> perform Fail
    | v -> v
  in
  handler (fun () -> tac goal)

let%expect_test "redesign" =
  print_int @@ with_dfs solve 7;
  [%expect {|test|}]
