open Effect
open Effect.Deep

(*
Some testing with a new search architecture that separates the 
exploration of choices and deepening of subgoals. In theory this should
give my priority queue strictly more control than aesop if I can pull 
it off.
 *)

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

(* type 'a step_result = *)
(*   | Cont of (unit -> 'a step_result) list *)
(*   | Need of 'a * (int -> 'a step_result) *)
(*   | Done of 'a *)
(*   | Dead *)
(**)
(* let step tac goal : 'a step_result = *)
(*   match tac goal with *)
(*   | effect Choose cs, k -> *)
(*       let r = Multicont.Deep.promote k in *)
(*       Cont (cs |> List.map (fun c () -> Multicont.Deep.resume r c)) *)
(*   | effect Subgoal g, k -> *)
(*       let r = Multicont.Deep.promote k in *)
(*       Need (g, fun v -> Multicont.Deep.resume r v) *)
(*   | effect Fail, _ -> Dead *)
(*   | v -> Done v *)
(**)
(* let print_step (s : int step_result) = *)
(*   match s with *)
(*   | Cont cs -> Printf.printf "%d continuations possible" (List.length cs) *)
(*   | Need (g, _) -> Printf.printf "Subgoal: %d\n" g *)
(*   | Done a -> Printf.printf "Done: %d\n" a *)
(*   | Dead -> print_endline "Dead" *)
(**)
(* let%expect_test "redesign" = *)
(*   (* print_int @@ with_dfs solve 7; *) *)
(*   let s1 = step solve 7 in *)
(*   print_step s1; *)
(**)
(*   [%expect {|test|}] *)

type 'a step_result =
  | Cont of (unit -> 'a step_result) list
  | Need of int * ('a -> 'a step_result)
  | Done of 'a
  | Dead

let step tac goal : 'a step_result =
  match tac goal with
  | effect Choose cs, k ->
      let r = Multicont.Deep.promote k in
      Cont (cs |> List.map (fun c () -> Multicont.Deep.resume r c))
  | effect Subgoal g, k ->
      let r = Multicont.Deep.promote k in
      Need (g, fun (v : int) -> Multicont.Deep.resume r v)
  | effect Fail, _ -> Dead
  | v -> Done v

let rec dfs tac parents result =
  match result with
  | Done v -> (
      match parents with
      | [] -> Some v
      | resume :: rest -> dfs tac rest (resume v))
  | Need (g, resume) -> dfs tac (resume :: parents) (step tac g)
  | Dead -> None
  | Cont thunks ->
      let rec try_each = function
        | [] -> None
        | t :: rest -> (
            match dfs tac parents (t ()) with
            | None -> try_each rest
            | some -> some)
      in
      try_each thunks

let bfs tac parents result =
  let q = Queue.create () in
  Queue.push (result, parents) q;
  let rec search () =
    match Queue.take_opt q with
    | None -> None
    | Some (result, parents) -> (
        match result with
        | Done v -> (
            match parents with
            | [] -> Some v
            | resume :: rest ->
                Queue.push (resume v, rest) q;
                search ())
        | Need (g, resume) ->
            Queue.push (step tac g, resume :: parents) q;
            search ()
        | Dead -> search ()
        | Cont thunks ->
            thunks |> List.iter (fun t -> Queue.push (t (), parents) q);
            search ())
  in
  search ()

let%expect_test "dfs solve 3" =
  (match bfs solve [] (step solve 3) with
  | Some v -> Printf.printf "Solution: %d\n" v
  | None -> print_endline "No solution");
  [%expect {| Solution: 0 |}]

let%expect_test "dfs solve 7" =
  (match dfs solve [] (step solve 7) with
  | Some v -> Printf.printf "Solution: %d\n" v
  | None -> print_endline "No solution");
  [%expect {| Solution: 0 |}]

let bfs_trace tac goal =
  let q = Queue.create () in
  Queue.push (step tac goal, [], [ goal ]) q;
  let rec search () =
    match Queue.take_opt q with
    | None -> None
    | Some (result, parents, path) -> (
        match result with
        | Done v -> (
            match parents with
            | [] -> Some (v, List.rev path)
            | resume :: rest ->
                Queue.push (resume v, rest, path) q;
                search ())
        | Need (g, resume) ->
            Queue.push (step tac g, resume :: parents, g :: path) q;
            search ()
        | Dead -> search ()
        | Cont thunks ->
            thunks |> List.iter (fun t -> Queue.push (t (), parents, path) q);
            search ())
  in
  search ()

let dfs_trace tac goal =
  let rec go tac parents path result =
    match result with
    | Done v -> (
        match parents with
        | [] -> Some (v, List.rev path)
        | resume :: rest -> go tac rest path (resume v))
    | Need (g, resume) -> go tac (resume :: parents) (g :: path) (step tac g)
    | Dead -> None
    | Cont thunks ->
        let rec try_each = function
          | [] -> None
          | t :: rest -> (
              match go tac parents path (t ()) with
              | None -> try_each rest
              | some -> some)
        in
        try_each thunks
  in
  go tac [] [ goal ] (step tac goal)

let print_path (v, path) =
  let s = path |> List.map string_of_int |> String.concat " → " in
  Printf.printf "Path: %s → done (%d)\n" s v;
  Printf.printf "Steps: %d\n" (List.length path - 1)

let%expect_test "dfs solve 3" =
  (match dfs_trace solve 3 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect {|
    Path: 3 → 2 → 1 → 0 → done (0)
    Steps: 3
    |}]

let%expect_test "bfs solve 3" =
  (match bfs_trace solve 3 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect {|
    Path: 3 → 0 → done (0)
    Steps: 1
    |}]

let%expect_test "dfs solve 7" =
  (match dfs_trace solve 7 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect
    {|
    Path: 7 → 6 → 5 → 4 → 3 → 2 → 1 → 0 → done (0)
    Steps: 7
    |}]

let%expect_test "bfs solve 7" =
  (match bfs_trace solve 7 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect {|
    Path: 7 → 6 → 3 → 0 → done (0)
    Steps: 3
    |}]

let split : tactic =
 fun n ->
  if n < 2 then perform Fail
  else
    let a = perform (Choose [ 1; 2; 3 ]) in
    let b = n - a in
    if b <= 0 then perform Fail
    else
      let ra = perform (Subgoal a) in
      let rb = perform (Subgoal b) in
      ra + rb

let solve2 : tactic =
 fun n ->
  let tac = perform (Choose [ done_; subtract; split ]) in
  tac n

let%expect_test "dfs solve2 4" =
  (match dfs_trace solve2 4 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect {|
    Path: 4 → 3 → 2 → 1 → 0 → done (0)
    Steps: 4
    |}]

let%expect_test "bfs solve2 4" =
  (match bfs_trace solve2 4 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect {|
    Path: 4 → 3 → 0 → done (0)
    Steps: 2
    |}]

let%expect_test "dfs solve2 6" =
  (match dfs_trace solve2 6 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect
    {|
    Path: 6 → 5 → 4 → 3 → 2 → 1 → 0 → done (0)
    Steps: 6
    |}]

let%expect_test "bfs solve2 6" =
  (match bfs_trace solve2 6 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect {|
    Path: 6 → 3 → 0 → done (0)
    Steps: 2
    |}]

let base : tactic = fun n -> if n <= 1 then n else perform Fail

let solve_split_only : tactic =
 fun n ->
  let tac = perform (Choose [ base; split ]) in
  tac n

let%expect_test "bfs split only 4" =
  (match bfs_trace solve_split_only 4 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect
    {|
    Path: 4 → 1 → 3 → 1 → 2 → 1 → 1 → done (4)
    Steps: 6
    |}]

let%expect_test "dfs split only 4" =
  (match dfs_trace solve_split_only 4 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect
    {|
    Path: 4 → 1 → 3 → 1 → 2 → 1 → 1 → done (4)
    Steps: 6
    |}]

(* 4 tactics, mirroring the real test *)
let sub1 : tactic =
 fun n -> if n >= 1 then perform (Subgoal (n - 1)) else perform Fail

let sub2 : tactic =
 fun n -> if n >= 2 then perform (Subgoal (n - 2)) else perform Fail

let sub3 : tactic =
 fun n -> if n >= 3 then perform (Subgoal (n - 3)) else perform Fail

let solve4 : tactic =
 fun n ->
  let tac = perform (Choose [ done_; sub1; sub2; sub3 ]) in
  tac n

let%expect_test "dfs solve4 6" =
  (match dfs_trace solve4 6 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect
    {|
    Path: 6 → 5 → 4 → 3 → 2 → 1 → 0 → done (0)
    Steps: 6
    |}]

let%expect_test "bfs solve4 6" =
  (match bfs_trace solve4 6 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect {|
    Path: 6 → 3 → 0 → done (0)
    Steps: 2
    |}]

let%expect_test "dfs solve4 9" =
  (match dfs_trace solve4 9 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect
    {|
    Path: 9 → 8 → 7 → 6 → 5 → 4 → 3 → 2 → 1 → 0 → done (0)
    Steps: 9
    |}]

let%expect_test "bfs solve4 9" =
  (match bfs_trace solve4 9 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect {|
    Path: 9 → 6 → 3 → 0 → done (0)
    Steps: 3
    |}]

let sub_pick : tactic =
 fun n ->
  let a = perform (Choose [ 1; 2; 3 ]) in
  let b = perform (Choose [ 0; 1 ]) in
  let k = a + b in
  if n - k >= 0 then perform (Subgoal (n - k)) else perform Fail

let solve5 : tactic =
 fun n ->
  let tac = perform (Choose [ done_; sub1; sub_pick ]) in
  tac n

let%expect_test "dfs solve5 9" =
  (match dfs_trace solve5 9 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect
    {|
    Path: 9 → 8 → 7 → 6 → 5 → 4 → 3 → 2 → 1 → 0 → done (0)
    Steps: 9
    |}]

let%expect_test "bfs solve5 9" =
  (match bfs_trace solve5 9 with
  | Some r -> print_path r
  | None -> print_endline "No solution");
  [%expect {|
    Path: 9 → 8 → 4 → 0 → done (0)
    Steps: 3
    |}]
