open Heft
open Tactic

type dfs_res = Success | Failure

let test_search () =
  let print_choice = function
    | `A -> print_endline "A"
    | `B -> print_endline "B"
    | `C -> print_endline "C"
    | `D -> print_endline "D"
    | `E -> print_endline "E"
    | `F -> print_endline "F"
    | `G -> print_endline "G"
    | `H -> print_endline "H"
    | `I -> print_endline "I"
  in
  let choice = choose_unknowns [ `A; `B; `C ] in
  print_choice choice;
  let choice2 = choose_unknowns [ `D; `E; `F ] in
  print_choice choice2;
  let choice3 = choose_unknowns [ `G; `H; `I ] in
  print_choice choice3;

  match (choice, choice2, choice3) with `C, `F, `G -> Success | _ -> Failure

type pending = Pending : (unit -> dfs_res) -> pending

let choice_bfs () =
  let q : pending Queue.t = Queue.create () in
  let rec go comp =
    match comp () with
    | effect Choose lst, k' ->
        let k = Multicont.Deep.promote k' in
        List.iter
          (fun x -> Queue.add (Pending (fun () -> Multicont.Deep.resume k x)) q)
          (as_list lst);
        next ()
    | v -> v
  and next () =
    match Queue.take_opt q with
    | None -> Failure
    | Some (Pending thunk) -> (
        print_endline "trying next";
        match go thunk with
        | Success -> Success
        | Failure ->
            print_endline "computation returned failure";
            next ())
  in
  go test_search

(* let choice_bfs () = *)
(*   let q = ref [] in *)
(*   match test_search () with *)
(*   | effect Choose lst, k' -> *)
(*           let k = Multicont.Deep.promote k' in *)
(*           q := !q @ (List.map (fun x -> (k, x)) (as_list lst)); *)
(*           (match !q with *)
(*           | [] -> Failure *)
(*           | (k, x) :: lst ->  q := lst; Multicont.Deep.resume k x) *)
(**)
(*   | v -> *)
(*       print_endline *)
(*         (match v with *)
(*         | Success -> "computation returned Success" *)
(*         | Failure -> "computation returned Failure"); *)
(*       v *)

let choice_dfs () =
  match test_search () with
  | effect Choose cs, k ->
      let r = Multicont.Deep.promote k in
      let rec try' = function
        | [] -> Failure
        | this :: rest -> (
            print_endline "trying next";
            match Multicont.Deep.resume r this with
            | Success -> Success
            | Failure -> try' rest)
      in
      try' (as_list cs)
  | v ->
      print_endline
        (match v with
        | Success -> "computation returned Success"
        | Failure -> "computation returned Failure");
      v

let%expect_test "choice test bfs" =
  (match choice_bfs () with
  | Success -> print_endline "success"
  | Failure -> print_endline "failure");
  [%expect
    {|
    trying next
    A
    trying next
    B
    trying next
    C
    trying next
    D
    trying next
    E
    trying next
    F
    trying next
    D
    trying next
    E
    trying next
    F
    trying next
    D
    trying next
    E
    trying next
    F
    trying next
    G
    computation returned failure
    trying next
    H
    computation returned failure
    trying next
    I
    computation returned failure
    trying next
    G
    computation returned failure
    trying next
    H
    computation returned failure
    trying next
    I
    computation returned failure
    trying next
    G
    computation returned failure
    trying next
    H
    computation returned failure
    trying next
    I
    computation returned failure
    trying next
    G
    computation returned failure
    trying next
    H
    computation returned failure
    trying next
    I
    computation returned failure
    trying next
    G
    computation returned failure
    trying next
    H
    computation returned failure
    trying next
    I
    computation returned failure
    trying next
    G
    computation returned failure
    trying next
    H
    computation returned failure
    trying next
    I
    computation returned failure
    trying next
    G
    computation returned failure
    trying next
    H
    computation returned failure
    trying next
    I
    computation returned failure
    trying next
    G
    computation returned failure
    trying next
    H
    computation returned failure
    trying next
    I
    computation returned failure
    trying next
    G
    success
    |}]

let%expect_test "choice test dfs" =
  (match choice_dfs () with
  | Success -> print_endline "success"
  | Failure -> print_endline "failure");
  [%expect
    {|
    trying next
    A
    trying next
    D
    trying next
    G
    computation returned Failure
    trying next
    H
    computation returned Failure
    trying next
    I
    computation returned Failure
    trying next
    E
    trying next
    G
    computation returned Failure
    trying next
    H
    computation returned Failure
    trying next
    I
    computation returned Failure
    trying next
    F
    trying next
    G
    computation returned Failure
    trying next
    H
    computation returned Failure
    trying next
    I
    computation returned Failure
    trying next
    B
    trying next
    D
    trying next
    G
    computation returned Failure
    trying next
    H
    computation returned Failure
    trying next
    I
    computation returned Failure
    trying next
    E
    trying next
    G
    computation returned Failure
    trying next
    H
    computation returned Failure
    trying next
    I
    computation returned Failure
    trying next
    F
    trying next
    G
    computation returned Failure
    trying next
    H
    computation returned Failure
    trying next
    I
    computation returned Failure
    trying next
    C
    trying next
    D
    trying next
    G
    computation returned Failure
    trying next
    H
    computation returned Failure
    trying next
    I
    computation returned Failure
    trying next
    E
    trying next
    G
    computation returned Failure
    trying next
    H
    computation returned Failure
    trying next
    I
    computation returned Failure
    trying next
    F
    trying next
    G
    computation returned Success
    success
    |}]
