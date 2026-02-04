open Heft
open Elaborator
open Derived

let _ = reset ()

let%expect_test "elaborate_nat" =
  let _ = reset () in
  let result =
    elaborate_string
      {|
    inductive nat :=
    | Zero : nat
    | Suc : nat -> nat
  |}
  in
  (match result with
  | Ok (env, _) ->
      Printf.printf "Inductives: %d\n" (List.length env.inductives);
      List.iter (fun (name, _) -> Printf.printf "  %s\n" name) env.inductives
  | Error _ -> Printf.printf "Error\n");
  [%expect {|
    Inductives: 1
      nat
    |}]

let%expect_test "elaborate_nat_and_plus" =
  let _ = reset () in
  let result =
    elaborate_string
      {|
    inductive nat :=
    | Zero : nat
    | Suc : nat -> nat

    variable n m : nat

    def plus over n : nat -> nat -> nat
    | Zero => λm. m
    | Suc n => λm. Suc (plus n m)
  |}
  in
  (match result with
  | Ok (env, _) ->
      Printf.printf "Inductives: %d\n" (List.length env.inductives);
      Printf.printf "Defs: %d\n" (List.length env.defs);
      List.iter (fun (name, _) -> Printf.printf "  def: %s\n" name) env.defs
  | Error `NotAForall -> Printf.printf "Error: NotAForall\n"
  | Error `NotAnExists -> Printf.printf "Error: NotAnExists\n"
  | Error (`InvariantViolation s) ->
      Printf.printf "Error: InvariantViolation %s\n" s
  | Error (`NotAConstantName s) ->
      Printf.printf "Error: NotAConstantName %s\n" s
  | Error _ -> Printf.printf "Error: other\n");
  [%expect {|
    Inductives: 1
    Defs: 1
      def: plus
    |}]

let%expect_test "elaborate_theorem" =
  let _ = reset () in
  let result =
    elaborate_string
      {|
    inductive nat :=
    | Zero : nat
    | Suc : nat -> nat

    variable n m : nat

    def plus over n : nat -> nat -> nat
    | Zero => λm. m
    | Suc n => λm. Suc (plus n m)

    theorem plus_comm : eq (plus n m) (plus m n)
  |}
  in
  (match result with
  | Ok (_, goals) ->
      Printf.printf "Goals: %d\n" (List.length goals);
      List.iter
        (fun goal ->
          Printf.printf "  %s\n" (Printing.pretty_print_hol_term goal))
        goals
  | Error `NotAForall -> Printf.printf "Error: NotAForall\n"
  | Error `NotAnExists -> Printf.printf "Error: NotAnExists\n"
  | Error (`InvariantViolation s) ->
      Printf.printf "Error: InvariantViolation %s\n" s
  | Error (`NotAConstantName s) ->
      Printf.printf "Error: NotAConstantName %s\n" s
  | Error (`MakeAppTypesDontAgree (t1, t2)) ->
      Printf.printf "Error: MakeAppTypesDontAgree %s vs %s\n" (show_hol_type t1)
        (show_hol_type t2)
  | Error _ -> Printf.printf "Error: other\n");
  [%expect {|
    Goals: 1
      plus n m = plus m n
    |}]
