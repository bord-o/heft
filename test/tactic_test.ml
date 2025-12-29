open Holinone
open Elaborator
open Parse
open Derived
open Proof

(* open Printing *)
open Tactic

let%expect_test "basic" =
  let () = Derived.reset () |> Result.get_ok in
  let prg =
    {|
(type nat ()
    (Z)
    (S (nat)))
(theorem basic_refl
    (fix ((x nat) (y nat))
        (/\ (= x x) (= y y))))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  let () = Elab.elab_program tast in
  (* (!the_goals |> List.iter @@ fun (name, t) -> *)
  (*     print_endline name; *)
  (*     print_term t); *)
  let goal = List.assoc "basic_refl" !the_goals in
  let session = create_session () in

  exec_command session (SetGoal ([], goal));
  exec_command session (Apply Conj);
  exec_command session (Apply Refl);
  exec_command session (Apply Refl);
  [%expect
    {|
    Set goal:
    x = x ∧ y = y

    Applying conj
    Applying refl
    Goal solved!
    ========================================
    x = x

    Applying refl
    Goal solved!
    ========================================
    y = y

    Goal completed:
    ========================================
    x = x ∧ y = y
    |}]

let%expect_test "basic" =
  let () = Derived.reset () |> Result.get_ok in
  let session = create_session () in
  let p = make_var "p" bool_ty in
  let q = make_var "q" bool_ty in

  exec_command session (SetGoal ([ p; q ], make_conj p q));
  exec_command session (Apply Conj);
  exec_command session (Apply Assumption);
  exec_command session (Apply Assumption);

  [%expect
    {|
    Set goal:
    p ∧ q

    Applying conj
    Applying assumption
    Goal solved!
    p
    ========================================
    p

    Applying assumption
    Goal solved!
    q
    ========================================
    q

    Goal completed:
    p
    q
    ========================================
    p ∧ q
    |}]

let%expect_test "basic3" =
  let () = Derived.reset () |> Result.get_ok in
  let prg =
    {|
(type nat ()
    (Z)
    (S (nat)))
(theorem basic_refl
    (fix ((x nat) (y nat))
        (\/ (= x x) (= y y))))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  let () = Elab.elab_program tast in
  let goal = List.assoc "basic_refl" !the_goals in
  let session = create_session () in
  exec_command session (SetGoal ([], goal));
  exec_command session (Apply Left);
  exec_command session (Apply Refl);

  [%expect
    {|
    Set goal:
    x = x ∨ y = y

    Applying left
    Applying refl
    Goal solved!
    ========================================
    x = x

    Goal completed:
    ========================================
    x = x ∨ y = y
    |}]

let%expect_test "basic4" =
  let () = Derived.reset () |> Result.get_ok in
  let prg =
    {|
(type nat ()
    (Z)
    (S (nat)))
(theorem basic_refl
    (fix ((x nat) (y nat))
        (\/ (= x x) (= y y))))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  let () = Elab.elab_program tast in
  let goal = List.assoc "basic_refl" !the_goals in
  let session = create_session () in
  exec_command session (SetGoal ([], goal));
  exec_command session (Apply Right);
  exec_command session (Apply Refl);

  [%expect
    {|
    Set goal:
    x = x ∨ y = y

    Applying right
    Applying refl
    Goal solved!
    ========================================
    y = y

    Goal completed:
    ========================================
    x = x ∨ y = y
    |}]

let%expect_test "basic5" =
  let () = Derived.reset () |> Result.get_ok in
  let prg = {|
(type nat ()
    (Z)
    (S (nat)))

  |} in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  let () = Elab.elab_program tast in
  let goal = List.assoc "basic_refl" !the_goals in
  let session = create_session () in
  exec_command session (SetGoal ([], goal));
  exec_command session (Apply Right);
  exec_command session (Apply Refl);

  [%expect
    {|
    Set goal:
    x = x ∨ y = y

    Applying right
    Applying refl
    Goal solved!
    ========================================
    y = y

    Goal completed:
    ========================================
    x = x ∨ y = y
    |}]
