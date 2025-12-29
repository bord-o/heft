open Holinone
open Elaborator
open Parse
open Derived
open Proof
(* open Printing *)
open Tactic

let%expect_test "basic" =
  let () = Derived.reset () |> Result.get_ok in
  let prg = {|
(type nat ()
    (Z)
    (S (nat)))
(theorem basic_refl
    (fix ((x nat) (y nat))
        (/\ (= x x) (= y y))))
  |} in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  let () = Elab.elab_program tast in
  (* (!the_goals |> List.iter @@ fun (name, t) -> *)
  (*     print_endline name; *)
  (*     print_term t); *)
  let goal = List.assoc "basic_refl" !the_goals in
  let session = create_session () in
  exec_command session (SetGoal ([], goal));
  show_session session;

  exec_command session (Apply Conj);
  exec_command session (Apply Refl);
  exec_command session (Apply Refl);
  show_session session;
  [%expect {|
    Set goal:
    x = x ∧ y = y


    === Session State ===
    Goal stack: 1
      0: x = x ∧ y = y

    Cached: 0
    Script length: 0
    =====================

    Applying conj
    Tactic needs subgoals: 2
      0: x = x

      1: y = y

    Subgoals not ready, aborting
    Applying refl
    Tactic completed directly
    Goal solved!
    ========================================
    x = x

    Retrying tactic on goal: x = x ∧ y = y

    Subgoals not ready, aborting
    Still waiting on subgoals
    Applying refl
    Tactic completed directly
    Goal solved!
    ========================================
    y = y

    Retrying tactic on goal: x = x ∧ y = y

    All subgoals cached, resuming
    Tactic completed directly
    SUCCESS! Goal completed:
    ========================================
    x = x ∧ y = y


    === Session State ===
    Goal stack: 0
    Cached: 3
    Script length: 3
    =====================
    |}]

let%expect_test "basic" =
  let () = Derived.reset () |> Result.get_ok in
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
  show_session session;

  [%expect
    {|
    === Step 1: Set goal ===
    Set goal:
    p ∧ q


    === Session State ===
    Goal stack: 1
      0: p ∧ q

    Cached: 0
    Script length: 0
    =====================

    === Step 2: Apply Conj ===
    Applying conj
    Tactic needs subgoals: 2
      0: p

      1: q

    Subgoals not ready, aborting

    === Session State ===
    Goal stack: 2
      0: p

      1: q

    Cached: 0
    Script length: 1
    =====================

    === Step 3: Apply Assumption (first subgoal) ===
    Applying assumption
    Tactic completed directly
    Goal solved!
    p
    ========================================
    p

    Retrying tactic on goal: p ∧ q

    Subgoals not ready, aborting
    Still waiting on subgoals

    === Session State ===
    Goal stack: 1
      0: q

    Cached: 1
    Script length: 2
    =====================

    === Step 4: Apply Assumption (second subgoal) ===
    Applying assumption
    Tactic completed directly
    Goal solved!
    q
    ========================================
    q

    Retrying tactic on goal: p ∧ q

    All subgoals cached, resuming
    Tactic completed directly
    SUCCESS! Goal completed:
    p
    q
    ========================================
    p ∧ q


    === Session State ===
    Goal stack: 0
    Cached: 3
    Script length: 3
    =====================
    |}]


let%expect_test "basic3" =
  let () = Derived.reset () |> Result.get_ok in
  let prg = {|
(type nat ()
    (Z)
    (S (nat)))
(theorem basic_refl
    (fix ((x nat) (y nat))
        (\/ (= x x) (= y y))))
  |} in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  let () = Elab.elab_program tast in
  let goal = List.assoc "basic_refl" !the_goals in
  let session = create_session () in
  exec_command session (SetGoal ([], goal));
  exec_command session (Apply Left);
  exec_command session (Apply Refl);

  [%expect {|
    Set goal:
    x = x ∨ y = y

    Applying left
    Tactic needs subgoals: 1
      0: x = x

    Subgoals not ready, aborting
    Applying refl
    Tactic completed directly
    Goal solved!
    ========================================
    x = x

    Retrying tactic on goal: x = x ∨ y = y

    All subgoals cached, resuming
    Tactic completed directly
    SUCCESS! Goal completed:
    ========================================
    x = x ∨ y = y
    |}]


let%expect_test "basic4" =
  let () = Derived.reset () |> Result.get_ok in
  let prg = {|
(type nat ()
    (Z)
    (S (nat)))
(theorem basic_refl
    (fix ((x nat) (y nat))
        (\/ (= x x) (= y y))))
  |} in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  let () = Elab.elab_program tast in
  let goal = List.assoc "basic_refl" !the_goals in
  let session = create_session () in
  exec_command session (SetGoal ([], goal));
  exec_command session (Apply Right);
  exec_command session (Apply Refl);

  [%expect {|
    Set goal:
    x = x ∨ y = y

    Applying right
    Tactic needs subgoals: 1
      0: y = y

    Subgoals not ready, aborting
    Applying refl
    Tactic completed directly
    Goal solved!
    ========================================
    y = y

    Retrying tactic on goal: x = x ∨ y = y

    All subgoals cached, resuming
    Tactic completed directly
    SUCCESS! Goal completed:
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

  [%expect {|
    Set goal:
    x = x ∨ y = y

    Applying right
    Tactic needs subgoals: 1
      0: y = y

    Subgoals not ready, aborting
    Applying refl
    Tactic completed directly
    Goal solved!
    ========================================
    y = y

    Retrying tactic on goal: x = x ∨ y = y

    All subgoals cached, resuming
    Tactic completed directly
    SUCCESS! Goal completed:
    ========================================
    x = x ∨ y = y
    |}]

