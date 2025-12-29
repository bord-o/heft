open Holinone
(* open Elaborator *)
(* open Parse *)
(* open Printing *)
open Tactic

(* let%expect_test "basic" = *)
(*   let () = Derived.reset () |> Result.get_ok in *)
(*   let prg = *)
(*     {| *)
(* (theorem basic_refl *)
(*     (fix ((x 'a)) *)
(*         (= x x))) *)
(*   |} *)
(*   in *)
(*   let ast = parse_string prg in *)
(*   let tast = Tast.check_program ast in *)
(*   let () = Elab.elab_program tast in *)
(*   (!the_goals |> List.iter @@ fun (name, t) -> *)
(*       print_endline name; *)
(*       print_term t); *)
(*   let goal  = List.assoc "basic_refl" !the_goals in *)
(*   let cmds = [ASetGoal goal; APrintGoal] in *)
(*   handler cmds; *)
(**)
(**)
(**)
(*   [%expect {| *)
(*     basic_refl *)
(*     x = x *)
(*     |}] *)
let%expect_test "basic" =
  let () = Derived.reset () |> Result.get_ok in
  let _ = run_commands test_commands in
  print_endline "done";


  [%expect {|
    |}]
