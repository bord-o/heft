open Heft
open Grimm
open Tactic

let%expect_test "expansion" = 
    let root_tac =  (pick [gen; intro; assumption]) in
    let%thm goal (a : bool) (b : bool) (c : bool) = 
        a ==> (b ==> ( c ==> a))
    in
    let root_id = uuid () in
    let once = expand root_tac root_tac goal root_id in
    (* let twice = once |> List.map (fun e -> )  in *)
    List.iter (fun n -> print_endline (show_node n)) once;
    [%expect {|
      { Grimm.up = None; down = (Some <fun>); expansion = Grimm.Edge;
        id = 509d261a-cb89-497b-bd75-829c80f44325 }
      { Grimm.up = None; down = (Some <fun>); expansion = Grimm.Edge;
        id = 509d261a-cb89-497b-bd75-829c80f44325 }
      { Grimm.up = None; down = (Some <fun>); expansion = Grimm.Edge;
        id = 509d261a-cb89-497b-bd75-829c80f44325 }
      |}]
