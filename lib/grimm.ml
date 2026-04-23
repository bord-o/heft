let () = ()
(*
Proof search with a flat fontier

what is a node?
    Right now a node is a suspended computation, marking a subgoal, concrete choice, or completed theorem

what does it mean to expand a node?
    Run it and serialize the effects into new nodes
    This implies that a node is an effect producing thunk, aka fun () -> tactic + goal  or maybe fun () -> resume k data
    In order to have value in arbitrary choices as nodes, I would need a way to actually rank them.
        Is there a case where we can say a choice resumption is better than a tactic resumption?

how do I control commit vs backtrack? Do I need to?

where is it meaningful to suspend computation, vs eagerly trying all choices?

is fuel a useful concept, is depth of tactic application better?

Do I need to track which rapp each node came from? 

Main idea: capture what a human would do by exposing each choice point to the search algorithm

 *)
