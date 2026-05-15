[@@@warning "-26-27-32-33"]

open Heft
open Kernel
open Tactic
open Auto
open Rubiks

let () =
  print_newline ();
  print_newline ()

let%thm co_sum_inv_U (c : cube) = co_sum (move_U c) = co_sum c

and proof =
  begin
    gen
    >> destruct_cube @>> destruct_corners
    >> simp ~exclude:[ "co_add"; "eo_add" ]
    >> with_repeat @@ ac_norm "co_add"
    >> refl
  end
  [@quiet]

let%thm co_sum_inv_D (c : cube) = co_sum (move_D c) = co_sum c

and proof =
  begin
    gen
    >> destruct_cube @>> destruct_corners
    >> simp ~exclude:[ "co_add"; "eo_add" ]
    >> with_repeat @@ ac_norm "co_add"
    >> refl
  end
  [@quiet]

let%thm co_add_1122 = co_add C1 (co_add C1 (co_add C2 C2)) = C0
and proof = simp [@quiet] [@simp]

let%thm co_sum_inv_L (c : cube) = co_sum (move_L c) = co_sum c

and proof =
  begin
    gen
    >> destruct_cube @>> destruct_corners
    >> simp ~exclude:[ "co_add"; "eo_add" ]
    >> with_repeat (with_proven [ "co_add_assoc" ] rewrite)
    >> with_repeat @@ ac_norm "co_add"
    >> simp ~exclude:[ "co_add"; "eo_add" ]
  end
  [@quiet]

let%thm co_sum_inv_R (c : cube) = co_sum (move_R c) = co_sum c

and proof =
  begin
    gen
    >> destruct_cube @>> destruct_corners
    >> simp ~exclude:[ "co_add"; "eo_add" ]
    >> with_repeat (with_proven [ "co_add_assoc" ] rewrite)
    >> with_repeat @@ ac_norm "co_add"
    >> simp ~exclude:[ "co_add"; "eo_add" ]
  end
  [@quiet]

let%thm co_sum_inv_F (c : cube) = co_sum (move_F c) = co_sum c

and proof =
  begin
    gen
    >> destruct_cube @>> destruct_corners @>> destruct_edges
    >> simp ~exclude:[ "co_add"; "eo_add" ]
    >> with_repeat (with_proven [ "co_add_assoc" ] rewrite)
    >> with_repeat @@ ac_norm "co_add"
    >> simp ~exclude:[ "co_add"; "eo_add" ]
  end
  [@quiet]

let%thm co_sum_inv_B (c : cube) = co_sum (move_B c) = co_sum c

and proof =
  begin
    gen
    >> destruct_cube @>> destruct_corners @>> destruct_edges
    >> simp ~exclude:[ "co_add"; "eo_add" ]
    >> with_repeat (with_proven [ "co_add_assoc" ] rewrite)
    >> with_repeat @@ ac_norm "co_add"
    >> simp ~exclude:[ "co_add"; "eo_add" ]
  end
  [@quiet]
