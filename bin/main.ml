open Holinone.Derived

let _ =
  match wip () with
  | Ok thm ->
      print_endline "Concluding";
      print_endline @@ Holinone.Printing.pretty_print_thm thm
  | Error (NewBasicDefinition t) ->
      print_endline (Holinone.Printing.pretty_print_hol_term t)
  | Error e -> print_endline (Holinone.show_kernel_error e)
