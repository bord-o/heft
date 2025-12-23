open Holinone.Parser_driver
(* main.ml *)

let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <file>\n" Sys.argv.(0);
    exit 1
  end;

  let ast = parse_file Sys.argv.(1) in
  Printf.printf "Parsed %d definitions\n" (List.length ast)
