open Holinone
(* main.ml *)

let parse_file filename =
  let ic = open_in filename in
  let lexbuf = Lexing.from_channel ic in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  
  try
    let ast = Parser.file Lexer.token lexbuf in
    close_in ic;
    ast
  with
  | Lexer.Error msg ->
      let pos = lexbuf.lex_curr_p in
      Printf.eprintf "Lexer error at %s:%d:%d: %s\n"
        pos.pos_fname
        pos.pos_lnum
        (pos.pos_cnum - pos.pos_bol + 1)
        msg;
      close_in ic;
      exit 1
      
  | Parser.Error ->
      let pos = lexbuf.lex_curr_p in
      let token = Lexing.lexeme lexbuf in
      Printf.eprintf "Parse error at %s:%d:%d\n"
        pos.pos_fname
        pos.pos_lnum
        (pos.pos_cnum - pos.pos_bol + 1);
      Printf.eprintf "Unexpected token: '%s'\n" token;
      close_in ic;
      exit 1

let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <file>\n" Sys.argv.(0);
    exit 1
  end;
  
  let ast = parse_file Sys.argv.(1) in
  Printf.printf "Parsed %d definitions\n" (List.length ast)
