let parse_string s =
  let lexbuf = Lexing.from_string s in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "from_string" };
  try
    let ast = Parser.file Lexer.token lexbuf in
    ast
  with
  | Lexer.Error msg ->
      let pos = lexbuf.lex_curr_p in
      Printf.eprintf "Lexer error at %s:%d:%d: %s\n" pos.pos_fname pos.pos_lnum
        (pos.pos_cnum - pos.pos_bol + 1)
        msg;
      exit 1
  | Parser.Error ->
      let pos = lexbuf.lex_curr_p in
      let token = Lexing.lexeme lexbuf in
      Printf.eprintf "Parse error at %s:%d:%d\n" pos.pos_fname pos.pos_lnum
        (pos.pos_cnum - pos.pos_bol + 1);
      Printf.eprintf "Unexpected token: '%s'\n" token;
      exit 1

let parse_file filename =
  In_channel.with_open_text filename @@ fun ic ->
  let s = In_channel.input_all ic in
  parse_string s
