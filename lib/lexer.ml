(** Lexer for the theorem specification language using sedlex *)

type token =
  (* Keywords *)
  | VARTYPE
  | INDUCTIVE
  | VARIABLE
  | DEF
  | THEOREM
  (* Symbols *)
  | COLONEQ (* := *)
  | BAR (* | *)
  | COLON (* : *)
  | ARROW (* -> or → *)
  | FATARROW (* => or ⇒ *)
  | LPAREN (* ( *)
  | RPAREN (* ) *)
  | DOT (* . *)
  | LAMBDA (* λ or \ *)
  (* Identifiers *)
  | IDENT of string
  (* End of file *)
  | EOF
[@@deriving show]

(* Character classes *)
let letter = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z']
let digit = [%sedlex.regexp? '0' .. '9']
let ident_start = [%sedlex.regexp? letter | '_']
let ident_cont = [%sedlex.regexp? letter | digit | '_' | '\'']
let ident = [%sedlex.regexp? ident_start, Star ident_cont]

(* Whitespace and comments *)
let whitespace = [%sedlex.regexp? Plus (' ' | '\t' | '\n' | '\r')]
let line_comment = [%sedlex.regexp? "--", Star (Compl '\n')]

(* Keyword lookup *)
let keyword_table =
  [
    ("vartype", VARTYPE);
    ("inductive", INDUCTIVE);
    ("variable", VARIABLE);
    ("def", DEF);
    ("theorem", THEOREM);
  ]

let lookup_ident s =
  match List.assoc_opt s keyword_table with Some kw -> kw | None -> IDENT s

(* Position tracking *)
type position = { line : int; col : int; offset : int } [@@deriving show]
type located_token = { token : token; start_pos : position; end_pos : position }

let position_of_lexbuf buf =
  let pos, _ = Sedlexing.lexing_positions buf in
  {
    line = pos.pos_lnum;
    col = pos.pos_cnum - pos.pos_bol;
    offset = pos.pos_cnum;
  }

let end_position_of_lexbuf buf =
  let _, pos = Sedlexing.lexing_positions buf in
  {
    line = pos.pos_lnum;
    col = pos.pos_cnum - pos.pos_bol;
    offset = pos.pos_cnum;
  }

(* Error handling *)
exception LexError of position * string

let lex_error buf msg = raise (LexError (position_of_lexbuf buf, msg))

(* Main lexer *)
let rec token buf =
  match%sedlex buf with
  (* Whitespace and comments - skip *)
  | whitespace -> token buf
  | line_comment -> token buf
  (* Multi-character symbols (must come before single-char) *)
  | ":=" -> COLONEQ
  | "->" -> ARROW
  | 0x2192 -> ARROW (* → *)
  | "=>" -> FATARROW
  | 0x21D2 -> FATARROW (* ⇒ *)
  (* Single-character symbols *)
  | '|' -> BAR
  | ':' -> COLON
  | '(' -> LPAREN
  | ')' -> RPAREN
  | '.' -> DOT
  | 0x03BB -> LAMBDA (* λ *)
  | '\\' -> LAMBDA
  (* Identifiers and keywords *)
  | ident -> lookup_ident (Sedlexing.Utf8.lexeme buf)
  (* End of file *)
  | eof -> EOF
  (* Error *)
  | any ->
      let c = Sedlexing.Utf8.lexeme buf in
      lex_error buf (Printf.sprintf "Unexpected character: %s" c)
  | _ -> lex_error buf "Unexpected end of input"

(* Token with position *)
let located_token buf =
  let start_pos = position_of_lexbuf buf in
  let tok = token buf in
  let end_pos = end_position_of_lexbuf buf in
  { token = tok; start_pos; end_pos }

(* Tokenize entire input into a list *)
let tokenize_string s =
  let buf = Sedlexing.Utf8.from_string s in
  Sedlexing.set_filename buf "<string>";
  let rec go acc =
    let tok = token buf in
    match tok with EOF -> List.rev (EOF :: acc) | _ -> go (tok :: acc)
  in
  go []

let tokenize_channel ic =
  let buf = Sedlexing.Utf8.from_channel ic in
  let rec go acc =
    let tok = token buf in
    match tok with EOF -> List.rev (EOF :: acc) | _ -> go (tok :: acc)
  in
  go []
