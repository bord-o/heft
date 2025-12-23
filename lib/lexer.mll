{
open Parser

exception Error of string

let next_line lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  lexbuf.Lexing.lex_curr_p <-
    { pos with pos_bol = pos.pos_cnum;
               pos_lnum = pos.pos_lnum + 1 }
}

let whitespace = [' ' '\t' '\r']
let newline = '\n'
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']
let alpha = lower | upper
let ident_char = alpha | digit | '_' | '\''

let type_var = '\'' lower ident_char*
let lower_ident = lower ident_char*
let upper_ident = upper ident_char*

rule token = parse
  | whitespace+ { token lexbuf }
  | newline     { next_line lexbuf; token lexbuf }
  | "//" [^ '\n']* { token lexbuf }
  
  (* Keywords *)
  | "type"     { TYPE }
  | "where"    { WHERE }
  | "of"       { OF }
  | "def"      { DEF }
  | "fun"      { FUN }
  | "theorem"  { THEOREM }
  | "fn"       { FN }
  | "let"      { LET }
  | "in"       { IN }
  | "if"       { IF }
  | "then"     { THEN }
  | "else"     { ELSE }
  | "forall"   { FORALL }
  
  (* Symbols *)
  | "("        { LPAREN }
  | ")"        { RPAREN }
  | "|"        { BAR }
  | ","        { COMMA }
  | ":"        { COLON }
  | ":="       { COLONEQUAL }
  | "=>"       { DARROW }
  | "->"       { ARROW }
  | "="        { EQUALS }
  
  (* Identifiers *)
  | type_var as tv     { TYVAR tv }
  | lower_ident as id  { LIDENT id }
  | upper_ident as id  { UIDENT id }
  
  | eof        { EOF }
  | _ as c     { raise (Error (Printf.sprintf "Unexpected character: %c" c)) }
