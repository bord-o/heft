(** AST types *)

type ty = TyVar of string | TyCon of string * ty list | TyFun of ty * ty
[@@deriving show]

type pat = PVar of string | PCon of string * pat list [@@deriving show]

type expr = Var of string | App of expr * expr | Lam of string * expr
[@@deriving show]

type def =
  | Vartype of string list
  | Variable of string list * ty
  | Inductive of string * (string * ty) list
  | Def of string * string * ty * (pat * expr) list
  | Theorem of string * expr
[@@deriving show]

(** Parser *)

open Lexer

exception ParseError of string

type state = { mutable tokens : token list }

let make_state tokens = { tokens }
let peek s = List.hd s.tokens
let advance s = s.tokens <- List.tl s.tokens

let expect s tok =
  if peek s = tok then advance s
  else raise (ParseError (Printf.sprintf "expected %s" (show_token tok)))

let ident s =
  match peek s with
  | IDENT x ->
      advance s;
      x
  | t ->
      raise
        (ParseError
           (Printf.sprintf "expected identifier, got %s" (show_token t)))

(* Types *)
let rec ty_atom s =
  match peek s with
  | LPAREN ->
      advance s;
      let t = ty s in
      expect s RPAREN;
      t
  | IDENT x -> (
      advance s;
      match peek s with
      | IDENT _ | LPAREN ->
          let args = ty_args s in
          TyCon (x, args)
      | _ -> TyVar x)
  | t ->
      raise (ParseError (Printf.sprintf "expected type, got %s" (show_token t)))

and ty_args s =
  match peek s with
  | IDENT x ->
      advance s;
      TyVar x :: ty_args s
  | LPAREN ->
      let t = ty_atom s in
      t :: ty_args s
  | _ -> []

and ty s =
  let lhs = ty_atom s in
  match peek s with
  | ARROW ->
      advance s;
      TyFun (lhs, ty s)
  | _ -> lhs

(* Patterns: head followed by args until => *)
let rec pat_atom s =
  match peek s with
  | LPAREN ->
      advance s;
      let p = pat s in
      expect s RPAREN;
      p
  | IDENT x ->
      advance s;
      PVar x
  | t ->
      raise
        (ParseError (Printf.sprintf "expected pattern, got %s" (show_token t)))

and pat_args s =
  match peek s with
  | IDENT _ | LPAREN ->
      let p = pat_atom s in
      p :: pat_args s
  | _ -> []

and pat s =
  match peek s with
  | IDENT x ->
      advance s;
      let args = pat_args s in
      if args = [] then PVar x else PCon (x, args)
  | LPAREN ->
      advance s;
      let p = pat s in
      expect s RPAREN;
      p
  | t ->
      raise
        (ParseError (Printf.sprintf "expected pattern, got %s" (show_token t)))

(* Expressions *)
let rec expr_atom s =
  match peek s with
  | LPAREN ->
      advance s;
      let e = expr s in
      expect s RPAREN;
      e
  | LAMBDA ->
      advance s;
      let x = ident s in
      expect s DOT;
      Lam (x, expr s)
  | IDENT x ->
      advance s;
      Var x
  | t ->
      raise
        (ParseError
           (Printf.sprintf "expected expression, got %s" (show_token t)))

and expr s =
  let rec apps acc =
    match peek s with
    | IDENT _ | LPAREN | LAMBDA ->
        let e = expr_atom s in
        apps (App (acc, e))
    | _ -> acc
  in
  apps (expr_atom s)

(* Clauses: | pat => expr *)
let clause s =
  expect s BAR;
  let p = pat s in
  expect s FATARROW;
  let e = expr s in
  (p, e)

let rec clauses s =
  match peek s with
  | BAR ->
      let c = clause s in
      c :: clauses s
  | _ -> []

(* Constructor: name : ty *)
let constructor s =
  expect s BAR;
  let name = ident s in
  expect s COLON;
  let t = ty s in
  (name, t)

let rec constructors s =
  match peek s with
  | BAR ->
      let c = constructor s in
      c :: constructors s
  | _ -> []

(* Identifiers until colon *)
let rec idents s =
  match peek s with
  | IDENT x ->
      advance s;
      x :: idents s
  | _ -> []

(* Top-level definitions *)
let def s =
  match peek s with
  | VARTYPE ->
      advance s;
      Vartype (idents s)
  | VARIABLE ->
      advance s;
      let xs = idents s in
      expect s COLON;
      Variable (xs, ty s)
  | INDUCTIVE ->
      advance s;
      let name = ident s in
      expect s COLONEQ;
      Inductive (name, constructors s)
  | DEF ->
      advance s;
      let name = ident s in
      expect s OVER;
      let over = ident s in
      expect s COLON;
      let t = ty s in
      Def (name, over, t, clauses s)
  | THEOREM ->
      advance s;
      let name = ident s in
      expect s COLON;
      Theorem (name, expr s)
  | t ->
      raise
        (ParseError
           (Printf.sprintf "expected definition, got %s" (show_token t)))

let rec defs s =
  match peek s with
  | EOF -> []
  | _ ->
      let d = def s in
      d :: defs s

let parse tokens =
  let s = make_state tokens in
  defs s

let parse_string str = parse (tokenize_string str)
