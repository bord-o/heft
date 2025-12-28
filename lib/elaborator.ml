open Sexplib
open Ast

let elaborate _ = failwith "TODO"

let rec atoms_of_sexp_list = function
  | [] -> []
  | Sexp.Atom x :: xs -> x :: atoms_of_sexp_list xs
  | _ -> failwith "expected list of atoms"

(* Parse type arguments list like (a b) *)
let parse_typarams = function
  | Sexp.List args -> atoms_of_sexp_list args
  | _ -> failwith "expected type parameters list"

(* Parse a type *)
let rec parse_type = function
  | Sexp.Atom s ->
      if String.length s > 0 && s.[0] = '\'' 
      then STyVar s
      else STyApp (s, [])
  | Sexp.List (Sexp.Atom "->" :: args) ->
      parse_arrow args
  | Sexp.List (Sexp.Atom name :: args) ->
      STyApp (name, List.map parse_type args)
  | Sexp.List [] -> failwith "empty type application"
  | Sexp.List (Sexp.List _ :: _) -> failwith "invalid type"

and parse_arrow = function
  | [ a; b ] ->
      let ta = parse_type a in
      let tb = parse_type b in
      STyApp ("fun", [ ta; tb ])
  | a :: rest ->
      let ta = parse_type a in
      let tb = parse_arrow rest in
      STyApp ("fun", [ ta; tb ])
  | [] -> failwith "arrow requires at least two arguments"

(* Parse a pattern *)
let rec parse_pattern = function
  | Sexp.Atom s ->
      if String.length s > 0 && s.[0] >= 'A' && s.[0] <= 'Z' then
        PApp (s, [])
      else
        PVar s
  | Sexp.List (Sexp.Atom name :: args) ->
      PApp (name, List.map parse_pattern args)
  | Sexp.List [] -> failwith "empty pattern"
  | _ -> failwith "invalid pattern"

let parse_binding = function
  | Sexp.List [ Sexp.Atom name; ty ] -> (name, parse_type ty)
  | _ -> failwith "expected binding (name type)"

(* Parse a term *)
let rec parse_term = function
  | Sexp.Atom s -> SVar s
  | Sexp.List [ Sexp.Atom "fn"; Sexp.Atom x; body ] -> SLam (x, parse_term body)
  | Sexp.List [ Sexp.Atom "let"; Sexp.Atom x; bound; body ] ->
      SLet (x, parse_term bound, parse_term body)
  | Sexp.List [ Sexp.Atom "if"; cond; then_; else_ ] ->
      SIf (parse_term cond, parse_term then_, parse_term else_)
  | Sexp.List [ Sexp.Atom "forall"; Sexp.List bindings; body ] ->
      let bs = List.map parse_binding bindings in
      SForall (bs, parse_term body)
  | Sexp.List [ Sexp.Atom "exists"; Sexp.List bindings; body ] ->
      let bs = List.map parse_binding bindings in
      SExists (bs, parse_term body)
  | Sexp.List [ Sexp.Atom "="; lhs; rhs ] -> SEq (parse_term lhs, parse_term rhs)
  | Sexp.List [] -> failwith "empty application"
  | Sexp.List (f :: args) ->
      let f' = parse_term f in
      List.fold_left (fun acc arg -> SApp (acc, parse_term arg)) f' args

(* Parse a constructor like (Cons a (list a)) *)
let parse_constructor = function
  | Sexp.List (Sexp.Atom name :: args) -> (name, List.map parse_type args)
  | Sexp.Atom name -> (name, [])
  | Sexp.List [] -> failwith "empty constructor"
  | Sexp.List (Sexp.List _ :: _) -> failwith "constructor name must be an atom"

(* Parse a fun clause like ((Cons x xs) body) or (((Cons x xs)) body) *)
let parse_clause = function
  | Sexp.List [ Sexp.List [pattern]; body ] -> ([ parse_pattern pattern ], parse_term body)
  | Sexp.List [ pattern; body ] -> ([ parse_pattern pattern ], parse_term body)
  | _ -> failwith "invalid clause"

(* Parse a declaration *)
let parse_decl = function
  | Sexp.List (Sexp.Atom "type" :: Sexp.Atom name :: typarams :: constrs) ->
      let params = parse_typarams typarams in
      let cs = List.map parse_constructor constrs in
      DType (name, params, cs)
  | Sexp.List [ Sexp.Atom "def"; Sexp.Atom name; ty; body ] ->
      DDef (name, parse_type ty, parse_term body)
  | Sexp.List (Sexp.Atom "fun" :: Sexp.Atom name :: ty :: clauses) ->
      DFun (name, parse_type ty, List.map parse_clause clauses)
  | Sexp.List [ Sexp.Atom "theorem"; Sexp.Atom name; body ] ->
      DTheorem (name, parse_term body)
  | _ -> failwith "invalid declaration"

(* Parse a program (list of declarations) *)
let parse_program sexps = List.map parse_decl sexps

(* Parse from a string *)
let parse_string s =
  let sexps = Sexp.of_string_many s in
  parse_program sexps

(* Parse from a file *)
let parse_file filename =
  let sexps = Sexp.load_sexps filename in
  parse_program sexps
