open Sexplib
open Ast

let rec parse_ty = function
  | Sexp.Atom s ->
      if String.length s > 0 && s.[0] = '\'' then TyVar s else TyApp (s, [])
  | Sexp.List (Sexp.Atom "->" :: args) -> parse_arrow args
  | Sexp.List (Sexp.Atom name :: args) -> TyApp (name, List.map parse_ty args)
  | Sexp.List [] -> failwith "empty type application"
  | Sexp.List (Sexp.List _ :: _) -> failwith "invalid type"

and parse_arrow = function
  | [ a; b ] -> TyApp ("fun", [ parse_ty a; parse_ty b ])
  | a :: rest -> TyApp ("fun", [ parse_ty a; parse_arrow rest ])
  | [] -> failwith "arrow requires at least two arguments"

let parse_binding = function
  | Sexp.List [ Sexp.Atom name; ty ] -> (name, parse_ty ty)
  | _ -> failwith "invalid binding: expected (name type)"

let parse_bindings = function
  | Sexp.List bindings -> List.map parse_binding bindings
  | single -> [ parse_binding single ]

let rec parse_tm = function
  | Sexp.Atom s -> Var s
  | Sexp.List [ Sexp.Atom "fn"; Sexp.List [ Sexp.Atom x; ty ]; body ] ->
      Lam (x, parse_ty ty, parse_tm body)
  | Sexp.List [ Sexp.Atom "let"; Sexp.Atom x; bound; body ] ->
      Let (x, parse_tm bound, parse_tm body)
  | Sexp.List [ Sexp.Atom "if"; cond; then_; else_ ] ->
      If (parse_tm cond, parse_tm then_, parse_tm else_)
  | Sexp.List [ Sexp.Atom "="; lhs; rhs ] -> Eq (parse_tm lhs, parse_tm rhs)
  | Sexp.List [ Sexp.Atom "forall"; bindings; body ] ->
      Forall (parse_bindings bindings, parse_tm body)
  | Sexp.List [ Sexp.Atom "exists"; bindings; body ] ->
      Exists (parse_bindings bindings, parse_tm body)
  | Sexp.List [ Sexp.Atom "fix"; bindings; body ] ->
      Fix (parse_bindings bindings, parse_tm body)
  | Sexp.List [] -> failwith "empty application"
  | Sexp.List (f :: args) ->
      List.fold_left (fun acc arg -> App (acc, parse_tm arg)) (parse_tm f) args

let parse_constr = function
  | Sexp.List [ Sexp.Atom name; Sexp.List args ] ->
      (name, List.map parse_ty args)
  | Sexp.List [ Sexp.Atom name ] -> (name, [])
  | Sexp.Atom name -> (name, [])
  | _ -> failwith "invalid constructor"

let parse_clause = function
  | Sexp.List [ Sexp.List args; body ] -> (List.map parse_tm args, parse_tm body)
  | _ -> failwith "invalid clause: expected ((args...) body)"

let parse_typarams = function
  | Sexp.List atoms ->
      List.map
        (function
          | Sexp.Atom s -> s | _ -> failwith "type parameter must be an atom")
        atoms
  | _ -> failwith "expected type parameter list"

let parse_decl = function
  | Sexp.List (Sexp.Atom "type" :: Sexp.Atom name :: typarams :: constrs) ->
      DType (name, parse_typarams typarams, List.map parse_constr constrs)
  | Sexp.List [ Sexp.Atom "def"; Sexp.Atom name; ty; body ] ->
      DDef (name, parse_ty ty, parse_tm body)
  | Sexp.List (Sexp.Atom "fun" :: Sexp.Atom name :: ty :: clauses) ->
      DFun (name, parse_ty ty, List.map parse_clause clauses)
  | Sexp.List [ Sexp.Atom "theorem"; Sexp.Atom name; body ] ->
      DTheorem (name, parse_tm body)
  | _ -> failwith "invalid declaration"

let parse_program sexps = List.map parse_decl sexps

let parse_string s =
  let sexps = Sexp.of_string_many s in
  parse_program sexps

let parse_file filename =
  let sexps = Sexp.load_sexps filename in
  parse_program sexps
