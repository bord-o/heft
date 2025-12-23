type typ = TyVar of string | TyCon of string * typ list | TyArr of typ * typ
type pattern = PVar of string | PCon of string * pattern list

type term =
  | Var of string
  | Con of string
  | App of term * term
  | Lam of string * term
  | Let of string * term * term
  | If of term * term * term
  | Forall of string * term
  | Ann of term * typ

type constructor = string * typ list
type equation = string * pattern list * term

type type_def = {
  name : string;
  params : string list;
  constructors : constructor list;
}

type def = { name : string; typ : typ; body : term }
type fun_def = { name : string; typ : typ; equations : equation list }
type theorem = { name : string; statement : term }

type toplevel =
  | TypeDef of type_def
  | Def of def
  | Fun of fun_def
  | Theorem of theorem
