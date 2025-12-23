type typ = TyVar of string | TyCon of string * typ list | TyArr of typ * typ
[@@deriving show]

type pattern = 
  | PVar of string 
  | PCon of string * pattern list
  | PAnn of pattern * typ
[@@deriving show]

type term =
  | Var of string
  | Con of string
  | App of term * term
  | Lam of string * term
  | Let of string * term * term
  | If of term * term * term
  | Forall of string * term
  | Ann of term * typ
[@@deriving show]

type constructor = string * typ list [@@deriving show]
type equation = string * pattern list * term [@@deriving show]

type type_def = {
  name : string;
  params : string list;
  constructors : constructor list;
}
[@@deriving show]

type def = { name : string; typ : typ; body : term } [@@deriving show]

type fun_def = { name : string; typ : typ; equations : equation list }
[@@deriving show]

type theorem = { name : string; statement : term } [@@deriving show]

type toplevel =
  | TypeDef of type_def
  | Def of def
  | Fun of fun_def
  | Theorem of theorem
[@@deriving show]
