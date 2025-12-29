type name = string [@@deriving show]

type ty =
  | TyVar of name
  | TyApp of name * ty list
[@@deriving show]

type tm =
  | Var of name
  | App of tm * tm
  | Lam of name * ty * tm
  | Let of name * tm * tm
  | If of tm * tm * tm
  | Eq of tm * tm
[@@deriving show]

type constr = name * ty list [@@deriving show]
type clause = tm list * tm [@@deriving show]

type decl =
  | DType of name * name list * constr list
  | DDef of name * ty * tm
  | DFun of name * ty * clause list
  | DTheorem of name * tm
[@@deriving show]

type program = decl list [@@deriving show]
