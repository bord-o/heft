type name = string [@@deriving show]

type surf_ty = STyVar of name | STyApp of name * surf_ty list
[@@deriving show]

type pattern = PVar of name | PApp of name * pattern list [@@deriving show]
type binding = name * surf_ty [@@deriving show]

type surf_tm =
  | SVar of name
  | SApp of surf_tm * surf_tm
  | SLam of name * surf_tm
  | SLet of name * surf_tm * surf_tm
  | SIf of surf_tm * surf_tm * surf_tm
  | SForall of binding list * surf_tm
  | SExists of binding list * surf_tm
  | SEq of surf_tm * surf_tm
[@@deriving show]

type constructor = name * surf_ty list [@@deriving show]
type clause = pattern list * surf_tm [@@deriving show]

type decl =
  | DType of name * name list * constructor list
  | DDef of name * surf_ty * surf_tm
  | DFun of name * surf_ty * clause list
  | DTheorem of name * surf_tm
[@@deriving show]

type program = decl list [@@deriving show]
