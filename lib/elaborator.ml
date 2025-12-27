open Sexplib

(*
type name = string

type surf_ty =
  | STyVar of name
  | STyApp of name * surf_ty list

type pattern =
  | PVar of name
  | PApp of name * pattern list

type surf_tm =
  | SVar of name
  | SApp of surf_tm * surf_tm
  | SLam of name * surf_tm
  | SLet of name * surf_tm * surf_tm
  | SIf of surf_tm * surf_tm * surf_tm
  | SForall of name list * surf_tm
  | SExists of name list * surf_tm
  | SEq of surf_tm * surf_tm

type constructor = name * surf_ty list

type clause = pattern list * surf_tm

type decl =
  | DType of name * name list * constructor list
  | DDef of name * surf_ty * surf_tm
  | DFun of name * surf_ty * clause list
  | DTheorem of name * surf_tm

type program = decl list
 *)
let rec items_of_sexp_list = function
  | Sexp.Atom x :: xs -> x :: items_of_sexp_list xs
  | _ -> failwith "no nested lists allowed"

let parse_tyargs = function
  | Sexp.List args -> items_of_sexp_list args
  | _ -> failwith "not tyargs"

let parse_typedef = function
  | Sexp.List (Atom "type" :: Atom name :: tyargs :: cases) ->
      let args = parse_tyargs tyargs in
      let nnew = name ^ "new" in

      ()
  | _ -> failwith "Not a typedef"

let elaborate _ = failwith "TODO"

(*

(type algraph (a)
  (Empty)
  (Vertex a)
  (Connect (algraph a) (algraph a))
  (Overlay (algraph a) (algraph a)))

(type pair (a b)
  (Pair a b))

(def simple (-> nat nat)
  (fn n (S n)))

 *)
