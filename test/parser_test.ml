open Heft
open Parser

(* Tests *)
let%expect_test "parse_vartype" =
  let ds = parse_string "vartype a b c" in
  List.iter (fun d -> print_endline (show_def d)) ds;
  [%expect {| (Parser.Vartype ["a"; "b"; "c"]) |}]

let%expect_test "parse_variable" =
  let ds = parse_string "variable n m : nat" in
  List.iter (fun d -> print_endline (show_def d)) ds;
  [%expect {| (Parser.Variable (["n"; "m"], (Parser.TyVar "nat"))) |}]

let%expect_test "parse_inductive_nat" =
  let ds =
    parse_string
      {|
    inductive nat :=
    | zero : nat
    | suc : nat -> nat
  |}
  in
  List.iter (fun d -> print_endline (show_def d)) ds;
  [%expect
    {|
    (Parser.Inductive ("nat",
       [("zero", (Parser.TyVar "nat"));
         ("suc", (Parser.TyFun ((Parser.TyVar "nat"), (Parser.TyVar "nat"))))]
       ))
    |}]

let%expect_test "parse_inductive_list" =
  let ds =
    parse_string
      {|
    inductive list :=
    | nil : list a
    | cons : a -> list a -> list a
  |}
  in
  List.iter (fun d -> print_endline (show_def d)) ds;
  [%expect
    {|
    (Parser.Inductive ("list",
       [("nil", (Parser.TyCon ("list", [(Parser.TyVar "a")])));
         ("cons",
          (Parser.TyFun ((Parser.TyVar "a"),
             (Parser.TyFun ((Parser.TyCon ("list", [(Parser.TyVar "a")])),
                (Parser.TyCon ("list", [(Parser.TyVar "a")]))))
             )))
         ]
       ))
    |}]

let%expect_test "parse_def_plus" =
  let ds =
    parse_string
      {|
    def plus over n : nat -> nat -> nat
    | zero => λm. m
    | suc n => λm. suc (plus n m)
  |}
  in
  List.iter (fun d -> print_endline (show_def d)) ds;
  [%expect
    {|
    (Parser.Def ("plus", "n",
       (Parser.TyFun ((Parser.TyVar "nat"),
          (Parser.TyFun ((Parser.TyVar "nat"), (Parser.TyVar "nat"))))),
       [((Parser.PVar "zero"), (Parser.Lam ("m", (Parser.Var "m"))));
         ((Parser.PCon ("suc", [(Parser.PVar "n")])),
          (Parser.Lam ("m",
             (Parser.App ((Parser.Var "suc"),
                (Parser.App (
                   (Parser.App ((Parser.Var "plus"), (Parser.Var "n"))),
                   (Parser.Var "m")))
                ))
             )))
         ]
       ))
    |}]

let%expect_test "parse_theorem" =
  let ds = parse_string "theorem plus_comm : eq (plus n m) (plus m n)" in
  List.iter (fun d -> print_endline (show_def d)) ds;
  [%expect
    {|
    (Parser.Theorem ("plus_comm",
       (Parser.App (
          (Parser.App ((Parser.Var "eq"),
             (Parser.App ((Parser.App ((Parser.Var "plus"), (Parser.Var "n"))),
                (Parser.Var "m")))
             )),
          (Parser.App ((Parser.App ((Parser.Var "plus"), (Parser.Var "m"))),
             (Parser.Var "n")))
          ))
       ))
    |}]

let%expect_test "parse_full" =
  let ds =
    parse_string
      {|
    vartype a b

    inductive nat :=
    | zero : nat
    | suc : nat -> nat

    inductive list :=
    | nil : list a
    | cons : a -> list a -> list a

    variable n m : nat
    variable xs : list a

    def plus over n : nat -> nat -> nat
    | zero => λm. m
    | suc n => λm. suc (plus n m)

    def map over xs : list a -> (a -> b) -> list b
    | nil => λf. nil
    | cons x xs => λf. cons (f x) (map xs f)

    theorem plus_comm : eq (plus n m) (plus m n)
  |}
  in
  Printf.printf "Parsed %d definitions\n" (List.length ds);
  [%expect {| Parsed 8 definitions |}]
