open Heft
open Lexer

(* Tests *)
let%expect_test "keywords" =
  let tokens = tokenize_string "vartype inductive variable def theorem" in
  List.iter (fun t -> print_endline (show_token t)) tokens;
  [%expect
    {|
    Lexer.VARTYPE
    Lexer.INDUCTIVE
    Lexer.VARIABLE
    Lexer.DEF
    Lexer.THEOREM
    Lexer.EOF
    |}]

let%expect_test "symbols" =
  let tokens = tokenize_string ":= | : -> => ( ) . λ \\" in
  List.iter (fun t -> print_endline (show_token t)) tokens;
  [%expect
    {|
    Lexer.COLONEQ
    Lexer.BAR
    Lexer.COLON
    Lexer.ARROW
    Lexer.FATARROW
    Lexer.LPAREN
    Lexer.RPAREN
    Lexer.DOT
    Lexer.LAMBDA
    Lexer.LAMBDA
    Lexer.EOF
    |}]

let%expect_test "unicode_symbols" =
  let tokens = tokenize_string "→ ⇒ λ" in
  List.iter (fun t -> print_endline (show_token t)) tokens;
  [%expect
    {|
    Lexer.ARROW
    Lexer.FATARROW
    Lexer.LAMBDA
    Lexer.EOF
    |}]

let%expect_test "identifiers" =
  let tokens =
    tokenize_string "a b nat list zero suc cons nil x' foo_bar _underscore"
  in
  List.iter (fun t -> print_endline (show_token t)) tokens;
  [%expect
    {|
    (Lexer.IDENT "a")
    (Lexer.IDENT "b")
    (Lexer.IDENT "nat")
    (Lexer.IDENT "list")
    (Lexer.IDENT "zero")
    (Lexer.IDENT "suc")
    (Lexer.IDENT "cons")
    (Lexer.IDENT "nil")
    (Lexer.IDENT "x'")
    (Lexer.IDENT "foo_bar")
    (Lexer.IDENT "_underscore")
    Lexer.EOF
    |}]

let%expect_test "comments" =
  let tokens = tokenize_string "foo -- this is a comment\nbar" in
  List.iter (fun t -> print_endline (show_token t)) tokens;
  [%expect
    {|
    (Lexer.IDENT "foo")
    (Lexer.IDENT "bar")
    Lexer.EOF
    |}]

let%expect_test "inductive_decl" =
  let tokens =
    tokenize_string
      {|
    inductive nat :=
    | zero : nat
    | suc : nat -> nat
  |}
  in
  List.iter (fun t -> print_endline (show_token t)) tokens;
  [%expect
    {|
    Lexer.INDUCTIVE
    (Lexer.IDENT "nat")
    Lexer.COLONEQ
    Lexer.BAR
    (Lexer.IDENT "zero")
    Lexer.COLON
    (Lexer.IDENT "nat")
    Lexer.BAR
    (Lexer.IDENT "suc")
    Lexer.COLON
    (Lexer.IDENT "nat")
    Lexer.ARROW
    (Lexer.IDENT "nat")
    Lexer.EOF
    |}]

let%expect_test "def_with_lambda" =
  let tokens =
    tokenize_string
      {|
    def plus : nat -> nat -> nat
    | zero => λm. m
    | suc n => λm. suc (plus n m)
  |}
  in
  List.iter (fun t -> print_endline (show_token t)) tokens;
  [%expect
    {|
    Lexer.DEF
    (Lexer.IDENT "plus")
    Lexer.COLON
    (Lexer.IDENT "nat")
    Lexer.ARROW
    (Lexer.IDENT "nat")
    Lexer.ARROW
    (Lexer.IDENT "nat")
    Lexer.BAR
    (Lexer.IDENT "zero")
    Lexer.FATARROW
    Lexer.LAMBDA
    (Lexer.IDENT "m")
    Lexer.DOT
    (Lexer.IDENT "m")
    Lexer.BAR
    (Lexer.IDENT "suc")
    (Lexer.IDENT "n")
    Lexer.FATARROW
    Lexer.LAMBDA
    (Lexer.IDENT "m")
    Lexer.DOT
    (Lexer.IDENT "suc")
    Lexer.LPAREN
    (Lexer.IDENT "plus")
    (Lexer.IDENT "n")
    (Lexer.IDENT "m")
    Lexer.RPAREN
    Lexer.EOF
    |}]

let%expect_test "theorem" =
  let tokens = tokenize_string "theorem plus_comm : eq (plus n m) (plus m n)" in
  List.iter (fun t -> print_endline (show_token t)) tokens;
  [%expect
    {|
    Lexer.THEOREM
    (Lexer.IDENT "plus_comm")
    Lexer.COLON
    (Lexer.IDENT "eq")
    Lexer.LPAREN
    (Lexer.IDENT "plus")
    (Lexer.IDENT "n")
    (Lexer.IDENT "m")
    Lexer.RPAREN
    Lexer.LPAREN
    (Lexer.IDENT "plus")
    (Lexer.IDENT "m")
    (Lexer.IDENT "n")
    Lexer.RPAREN
    Lexer.EOF
    |}]

let%expect_test "full_example" =
  let tokens =
    tokenize_string
      {|
    vartype a b

    inductive nat :=
    | zero : nat
    | suc : nat -> nat

    inductive list :=
    | nil : list a
    | cons : a -> list a -> list a

    variable n m : nat
    variable x y : a
    variable xs ys : list a

    def plus : nat -> nat -> nat
    | zero => λm. m
    | suc n => λm. suc (plus n m)

    def map : list a -> (a -> b) -> list b
    | nil => λf. nil
    | cons x xs => λf. cons (f x) (map xs f)

    theorem plus_comm : eq (plus n m) (plus m n)
  |}
  in
  Printf.printf "Token count: %d\n" (List.length tokens);
  [%expect {| Token count: 132 |}]
