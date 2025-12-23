
let%expect_test "elaborate_simple" =
  let test_prog = {|
type fizz where
    | Buzz 
    | Bar

fun fizz_flip : fizz -> fizz where
  | fizz_flip Buzz => Bar
  | fizz_flip Bar => Buzz

        |} in
  let ast = Parser_driver.parse_string test_prog in
  ast |> List.iter @@ fun t -> print_endline @@ Ast.show_toplevel t;
  (* (match elaborate ast with *)
  (* | Ok () -> print_endline "elaborated successfully" *)
  (* | Error e -> print_endline @@ Kernel.show_kernel_error e); *)
  [%expect
    {|
    |}]

let%expect_test "elaborate_add" =
  let test_prog = {|
type nat0 where
    | Z0
    | S0

fun add : nat0 -> nat0 -> nat0 where
  | add Z0 (n:nat0) => (n:nat0)
  | add (S0 m) (n:nat0) => S0 (add (m:nat0) (n:nat0))

        |} in
  let ast = Parser_driver.parse_string test_prog in
  ast |> List.iter @@ fun t -> print_endline @@ Ast.show_toplevel t;
  (* (match elaborate ast with *)
  (* | Ok () -> print_endline "elaborated successfully" *)
  (* | Error e -> print_endline @@ Kernel.show_kernel_error e); *)
  [%expect
    {|
    |}]
