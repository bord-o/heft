let%expect_test "simple_parse" =
  let prg = {|
    (type pair (a b)
        (Pair a b))
    |} in
  print_endline "Hello";
  [%expect {|
    |}]
