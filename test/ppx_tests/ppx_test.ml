
let%expect_test "basic transformation" =
  let f = [%heft test] in
  Printf.printf "%d" f;
  [%expect {| 4 |}]


