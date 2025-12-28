
let%expect_test "simple_parse" =
  let _prg =
    {|
    (type pair ('a 'b)
        (Pair ('a 'b)))

    (type algraph ('a)
      (Empty ())
      (Vertex ('a))
      (Connect ((algraph 'a) (algraph 'a)))
      (Overlay ((algraph 'a) (algraph 'a))))

    (def simple (-> nat nat)
      (fn n (S n)))

    (fun semant (-> (algraph 'a) (pair (set (pair 'a 'a)) (set 'a)))
      ((Empty) (Pair empty empty))
      ((Vertex v) (Pair empty (singleton v)))
      ((Overlay x y)
        (let sx (semant x)
        (let sy (semant y)
        (let x_edges (fst sx)
        (let x_verts (snd sx)
        (let y_edges (fst sy)
        (let y_verts (snd sy)
        (Pair (union x_edges y_edges) (union x_verts y_verts)))))))))
      ((Connect x y)
        (let sx (semant x)
        (let sy (semant y)
        (let x_edges (fst sx)
        (let x_verts (snd sx)
        (let y_edges (fst sy)
        (let y_verts (snd sy)
        (Pair (union (union x_edges y_edges) (cart_prod x_verts y_verts))
              (union x_verts y_verts))))))))))
    (theorem overlay_zero
      (forall ((n 'a)) (= (semant (Overlay n Empty)) (semant n))))
    |}
  in
  print_endline "todo";
  [%expect
    {|
    |}]

