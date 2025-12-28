open Ast
open Tast
open Elaborator

let%expect_test "simple_parse" =
  let prg =
    {|
    (type pair ('a 'b)
        (Pair 'a 'b))

    (type algraph ('a)
      (Empty)
      (Vertex 'a)
      (Connect (algraph 'a) (algraph 'a))
      (Overlay (algraph 'a) (algraph 'a)))

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
  let s = parse_string prg in
  List.iter (fun d -> print_endline @@ show_decl d) s;
  [%expect
    {|
    (Ast.DType ("pair", ["'a"; "'b"],
       [("Pair", [(Ast.STyVar "'a"); (Ast.STyVar "'b")])]))
    (Ast.DType ("algraph", ["'a"],
       [("Empty", []); ("Vertex", [(Ast.STyVar "'a")]);
         ("Connect",
          [(Ast.STyApp ("algraph", [(Ast.STyVar "'a")]));
            (Ast.STyApp ("algraph", [(Ast.STyVar "'a")]))]);
         ("Overlay",
          [(Ast.STyApp ("algraph", [(Ast.STyVar "'a")]));
            (Ast.STyApp ("algraph", [(Ast.STyVar "'a")]))])
         ]
       ))
    (Ast.DDef ("simple",
       (Ast.STyApp ("fun", [(Ast.STyApp ("nat", [])); (Ast.STyApp ("nat", []))])),
       (Ast.SLam ("n", (Ast.SApp ((Ast.SVar "S"), (Ast.SVar "n")))))))
    (Ast.DFun ("semant",
       (Ast.STyApp ("fun",
          [(Ast.STyApp ("algraph", [(Ast.STyVar "'a")]));
            (Ast.STyApp ("pair",
               [(Ast.STyApp ("set",
                   [(Ast.STyApp ("pair", [(Ast.STyVar "'a"); (Ast.STyVar "'a")]))
                     ]
                   ));
                 (Ast.STyApp ("set", [(Ast.STyVar "'a")]))]
               ))
            ]
          )),
       [([(Ast.PVar "Empty")],
         (Ast.SApp ((Ast.SApp ((Ast.SVar "Pair"), (Ast.SVar "empty"))),
            (Ast.SVar "empty"))));
         ([(Ast.PApp ("Vertex", [(Ast.PVar "v")]))],
          (Ast.SApp ((Ast.SApp ((Ast.SVar "Pair"), (Ast.SVar "empty"))),
             (Ast.SApp ((Ast.SVar "singleton"), (Ast.SVar "v"))))));
         ([(Ast.PApp ("Overlay", [(Ast.PVar "x"); (Ast.PVar "y")]))],
          (Ast.SLet ("sx", (Ast.SApp ((Ast.SVar "semant"), (Ast.SVar "x"))),
             (Ast.SLet ("sy", (Ast.SApp ((Ast.SVar "semant"), (Ast.SVar "y"))),
                (Ast.SLet ("x_edges",
                   (Ast.SApp ((Ast.SVar "fst"), (Ast.SVar "sx"))),
                   (Ast.SLet ("x_verts",
                      (Ast.SApp ((Ast.SVar "snd"), (Ast.SVar "sx"))),
                      (Ast.SLet ("y_edges",
                         (Ast.SApp ((Ast.SVar "fst"), (Ast.SVar "sy"))),
                         (Ast.SLet ("y_verts",
                            (Ast.SApp ((Ast.SVar "snd"), (Ast.SVar "sy"))),
                            (Ast.SApp (
                               (Ast.SApp ((Ast.SVar "Pair"),
                                  (Ast.SApp (
                                     (Ast.SApp ((Ast.SVar "union"),
                                        (Ast.SVar "x_edges"))),
                                     (Ast.SVar "y_edges")))
                                  )),
                               (Ast.SApp (
                                  (Ast.SApp ((Ast.SVar "union"),
                                     (Ast.SVar "x_verts"))),
                                  (Ast.SVar "y_verts")))
                               ))
                            ))
                         ))
                      ))
                   ))
                ))
             )));
         ([(Ast.PApp ("Connect", [(Ast.PVar "x"); (Ast.PVar "y")]))],
          (Ast.SLet ("sx", (Ast.SApp ((Ast.SVar "semant"), (Ast.SVar "x"))),
             (Ast.SLet ("sy", (Ast.SApp ((Ast.SVar "semant"), (Ast.SVar "y"))),
                (Ast.SLet ("x_edges",
                   (Ast.SApp ((Ast.SVar "fst"), (Ast.SVar "sx"))),
                   (Ast.SLet ("x_verts",
                      (Ast.SApp ((Ast.SVar "snd"), (Ast.SVar "sx"))),
                      (Ast.SLet ("y_edges",
                         (Ast.SApp ((Ast.SVar "fst"), (Ast.SVar "sy"))),
                         (Ast.SLet ("y_verts",
                            (Ast.SApp ((Ast.SVar "snd"), (Ast.SVar "sy"))),
                            (Ast.SApp (
                               (Ast.SApp ((Ast.SVar "Pair"),
                                  (Ast.SApp (
                                     (Ast.SApp ((Ast.SVar "union"),
                                        (Ast.SApp (
                                           (Ast.SApp ((Ast.SVar "union"),
                                              (Ast.SVar "x_edges"))),
                                           (Ast.SVar "y_edges")))
                                        )),
                                     (Ast.SApp (
                                        (Ast.SApp ((Ast.SVar "cart_prod"),
                                           (Ast.SVar "x_verts"))),
                                        (Ast.SVar "y_verts")))
                                     ))
                                  )),
                               (Ast.SApp (
                                  (Ast.SApp ((Ast.SVar "union"),
                                     (Ast.SVar "x_verts"))),
                                  (Ast.SVar "y_verts")))
                               ))
                            ))
                         ))
                      ))
                   ))
                ))
             )))
         ]
       ))
    (Ast.DTheorem ("overlay_zero",
       (Ast.SForall ([("n", (Ast.STyVar "'a"))],
          (Ast.SEq (
             (Ast.SApp ((Ast.SVar "semant"),
                (Ast.SApp ((Ast.SApp ((Ast.SVar "Overlay"), (Ast.SVar "n"))),
                   (Ast.SVar "Empty")))
                )),
             (Ast.SApp ((Ast.SVar "semant"), (Ast.SVar "n")))))
          ))
       ))
    |}]

let%expect_test "simple_typecheck" =
  let prg =
    {|
    (type nat ()
        (Z)
        (S nat))

    (def simple (-> nat nat)
      (fn n (S n)))
    |}
  in
  let untyped = parse_string prg in
  let typed = check_program untyped in
  print_endline @@ show_tprogram typed;
  [%expect
    {|
    [(Tast.TDType ("nat", [], [("Z", []); ("S", [(Tast.TyApp ("nat", []))])]));
      (Tast.TDDef ("simple",
         (Tast.TyApp ("fun", [(Tast.TyApp ("nat", [])); (Tast.TyApp ("nat", []))]
            )),
         (Tast.TLam ("n", (Tast.TyApp ("nat", [])),
            (Tast.TApp (
               (Tast.TConst ("S",
                  (Tast.TyApp ("fun",
                     [(Tast.TyApp ("nat", [])); (Tast.TyApp ("nat", []))]))
                  )),
               (Tast.TVar ("n",
                  (Tast.TyVar ref ((Tast.Link (Tast.TyApp ("nat", []))))))),
               (Tast.TyApp ("nat", [])))),
            (Tast.TyApp ("fun",
               [(Tast.TyApp ("nat", [])); (Tast.TyApp ("nat", []))]))
            ))
         ))
      ]
    |}]

let%expect_test "simple_typecheck" =
  let prg =
    {|
    (type nat ()
        (Z)
        (S (nat)))
    (type list ('a)
       (Nil)
       (Cons 'a (list 'a))
    )

    (fun tl (-> (list 'a) (list 'a))
        ((Nil) (Nil))
        ((Cons x xs) (xs)))

    (def test (list nat)
      (tl Nil))
    |}
  in
  let untyped = parse_string prg in
  print_endline @@ show_program untyped;
  let typed = check_program untyped in
  print_endline @@ show_tprogram typed;
  [%expect {|
    |}]
