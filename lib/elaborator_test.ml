open Elaborator

let%expect_test "typecheck: nullary type and constant" =
  let prg =
    {|
    (type nat ()
      (Z)
      (S (nat)))

    (def zero nat Z)
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDDef ("zero", (Ast.TyApp ("nat", [])),
       (Tast.TConst ("Z", (Ast.TyApp ("nat", []))))))
    |}]

let%expect_test "typecheck: constructor application" =
  let prg =
    {|
    (type nat ()
      (Z)
      (S (nat)))

    (def one nat (S Z))
    (def two nat (S (S Z)))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDDef ("one", (Ast.TyApp ("nat", [])),
       (Tast.TApp (
          (Tast.TConst ("S",
             (Ast.TyApp ("fun",
                [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
             )),
          (Tast.TConst ("Z", (Ast.TyApp ("nat", [])))), (Ast.TyApp ("nat", []))))
       ))
    (Tast.TDDef ("two", (Ast.TyApp ("nat", [])),
       (Tast.TApp (
          (Tast.TConst ("S",
             (Ast.TyApp ("fun",
                [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
             )),
          (Tast.TApp (
             (Tast.TConst ("S",
                (Ast.TyApp ("fun",
                   [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                )),
             (Tast.TConst ("Z", (Ast.TyApp ("nat", [])))),
             (Ast.TyApp ("nat", [])))),
          (Ast.TyApp ("nat", []))))
       ))
    |}]

let%expect_test "typecheck: polymorphic type" =
  let prg =
    {|
    (type list ('a)
      (Nil)
      (Cons ('a (list 'a))))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("list", ["'a"],
       [("Nil", []);
         ("Cons", [(Ast.TyVar "'a"); (Ast.TyApp ("list", [(Ast.TyVar "'a")]))])]
       ))
    |}]

let%expect_test "typecheck: polymorphic instantiation" =
  let prg =
    {|
    (type nat ()
      (Z)
      (S (nat)))

    (type list ('a)
      (Nil)
      (Cons ('a (list 'a))))

    (def empty_nat_list (list nat) Nil)
    (def singleton_nat (list nat) (Cons Z Nil))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDType ("list", ["'a"],
       [("Nil", []);
         ("Cons", [(Ast.TyVar "'a"); (Ast.TyApp ("list", [(Ast.TyVar "'a")]))])]
       ))
    (Tast.TDDef ("empty_nat_list",
       (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))])),
       (Tast.TConst ("Nil", (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))))))
    (Tast.TDDef ("singleton_nat",
       (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))])),
       (Tast.TApp (
          (Tast.TApp (
             (Tast.TConst ("Cons",
                (Ast.TyApp ("fun",
                   [(Ast.TyApp ("nat", []));
                     (Ast.TyApp ("fun",
                        [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]));
                          (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]
                        ))
                     ]
                   ))
                )),
             (Tast.TConst ("Z", (Ast.TyApp ("nat", [])))),
             (Ast.TyApp ("fun",
                [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]));
                  (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]
                ))
             )),
          (Tast.TConst ("Nil", (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))])))),
          (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))))
       ))
    |}]

let%expect_test "typecheck: lambda with type annotation" =
  let prg =
    {|
    (type nat ()
      (Z)
      (S (nat)))

    (def succ (-> nat nat)
      (fn (n nat) (S n)))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDDef ("succ",
       (Ast.TyApp ("fun", [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))])),
       (Tast.TLam ("n", (Ast.TyApp ("nat", [])),
          (Tast.TApp (
             (Tast.TConst ("S",
                (Ast.TyApp ("fun",
                   [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                )),
             (Tast.TVar ("n", (Ast.TyApp ("nat", [])))), (Ast.TyApp ("nat", []))
             )),
          (Ast.TyApp ("fun", [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
          ))
       ))
    |}]

let%expect_test "typecheck: let binding" =
  let prg =
    {|
    (type nat ()
      (Z)
      (S (nat)))

    (def test nat
      (let x Z
      (let y (S x)
      (S y))))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDDef ("test", (Ast.TyApp ("nat", [])),
       (Tast.TLet ("x", (Ast.TyApp ("nat", [])),
          (Tast.TConst ("Z", (Ast.TyApp ("nat", [])))),
          (Tast.TLet ("y", (Ast.TyApp ("nat", [])),
             (Tast.TApp (
                (Tast.TConst ("S",
                   (Ast.TyApp ("fun",
                      [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                   )),
                (Tast.TVar ("x", (Ast.TyApp ("nat", [])))),
                (Ast.TyApp ("nat", [])))),
             (Tast.TApp (
                (Tast.TConst ("S",
                   (Ast.TyApp ("fun",
                      [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                   )),
                (Tast.TVar ("y", (Ast.TyApp ("nat", [])))),
                (Ast.TyApp ("nat", [])))),
             (Ast.TyApp ("nat", [])))),
          (Ast.TyApp ("nat", []))))
       ))
    |}]

let%expect_test "typecheck: function application" =
  let prg =
    {|
    (type nat ()
      (Z)
      (S (nat)))

    (def succ (-> nat nat)
      (fn (n nat) (S n)))

    (def two nat (succ (succ Z)))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDDef ("succ",
       (Ast.TyApp ("fun", [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))])),
       (Tast.TLam ("n", (Ast.TyApp ("nat", [])),
          (Tast.TApp (
             (Tast.TConst ("S",
                (Ast.TyApp ("fun",
                   [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                )),
             (Tast.TVar ("n", (Ast.TyApp ("nat", [])))), (Ast.TyApp ("nat", []))
             )),
          (Ast.TyApp ("fun", [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
          ))
       ))
    (Tast.TDDef ("two", (Ast.TyApp ("nat", [])),
       (Tast.TApp (
          (Tast.TConst ("succ",
             (Ast.TyApp ("fun",
                [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
             )),
          (Tast.TApp (
             (Tast.TConst ("succ",
                (Ast.TyApp ("fun",
                   [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                )),
             (Tast.TConst ("Z", (Ast.TyApp ("nat", [])))),
             (Ast.TyApp ("nat", [])))),
          (Ast.TyApp ("nat", []))))
       ))
    |}]

let%expect_test "typecheck: recursive function simple" =
  let prg =
    {|
    (type nat ()
      (Z)
      (S (nat)))

    (fun double (-> nat nat)
      ((Z) Z)
      (((S n)) (S (S (double n)))))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDFun ("double",
       (Ast.TyApp ("fun", [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))])),
       [([(Tast.TConst ("Z", (Ast.TyApp ("nat", []))))],
         (Tast.TConst ("Z", (Ast.TyApp ("nat", [])))));
         ([(Tast.TApp (
              (Tast.TConst ("S",
                 (Ast.TyApp ("fun",
                    [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                 )),
              (Tast.TVar ("n", (Ast.TyApp ("nat", [])))), (Ast.TyApp ("nat", []))
              ))
            ],
          (Tast.TApp (
             (Tast.TConst ("S",
                (Ast.TyApp ("fun",
                   [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                )),
             (Tast.TApp (
                (Tast.TConst ("S",
                   (Ast.TyApp ("fun",
                      [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                   )),
                (Tast.TApp (
                   (Tast.TConst ("double",
                      (Ast.TyApp ("fun",
                         [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                      )),
                   (Tast.TVar ("n", (Ast.TyApp ("nat", [])))),
                   (Ast.TyApp ("nat", [])))),
                (Ast.TyApp ("nat", [])))),
             (Ast.TyApp ("nat", [])))))
         ]
       ))
    |}]

let%expect_test "typecheck: recursive function two args" =
  let prg =
    {|
    (type nat ()
      (Z)
      (S (nat)))

    (fun plus (-> nat nat nat)
      ((Z n) n)
      (((S m) n) (S (plus m n))))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDFun ("plus",
       (Ast.TyApp ("fun",
          [(Ast.TyApp ("nat", []));
            (Ast.TyApp ("fun", [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]
               ))
            ]
          )),
       [([(Tast.TConst ("Z", (Ast.TyApp ("nat", []))));
           (Tast.TVar ("n", (Ast.TyApp ("nat", []))))],
         (Tast.TVar ("n", (Ast.TyApp ("nat", [])))));
         ([(Tast.TApp (
              (Tast.TConst ("S",
                 (Ast.TyApp ("fun",
                    [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                 )),
              (Tast.TVar ("m", (Ast.TyApp ("nat", [])))), (Ast.TyApp ("nat", []))
              ));
            (Tast.TVar ("n", (Ast.TyApp ("nat", []))))],
          (Tast.TApp (
             (Tast.TConst ("S",
                (Ast.TyApp ("fun",
                   [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                )),
             (Tast.TApp (
                (Tast.TApp (
                   (Tast.TConst ("plus",
                      (Ast.TyApp ("fun",
                         [(Ast.TyApp ("nat", []));
                           (Ast.TyApp ("fun",
                              [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]
                              ))
                           ]
                         ))
                      )),
                   (Tast.TVar ("m", (Ast.TyApp ("nat", [])))),
                   (Ast.TyApp ("fun",
                      [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                   )),
                (Tast.TVar ("n", (Ast.TyApp ("nat", [])))),
                (Ast.TyApp ("nat", [])))),
             (Ast.TyApp ("nat", [])))))
         ]
       ))
    |}]

let%expect_test "typecheck: polymorphic recursive function" =
  let prg =
    {|
    (type list ('a)
      (Nil)
      (Cons ('a (list 'a))))

    (fun tl (-> (list 'a) (list 'a))
      ((Nil) Nil)
      (((Cons x xs)) xs))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("list", ["'a"],
       [("Nil", []);
         ("Cons", [(Ast.TyVar "'a"); (Ast.TyApp ("list", [(Ast.TyVar "'a")]))])]
       ))
    (Tast.TDFun ("tl",
       (Ast.TyApp ("fun",
          [(Ast.TyApp ("list", [(Ast.TyVar "'a")]));
            (Ast.TyApp ("list", [(Ast.TyVar "'a")]))]
          )),
       [([(Tast.TConst ("Nil", (Ast.TyApp ("list", [(Ast.TyVar "'a")]))))],
         (Tast.TConst ("Nil", (Ast.TyApp ("list", [(Ast.TyVar "'a")])))));
         ([(Tast.TApp (
              (Tast.TApp (
                 (Tast.TConst ("Cons",
                    (Ast.TyApp ("fun",
                       [(Ast.TyVar "'a");
                         (Ast.TyApp ("fun",
                            [(Ast.TyApp ("list", [(Ast.TyVar "'a")]));
                              (Ast.TyApp ("list", [(Ast.TyVar "'a")]))]
                            ))
                         ]
                       ))
                    )),
                 (Tast.TVar ("x", (Ast.TyVar "'a"))),
                 (Ast.TyApp ("list", [(Ast.TyVar "'a")])))),
              (Tast.TVar ("xs", (Ast.TyApp ("list", [(Ast.TyVar "'a")])))),
              (Ast.TyApp ("list", [(Ast.TyVar "'a")]))))
            ],
          (Tast.TVar ("xs", (Ast.TyApp ("list", [(Ast.TyVar "'a")])))))
         ]
       ))
    |}]

let%expect_test "typecheck: pair type" =
  let prg =
    {|
    (type pair ('a 'b)
      (Pair ('a 'b)))

    (type nat ()
      (Z)
      (S (nat)))

    (type bool ()
      (True)
      (False))

    (def my_pair (pair nat bool) (Pair Z True))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("pair", ["'a"; "'b"],
       [("Pair", [(Ast.TyVar "'a"); (Ast.TyVar "'b")])]))
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDType ("bool", [], [("True", []); ("False", [])]))
    (Tast.TDDef ("my_pair",
       (Ast.TyApp ("pair", [(Ast.TyApp ("nat", [])); (Ast.TyApp ("bool", []))])),
       (Tast.TApp (
          (Tast.TApp (
             (Tast.TConst ("Pair",
                (Ast.TyApp ("fun",
                   [(Ast.TyApp ("nat", []));
                     (Ast.TyApp ("fun",
                        [(Ast.TyApp ("bool", []));
                          (Ast.TyApp ("pair",
                             [(Ast.TyApp ("nat", [])); (Ast.TyApp ("bool", []))]
                             ))
                          ]
                        ))
                     ]
                   ))
                )),
             (Tast.TConst ("Z", (Ast.TyApp ("nat", [])))),
             (Ast.TyApp ("fun",
                [(Ast.TyApp ("bool", []));
                  (Ast.TyApp ("pair",
                     [(Ast.TyApp ("nat", [])); (Ast.TyApp ("bool", []))]))
                  ]
                ))
             )),
          (Tast.TConst ("True", (Ast.TyApp ("bool", [])))),
          (Ast.TyApp ("pair", [(Ast.TyApp ("nat", [])); (Ast.TyApp ("bool", []))]
             ))
          ))
       ))
    |}]

let%expect_test "typecheck: nested polymorphic types" =
  let prg =
    {|
    (type nat ()
      (Z)
      (S (nat)))

    (type list ('a)
      (Nil)
      (Cons ('a (list 'a))))

    (def nested (list (list nat))
      (Cons (Cons Z Nil) Nil))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDType ("list", ["'a"],
       [("Nil", []);
         ("Cons", [(Ast.TyVar "'a"); (Ast.TyApp ("list", [(Ast.TyVar "'a")]))])]
       ))
    (Tast.TDDef ("nested",
       (Ast.TyApp ("list", [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))])),
       (Tast.TApp (
          (Tast.TApp (
             (Tast.TConst ("Cons",
                (Ast.TyApp ("fun",
                   [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]));
                     (Ast.TyApp ("fun",
                        [(Ast.TyApp ("list",
                            [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]));
                          (Ast.TyApp ("list",
                             [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]))
                          ]
                        ))
                     ]
                   ))
                )),
             (Tast.TApp (
                (Tast.TApp (
                   (Tast.TConst ("Cons",
                      (Ast.TyApp ("fun",
                         [(Ast.TyApp ("nat", []));
                           (Ast.TyApp ("fun",
                              [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]));
                                (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]
                              ))
                           ]
                         ))
                      )),
                   (Tast.TConst ("Z", (Ast.TyApp ("nat", [])))),
                   (Ast.TyApp ("fun",
                      [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]));
                        (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]
                      ))
                   )),
                (Tast.TConst ("Nil",
                   (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))])))),
                (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))])))),
             (Ast.TyApp ("fun",
                [(Ast.TyApp ("list",
                    [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]));
                  (Ast.TyApp ("list",
                     [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]))
                  ]
                ))
             )),
          (Tast.TConst ("Nil",
             (Ast.TyApp ("list",
                [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]))
             )),
          (Ast.TyApp ("list", [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]))
          ))
       ))
    |}]

let%expect_test "typecheck: equality" =
  let prg =
    {|
    (type nat ()
      (Z)
      (S (nat)))

    (theorem zero_eq_zero
      (= Z Z))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDTheorem ("zero_eq_zero",
       (Tast.TEq ((Tast.TConst ("Z", (Ast.TyApp ("nat", [])))),
          (Tast.TConst ("Z", (Ast.TyApp ("nat", [])))), (Ast.TyApp ("bool", []))
          ))
       ))
    |}]

let%expect_test "typecheck: if expression" =
  let prg =
    {|
    (type bool ()
      (True)
      (False))

    (type nat ()
      (Z)
      (S (nat)))

    (def test nat
      (if True Z (S Z)))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("bool", [], [("True", []); ("False", [])]))
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDDef ("test", (Ast.TyApp ("nat", [])),
       (Tast.TIf ((Tast.TConst ("True", (Ast.TyApp ("bool", [])))),
          (Tast.TConst ("Z", (Ast.TyApp ("nat", [])))),
          (Tast.TApp (
             (Tast.TConst ("S",
                (Ast.TyApp ("fun",
                   [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                )),
             (Tast.TConst ("Z", (Ast.TyApp ("nat", [])))),
             (Ast.TyApp ("nat", [])))),
          (Ast.TyApp ("nat", []))))
       ))
    |}]

let%expect_test "typecheck: using defined function" =
  let prg =
    {|
    (type nat ()
      (Z)
      (S (nat)))

    (type list ('a)
      (Nil)
      (Cons ('a (list 'a))))

    (fun tl (-> (list 'a) (list 'a))
      ((Nil) Nil)
      (((Cons x xs)) xs))

    (def mylist (list nat)
      (Cons Z (Cons (S Z) Nil)))

    (def tail_of_mylist (list nat)
      (tl mylist))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDType ("list", ["'a"],
       [("Nil", []);
         ("Cons", [(Ast.TyVar "'a"); (Ast.TyApp ("list", [(Ast.TyVar "'a")]))])]
       ))
    (Tast.TDFun ("tl",
       (Ast.TyApp ("fun",
          [(Ast.TyApp ("list", [(Ast.TyVar "'a")]));
            (Ast.TyApp ("list", [(Ast.TyVar "'a")]))]
          )),
       [([(Tast.TConst ("Nil", (Ast.TyApp ("list", [(Ast.TyVar "'a")]))))],
         (Tast.TConst ("Nil", (Ast.TyApp ("list", [(Ast.TyVar "'a")])))));
         ([(Tast.TApp (
              (Tast.TApp (
                 (Tast.TConst ("Cons",
                    (Ast.TyApp ("fun",
                       [(Ast.TyVar "'a");
                         (Ast.TyApp ("fun",
                            [(Ast.TyApp ("list", [(Ast.TyVar "'a")]));
                              (Ast.TyApp ("list", [(Ast.TyVar "'a")]))]
                            ))
                         ]
                       ))
                    )),
                 (Tast.TVar ("x", (Ast.TyVar "'a"))),
                 (Ast.TyApp ("list", [(Ast.TyVar "'a")])))),
              (Tast.TVar ("xs", (Ast.TyApp ("list", [(Ast.TyVar "'a")])))),
              (Ast.TyApp ("list", [(Ast.TyVar "'a")]))))
            ],
          (Tast.TVar ("xs", (Ast.TyApp ("list", [(Ast.TyVar "'a")])))))
         ]
       ))
    (Tast.TDDef ("mylist", (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))])),
       (Tast.TApp (
          (Tast.TApp (
             (Tast.TConst ("Cons",
                (Ast.TyApp ("fun",
                   [(Ast.TyApp ("nat", []));
                     (Ast.TyApp ("fun",
                        [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]));
                          (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]
                        ))
                     ]
                   ))
                )),
             (Tast.TConst ("Z", (Ast.TyApp ("nat", [])))),
             (Ast.TyApp ("fun",
                [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]));
                  (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]
                ))
             )),
          (Tast.TApp (
             (Tast.TApp (
                (Tast.TConst ("Cons",
                   (Ast.TyApp ("fun",
                      [(Ast.TyApp ("nat", []));
                        (Ast.TyApp ("fun",
                           [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]));
                             (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]
                           ))
                        ]
                      ))
                   )),
                (Tast.TApp (
                   (Tast.TConst ("S",
                      (Ast.TyApp ("fun",
                         [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                      )),
                   (Tast.TConst ("Z", (Ast.TyApp ("nat", [])))),
                   (Ast.TyApp ("nat", [])))),
                (Ast.TyApp ("fun",
                   [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]));
                     (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]
                   ))
                )),
             (Tast.TConst ("Nil", (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))
                )),
             (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))])))),
          (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))))
       ))
    (Tast.TDDef ("tail_of_mylist",
       (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))])),
       (Tast.TApp (
          (Tast.TConst ("tl",
             (Ast.TyApp ("fun",
                [(Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]));
                  (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))]
                ))
             )),
          (Tast.TConst ("mylist", (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))
             )),
          (Ast.TyApp ("list", [(Ast.TyApp ("nat", []))]))))
       ))
    |}]

let%expect_test "typecheck: polymorphic lambda" =
  let prg = {|
    (def id (-> 'a 'a)
      (fn (x 'a) x))
  |} in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDDef ("id", (Ast.TyApp ("fun", [(Ast.TyVar "'a"); (Ast.TyVar "'a")])),
       (Tast.TLam ("x", (Ast.TyVar "'a"), (Tast.TVar ("x", (Ast.TyVar "'a"))),
          (Ast.TyApp ("fun", [(Ast.TyVar "'a"); (Ast.TyVar "'a")]))))
       ))
    |}]

let%expect_test "typecheck: higher order function" =
  let prg =
    {|
    (type nat ()
      (Z)
      (S (nat)))

    (def apply (-> (-> nat nat) nat nat)
      (fn (f (-> nat nat))
      (fn (x nat)
        (f x))))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect
    {|
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDDef ("apply",
       (Ast.TyApp ("fun",
          [(Ast.TyApp ("fun", [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]
              ));
            (Ast.TyApp ("fun", [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]
               ))
            ]
          )),
       (Tast.TLam ("f",
          (Ast.TyApp ("fun", [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))])),
          (Tast.TLam ("x", (Ast.TyApp ("nat", [])),
             (Tast.TApp (
                (Tast.TVar ("f",
                   (Ast.TyApp ("fun",
                      [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
                   )),
                (Tast.TVar ("x", (Ast.TyApp ("nat", [])))),
                (Ast.TyApp ("nat", [])))),
             (Ast.TyApp ("fun",
                [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
             )),
          (Ast.TyApp ("fun",
             [(Ast.TyApp ("fun",
                 [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]));
               (Ast.TyApp ("fun",
                  [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]))
               ]
             ))
          ))
       ))
    |}]

let%expect_test "elab" =
  let prg =
    {|
    (type mynat ()
      (Zmy)
      (Smy (mynat)))

    (def mnat_id (-> mynat mynat)
        (fn (n mynat) (n)))

    (fun mnat_id2 (-> mynat mynat)
        ((Zmy) Zmy)
        (((Smy n)) (Smy n)))

    (fun mnat_plus (-> mynat (-> mynat mynat))
        ((Zmy n) Zmy)
        (((Smy m) n) (Smy (mnat_plus m n))))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  let () = Elab.elab_program tast in
  (Kernel.the_inductives
  |> Hashtbl.iter @@ fun k (v : Kernel.inductive_def) ->
     print_endline k;
     Derived.pp_thm v.recursion;
     Derived.pp_thm v.induction);
  (Kernel.the_term_constants
  |> Hashtbl.iter @@ fun k (v : Kernel.hol_type) ->
     print_endline k;
     print_endline @@ Printing.pretty_print_hol_type v);
  (!Kernel.the_definitions |> List.iter @@ fun t -> Derived.pp_thm t);
  (!Kernel.the_axioms |> List.iter @@ fun t -> Derived.pp_thm t);
  [%expect
    {|
    mynat
    ========================================
    ∀Zmy_case. ∀Smy_case. ∃g. g Zmy = Zmy_case ∧ (∀x0. g (Smy x0) = Smy_case x0 (g x0))

    ========================================
    ∀P. P Zmy ==> (∀n0. P n0 ==> P (Smy n0)) ==> ∀x. P x

    nat
    ========================================
    ∀Zero_case. ∀Suc_case. ∃g. g Zero = Zero_case ∧ (∀x0. g (Suc x0) = Suc_case x0 (g x0))

    ========================================
    ∀P. P Zero ==> (∀n0. P n0 ==> P (Suc n0)) ==> ∀x. P x

    Zmy
    mynat
    mnat_id
    (mynat -> mynat)
    \/
    (bool -> (bool -> bool))
    ~
    (bool -> bool)
    mnat_plus
    (mynat -> (mynat -> mynat))
    !
    ((a -> bool) -> bool)
    =
    (A -> (A -> bool))
    /\
    (bool -> (bool -> bool))
    T
    bool
    F
    bool
    mnat_id2
    (mynat -> mynat)
    Suc
    (nat -> nat)
    Smy
    (mynat -> mynat)
    Zero
    nat
    plus
    (nat -> (nat -> nat))
    ?
    ((a -> bool) -> bool)
    ==>
    (bool -> (bool -> bool))
    ========================================
    mnat_id = (λn. n)

    ========================================
    \/ = (λp. λq. ∀r. (p ==> r) ==> (q ==> r) ==> r)

    ========================================
    ? = (λP. ¬(∀x. ¬(P x)))

    ========================================
    ~ = (λp. p ==> F)

    ========================================
    F = (∀p. p)

    ========================================
    ==> = (λp. λq. p ∧ q = p)

    ========================================
    /\ = (λp. λq. (λf. f p q) = (λf. f T T))

    ========================================
    ! = (λP. P = (λx. T))

    ========================================
    T = (λp. p) = (λp. p)

    ========================================
    mnat_plus Zmy = (λn. Zmy) ∧ (∀x0. mnat_plus (Smy x0) = (λn. Smy (mnat_plus x0 n)))

    ========================================
    mnat_id2 Zmy = Zmy ∧ (∀x0. mnat_id2 (Smy x0) = Smy x0)

    ========================================
    ∀x0. ∀y0. Smy x0 = Smy y0 ==> x0 = y0

    ========================================
    ∀y0. ¬Zmy = Smy y0

    ========================================
    ∀Zmy_case. ∀Smy_case. ∃g. g Zmy = Zmy_case ∧ (∀x0. g (Smy x0) = Smy_case x0 (g x0))

    ========================================
    ∀P. P Zmy ==> (∀n0. P n0 ==> P (Smy n0)) ==> ∀x. P x

    ========================================
    plus Zero = (λn. n) ∧ (∀x0. plus (Suc x0) = (λn. Suc (plus x0 n)))

    ========================================
    ∀x0. ∀y0. Suc x0 = Suc y0 ==> x0 = y0

    ========================================
    ∀y0. ¬Zero = Suc y0

    ========================================
    ∀Zero_case. ∀Suc_case. ∃g. g Zero = Zero_case ∧ (∀x0. g (Suc x0) = Suc_case x0 (g x0))

    ========================================
    ∀P. P Zero ==> (∀n0. P n0 ==> P (Suc n0)) ==> ∀x. P x

    ========================================
    ∀P. (∃x. P x) ==> P (@ (λx. P x))

    ========================================
    ∀p. p ∨ ¬p
    |}]

let%expect_test "elab2" =
  let prg =
    {|

  (type mnat ()
    (Zm)
    (Sm (mnat)))
  (type list ('a)
    (Nil)
    (Cons ('a (list 'a))))
  (type option ('a)
    (None)
    (Some ('a)))
  (fun length (-> (list 'a) mnat)
    ( (Nil) Zm)
    ( ((Cons x xs)) (Sm (length xs))))
  (fun head (-> (list 'a) (option 'a))
    ( (Nil) None)
    ( ((Cons x xs)) (Some x)))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  let () = Elab.elab_program tast in
  let length_def = Hashtbl.find Kernel.the_specifications "length" in
  let head_def = Hashtbl.find Kernel.the_specifications "head" in
  Derived.pp_thm length_def;
  Derived.pp_thm head_def;
  [%expect
    {|
    ========================================
    length Nil = Zm ∧ (∀x0. ∀x1. length (Cons x0 x1) = Sm (length x1))

    ========================================
    head Nil = None ∧ (∀x0. ∀x1. head (Cons x0 x1) = Some x0)
    |}]
