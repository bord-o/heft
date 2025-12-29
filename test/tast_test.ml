open Holinone
open Parse

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

