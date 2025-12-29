open Elaborator

let%expect_test "parse_simple" =
  let prg = {|
    (type nat ()
      (Z)
      (S (nat)))

    (def zero nat Z)
  |} in
  let ast = parse_string prg in
  List.iter (fun d -> print_endline (Ast.show_decl d)) ast;
  [%expect {|
    (Ast.DType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Ast.DDef ("zero", (Ast.TyApp ("nat", [])), (Ast.Var "Z")))
    |}]

let%expect_test "parse_list" =
  let prg = {|
    (type list ('a)
      (Nil)
      (Cons ('a (list 'a))))

    (fun tl (-> (list 'a) (list 'a))
      ((Nil) Nil)
      (((Cons x xs)) xs))
  |} in
  let ast = parse_string prg in
  List.iter (fun d -> print_endline (Ast.show_decl d)) ast;
  [%expect {|
    (Ast.DType ("list", ["'a"],
       [("Nil", []);
         ("Cons", [(Ast.TyVar "'a"); (Ast.TyApp ("list", [(Ast.TyVar "'a")]))])]
       ))
    (Ast.DFun ("tl",
       (Ast.TyApp ("fun",
          [(Ast.TyApp ("list", [(Ast.TyVar "'a")]));
            (Ast.TyApp ("list", [(Ast.TyVar "'a")]))]
          )),
       [([(Ast.Var "Nil")], (Ast.Var "Nil"));
         ([(Ast.App ((Ast.App ((Ast.Var "Cons"), (Ast.Var "x"))), (Ast.Var "xs")
              ))
            ],
          (Ast.Var "xs"))
         ]
       ))
    |}]

let%expect_test "parse_plus" =
  let prg = {|
    (type nat ()
      (Z)
      (S (nat)))

    (fun plus (-> nat nat nat)
      ((Z n) n)
      (((S m) n) (S (plus m n))))
  |} in
  let ast = parse_string prg in
  List.iter (fun d -> print_endline (Ast.show_decl d)) ast;
  [%expect {|
    (Ast.DType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Ast.DFun ("plus",
       (Ast.TyApp ("fun",
          [(Ast.TyApp ("nat", []));
            (Ast.TyApp ("fun", [(Ast.TyApp ("nat", [])); (Ast.TyApp ("nat", []))]
               ))
            ]
          )),
       [([(Ast.Var "Z"); (Ast.Var "n")], (Ast.Var "n"));
         ([(Ast.App ((Ast.Var "S"), (Ast.Var "m"))); (Ast.Var "n")],
          (Ast.App ((Ast.Var "S"),
             (Ast.App ((Ast.App ((Ast.Var "plus"), (Ast.Var "m"))), (Ast.Var "n")
                ))
             )))
         ]
       ))
    |}]

let%expect_test "typecheck_simple" =
  let prg = {|
    (type nat ()
      (Z)
      (S (nat)))

    (def zero nat Z)
  |} in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect {|
    (Tast.TDType ("nat", [], [("Z", []); ("S", [(Ast.TyApp ("nat", []))])]))
    (Tast.TDDef ("zero", (Ast.TyApp ("nat", [])),
       (Tast.TConst ("Z", (Ast.TyApp ("nat", []))))))
    |}]

let%expect_test "typecheck_tl" =
  let prg = {|
    (type mynat ()
        (Z)
        (S (mynat)))

    (type list ('a)
      (Nil)
      (Cons ('a (list 'a))))

    (fun tl (-> (list 'a) (list 'a))
      ((Nil) Nil)
      (((Cons x xs)) xs))

    (def mylist (list mynat)
     (Cons Z (Cons Z Nil)))

    (def applied (-> 'a (list mynat))
        (fn (x 'a) (tl mylist)))
  |} in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  List.iter (fun d -> print_endline (Tast.show_tdecl d)) tast;
  [%expect {|
    (Tast.TDType ("mynat", [], [("Z", []); ("S", [(Ast.TyApp ("mynat", []))])]))
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
    (Tast.TDDef ("applied", (Ast.TyApp ("list", [(Ast.TyApp ("mynat", []))])),
       (Tast.TConst ("Nil", (Ast.TyApp ("list", [(Ast.TyApp ("mynat", []))]))))))
    |}]
