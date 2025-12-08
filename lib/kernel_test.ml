open Kernel
open Util

let p = Var ("P", bool_ty)
let q = Var ("Q", bool_ty)
let r = Var ("R", bool_ty)

let f = Var ("f", TyCon ("fun", [bool_ty; bool_ty]))
let g = Var ("g", TyCon ("fun", [bool_ty; bool_ty]))

let print_term = 
    Fun.compose print_endline show_term

let print_thm =
    Fun.compose print_endline show_thm

let print_thm_result =
    Format.pp_print_result ~ok:pp_thm ~error:pp_kernel_error Format.std_formatter

let print_term_result =
    Format.pp_print_result ~ok:pp_term ~error:pp_kernel_error Format.std_formatter

(* Template
let%expect_test "" =
    let thm1 = _ in
    print_thm_result thm1;
    [%expect {||}]
   
 *)

let%expect_test "assume_simple" =
    let thm1 = assume p in
    print_thm_result thm1;
    [%expect {|
      (Sequent ([(Var ("P", (TyCon ("bool", []))))],
         (Var ("P", (TyCon ("bool", []))))))
      |}]

let%expect_test "refl_simple" =
    let thm1 = refl p in 
    print_thm_result thm1;
    [%expect {|
      (Sequent ([],
         (App (
            (App (
               (Const ("=",
                  (TyCon ("fun",
                     [(TyCon ("bool", []));
                       (TyCon ("fun", [(TyCon ("bool", [])); (TyCon ("bool", []))]
                          ))
                       ]
                     ))
                  )),
               (Var ("P", (TyCon ("bool", [])))))),
            (Var ("P", (TyCon ("bool", []))))))
         ))
      |}]

let%expect_test "trans_simple" =
    let pq_eq = unwrap (safe_make_eq p q) in
    let qr_eq = unwrap (safe_make_eq q r) in
    let thm1 = unwrap (assume pq_eq) in
    let thm2 = unwrap (assume qr_eq) in
    let thm3 = trans thm1 thm2 in
    print_thm_result thm3;
    [%expect {|
      (Sequent (
         [(App (
             (App (
                (Const ("=",
                   (TyCon ("fun",
                      [(TyCon ("bool", []));
                        (TyCon ("fun", [(TyCon ("bool", [])); (TyCon ("bool", []))]
                           ))
                        ]
                      ))
                   )),
                (Var ("P", (TyCon ("bool", [])))))),
             (Var ("Q", (TyCon ("bool", []))))));
           (App (
              (App (
                 (Const ("=",
                    (TyCon ("fun",
                       [(TyCon ("bool", []));
                         (TyCon ("fun",
                            [(TyCon ("bool", [])); (TyCon ("bool", []))]))
                         ]
                       ))
                    )),
                 (Var ("Q", (TyCon ("bool", [])))))),
              (Var ("R", (TyCon ("bool", []))))))
           ],
         (App (
            (App (
               (Const ("=",
                  (TyCon ("fun",
                     [(TyCon ("bool", []));
                       (TyCon ("fun", [(TyCon ("bool", [])); (TyCon ("bool", []))]
                          ))
                       ]
                     ))
                  )),
               (Var ("P", (TyCon ("bool", [])))))),
            (Var ("R", (TyCon ("bool", []))))))
         ))
      |}]
