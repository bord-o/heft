(* (* [@@@ocamlformat "disable"] *) *)
open Heft
open Kernel
open Tactic
open Auto
open Result.Syntax
open Effect

let () =
  print_newline ();
  print_newline ()

let auto =
  with_no_automation_trace
    (Auto.with_dfs'
       (pick
          [
            simp;
            gen;
            intro;
            truth;
            assumption;
            neg_intro;
            elim_disj_asm;
            conj;
            elim_conj_asm;
            elim_exists_asm;
            eq_true_elim_asm;
            false_elim;
            or_;
            with_assumptions (with_first_term apply_asm);
            with_assumptions apply;
            simp_asm;
            cond;
            discriminate;
          ]))

[%%inductive type corner_pos = URF | UFL | ULB | UBR | DFR | DLF | DBL | DRB]

[%%inductive
type edge_pos = UR | UF | UL | UB | DR | DF | DL | DB | FR | FL | BL | BR]

[%%inductive type corner_ori = C0 | C1 | C2]
[%%inductive type edge_ori = E0 | E1]
[%%inductive type corner_cubie = Corner of corner_pos * corner_ori]
[%%inductive type edge_cubie = Edge of edge_pos * edge_ori]

[%%inductive
type corners =
  | Corners of
      corner_cubie (* slot 1: URF home *)
      * corner_cubie (* slot 2: UFL home *)
      * corner_cubie (* slot 3: ULB home *)
      * corner_cubie (* slot 4: UBR home *)
      * corner_cubie (* slot 5: DFR home *)
      * corner_cubie (* slot 6: DLF home *)
      * corner_cubie (* slot 7: DBL home *)
      * corner_cubie (* slot 8: DRB home *)]

[%%inductive
type edges =
  | Edges of
      edge_cubie (* slot 1:  UR home *)
      * edge_cubie (* slot 2:  UF home *)
      * edge_cubie (* slot 3:  UL home *)
      * edge_cubie (* slot 4:  UB home *)
      * edge_cubie (* slot 5:  DR home *)
      * edge_cubie (* slot 6:  DF home *)
      * edge_cubie (* slot 7:  DL home *)
      * edge_cubie (* slot 8:  DB home *)
      * edge_cubie (* slot 9:  FR home *)
      * edge_cubie (* slot 10: FL home *)
      * edge_cubie (* slot 11: BL home *)
      * edge_cubie (* slot 12: BR home *)]

[%%inductive type cube = Cube of corners * edges]

let%def solved_cube : cube =
  Cube
    ( Corners
        ( Corner (URF, C0),
          Corner (UFL, C0),
          Corner (ULB, C0),
          Corner (UBR, C0),
          Corner (DFR, C0),
          Corner (DLF, C0),
          Corner (DBL, C0),
          Corner (DRB, C0) ),
      Edges
        ( Edge (UR, E0),
          Edge (UF, E0),
          Edge (UL, E0),
          Edge (UB, E0),
          Edge (DR, E0),
          Edge (DF, E0),
          Edge (DL, E0),
          Edge (DB, E0),
          Edge (FR, E0),
          Edge (FL, E0),
          Edge (BL, E0),
          Edge (BR, E0) ) )

let%def co_add (a : corner_ori) (b : corner_ori) : corner_ori =
  match a with
  | C0 -> b
  | C1 -> ( match b with C0 -> C1 | C1 -> C2 | C2 -> C0)
  | C2 -> ( match b with C0 -> C2 | C1 -> C0 | C2 -> C1)

let%def eo_add (a : edge_ori) (b : edge_ori) : edge_ori =
  match a with E0 -> b | E1 -> ( match b with E0 -> E1 | E1 -> E0)

let%thm co_add_C0_l (x : corner_ori) = co_add C0 x = x
and proof = (induct @>> auto) [@quiet] [@simp]

let%thm co_add_C0_r (x : corner_ori) = co_add x C0 = x
and proof = (induct @>> auto) [@quiet] [@simp]

let%thm co_add_assoc (a : corner_ori) (b : corner_ori) (c : corner_ori) =
  co_add (co_add a b) c = co_add a (co_add b c)

and proof =
  begin
    intros
    >> with_term [%term (a : corner_ori)] destruct_elim
       @>> with_term [%term (b : corner_ori)] destruct_elim
       @>> with_term [%term (c : corner_ori)] destruct_elim
       @>> auto
  end
  [@quiet]

let%thm co_add_three_same (x : corner_ori) = co_add x (co_add x x) = C0

and proof =
  begin
    intros >> with_term [%term (x : corner_ori)] destruct_elim @>> auto
  end
  [@quiet]

let%thm co_add_C1_C2 = co_add C1 C2 = C0
and proof = auto [@quiet]

let%thm co_add_C2_C1 = co_add C2 C1 = C0
and proof = auto [@quiet]

let%thm eo_add_E0_r (x : edge_ori) = eo_add x E0 = x
and proof = (induct @>> auto) [@quiet] [@simp]

let%thm eo_add_E1_E1 = eo_add E1 E1 = E0
and proof = auto [@quiet]

let%thm eo_add_self (x : edge_ori) = eo_add x x = E0
and proof = (induct @>> auto) [@quiet]

let%def move_U (c : cube) : cube =
  match c with
  | Cube (corners, edges) -> (
      match (corners : corners) with
      | Corners (c1, c2, c3, c4, c5, c6, c7, c8) -> (
          match (edges : edges) with
          | Edges (e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12) ->
              Cube
                ( Corners (c2, c3, c4, c1, c5, c6, c7, c8),
                  Edges (e2, e3, e4, e1, e5, e6, e7, e8, e9, e10, e11, e12) )))

let%thm move_U_id (c : cube) = move_U (move_U (move_U (move_U c))) = c

and proof =
  begin
    gen
    >> with_term [%term (c : cube)] destruct_elim
    >> with_term [%term (a0 : corners)] destruct_elim
    >> with_term [%term (a1 : edges)] destruct_elim
    >> simp
  end
  [@quiet]

let%def move_D (c : cube) : cube =
  match c with
  | Cube (corners, edges) -> (
      match (corners : corners) with
      | Corners (c1, c2, c3, c4, c5, c6, c7, c8) -> (
          match (edges : edges) with
          | Edges (e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12) ->
              Cube
                ( Corners (c1, c2, c3, c4, c6, c7, c8, c5),
                  Edges (e1, e2, e3, e4, e6, e7, e8, e5, e9, e10, e11, e12) )))

let%thm move_D_id (c : cube) = move_D (move_D (move_D (move_D c))) = c

and proof =
  begin
    gen
    >> with_term [%term (c : cube)] destruct_elim
    >> with_term [%term (a0 : corners)] destruct_elim
    >> with_term [%term (a1 : edges)] destruct_elim
    >> simp
  end
  [@quiet]

let%def move_R (c : cube) : cube =
  match c with
  | Cube (corners, edges) -> (
      match (corners : corners) with
      | Corners (c1, c2, c3, c4, c5, c6, c7, c8) -> (
          match (edges : edges) with
          | Edges (e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12) -> (
              match (c1 : corner_cubie) with
              | Corner (p1, o1) -> (
                  match (c4 : corner_cubie) with
                  | Corner (p4, o4) -> (
                      match (c5 : corner_cubie) with
                      | Corner (p5, o5) -> (
                          match (c8 : corner_cubie) with
                          | Corner (p8, o8) ->
                              Cube
                                ( Corners
                                    ( Corner (p5, co_add o5 C2),
                                      c2,
                                      c3,
                                      Corner (p1, co_add o1 C1),
                                      Corner (p8, co_add o8 C1),
                                      c6,
                                      c7,
                                      Corner (p4, co_add o4 C2) ),
                                  Edges
                                    ( e12,
                                      e2,
                                      e3,
                                      e4,
                                      e9,
                                      e6,
                                      e7,
                                      e8,
                                      e1,
                                      e10,
                                      e11,
                                      e5 ) )))))))

let%thm co_add_1212 (x : corner_ori) =
  co_add (co_add (co_add (co_add x C1) C2) C1) C2 = x

and proof = (induct @>> auto) [@simp] [@quiet]

let%thm co_add_2121 (x : corner_ori) =
  co_add (co_add (co_add (co_add x C2) C1) C2) C1 = x

and proof = (induct @>> auto) [@simp] [@quiet]

let%thm move_R_id (c : cube) = move_R (move_R (move_R (move_R c))) = c

and proof =
  begin
    gen
    >> with_term [%term (c : cube)] destruct_elim
       @>> with_term [%term (a0 : corners)] destruct_elim
       @>> with_term [%term (a1 : edges)] destruct_elim
       @>> with_term [%term (a0 : corner_cubie)] destruct_elim
       @>> with_term [%term (a3 : corner_cubie)] destruct_elim
       @>> with_term [%term (a4 : corner_cubie)] destruct_elim
       @>> with_term [%term (a7 : corner_cubie)] destruct_elim
       @>> simp ~exclude:[ "co_add" ]
  end
  [@quiet]

let%def move_L (c : cube) : cube =
  match c with
  | Cube (corners, edges) -> (
      match (corners : corners) with
      | Corners (c1, c2, c3, c4, c5, c6, c7, c8) -> (
          match (edges : edges) with
          | Edges (e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12) -> (
              match (c2 : corner_cubie) with
              | Corner (p2, o2) -> (
                  match (c3 : corner_cubie) with
                  | Corner (p3, o3) -> (
                      match (c6 : corner_cubie) with
                      | Corner (p6, o6) -> (
                          match (c7 : corner_cubie) with
                          | Corner (p7, o7) ->
                              Cube
                                ( Corners
                                    ( c1,
                                      Corner (p3, co_add o3 C2),
                                      Corner (p7, co_add o7 C1),
                                      c4,
                                      c5,
                                      Corner (p2, co_add o2 C1),
                                      Corner (p6, co_add o6 C2),
                                      c8 ),
                                  Edges
                                    ( e1,
                                      e2,
                                      e11,
                                      e4,
                                      e5,
                                      e6,
                                      e10,
                                      e8,
                                      e9,
                                      e3,
                                      e7,
                                      e12 ) )))))))

let%thm move_L_id (c : cube) = move_L (move_L (move_L (move_L c))) = c

and proof =
  begin
    gen
    >> with_term [%term (c : cube)] destruct_elim
       @>> with_term [%term (a0 : corners)] destruct_elim
       @>> with_term [%term (a1 : edges)] destruct_elim
       @>> with_term [%term (a1 : corner_cubie)] destruct_elim
       @>> with_term [%term (a2 : corner_cubie)] destruct_elim
       @>> with_term [%term (a5 : corner_cubie)] destruct_elim
       @>> with_term [%term (a6 : corner_cubie)] destruct_elim
       @>> simp ~exclude:[ "co_add" ]
  end
  [@quiet]

let%def move_F (c : cube) : cube =
  match c with
  | Cube (corners, edges) -> (
      match (corners : corners) with
      | Corners (c1, c2, c3, c4, c5, c6, c7, c8) -> (
          match (edges : edges) with
          | Edges (e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12) -> (
              match (c1 : corner_cubie) with
              | Corner (p1, o1) -> (
                  match (c2 : corner_cubie) with
                  | Corner (p2, o2) -> (
                      match (c5 : corner_cubie) with
                      | Corner (p5, o5) -> (
                          match (c6 : corner_cubie) with
                          | Corner (p6, o6) -> (
                              match (e2 : edge_cubie) with
                              | Edge (q2, f2) -> (
                                  match (e6 : edge_cubie) with
                                  | Edge (q6, f6) -> (
                                      match (e9 : edge_cubie) with
                                      | Edge (q9, f9) -> (
                                          match (e10 : edge_cubie) with
                                          | Edge (q10, f10) ->
                                              Cube
                                                ( Corners
                                                    ( Corner (p2, co_add o2 C1),
                                                      Corner (p6, co_add o6 C2),
                                                      c3,
                                                      c4,
                                                      Corner (p1, co_add o1 C2),
                                                      Corner (p5, co_add o5 C1),
                                                      c7,
                                                      c8 ),
                                                  Edges
                                                    ( e1,
                                                      Edge (q9, eo_add f9 E1),
                                                      e3,
                                                      e4,
                                                      e5,
                                                      Edge (q10, eo_add f10 E1),
                                                      e7,
                                                      e8,
                                                      Edge (q6, eo_add f6 E1),
                                                      Edge (q2, eo_add f2 E1),
                                                      e11,
                                                      e12 ) )))))))))))

let%thm eo_add_1111 (x : edge_ori) =
  eo_add (eo_add (eo_add (eo_add x E1) E1) E1) E1 = x

and proof = (induct @>> auto) [@simp] [@quiet]

let%thm move_F_id (c : cube) = move_F (move_F (move_F (move_F c))) = c

and proof =
  begin
    gen
    >> with_term [%term (c : cube)] destruct_elim
       @>> with_term [%term (a0 : corners)] destruct_elim
       @>> with_term [%term (a1 : edges)] destruct_elim
       @>> with_term [%term (a0 : corner_cubie)] destruct_elim
       @>> with_term [%term (a1 : corner_cubie)] destruct_elim
       @>> with_term [%term (a4 : corner_cubie)] destruct_elim
       @>> with_term [%term (a5 : corner_cubie)] destruct_elim
       @>> with_term [%term (a1 : edge_cubie)] destruct_elim
       @>> with_term [%term (a5 : edge_cubie)] destruct_elim
       @>> with_term [%term (a8 : edge_cubie)] destruct_elim
       @>> with_term [%term (a9 : edge_cubie)] destruct_elim
       @>> simp ~exclude:[ "co_add"; "eo_add" ]
  end
  [@quiet]

let%def move_B (c : cube) : cube =
  match c with
  | Cube (corners, edges) -> (
      match (corners : corners) with
      | Corners (c1, c2, c3, c4, c5, c6, c7, c8) -> (
          match (edges : edges) with
          | Edges (e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12) -> (
              match (c3 : corner_cubie) with
              | Corner (p3, o3) -> (
                  match (c4 : corner_cubie) with
                  | Corner (p4, o4) -> (
                      match (c7 : corner_cubie) with
                      | Corner (p7, o7) -> (
                          match (c8 : corner_cubie) with
                          | Corner (p8, o8) -> (
                              match (e4 : edge_cubie) with
                              | Edge (q4, f4) -> (
                                  match (e8 : edge_cubie) with
                                  | Edge (q8, f8) -> (
                                      match (e11 : edge_cubie) with
                                      | Edge (q11, f11) -> (
                                          match (e12 : edge_cubie) with
                                          | Edge (q12, f12) ->
                                              Cube
                                                ( Corners
                                                    ( c1,
                                                      c2,
                                                      Corner (p4, co_add o4 C1),
                                                      Corner (p8, co_add o8 C2),
                                                      c5,
                                                      c6,
                                                      Corner (p3, co_add o3 C2),
                                                      Corner (p7, co_add o7 C1)
                                                    ),
                                                  Edges
                                                    ( e1,
                                                      e2,
                                                      e3,
                                                      Edge (q12, eo_add f12 E1),
                                                      e5,
                                                      e6,
                                                      e7,
                                                      Edge (q11, eo_add f11 E1),
                                                      e9,
                                                      e10,
                                                      Edge (q4, eo_add f4 E1),
                                                      Edge (q8, eo_add f8 E1) )
                                                )))))))))))

let%thm move_B_id (c : cube) = move_B (move_B (move_B (move_B c))) = c

and proof =
  begin
    gen
    >> with_term [%term (c : cube)] destruct_elim
       @>> with_term [%term (a0 : corners)] destruct_elim
       @>> with_term [%term (a1 : edges)] destruct_elim
       @>> with_term [%term (a2 : corner_cubie)] destruct_elim
       @>> with_term [%term (a3 : corner_cubie)] destruct_elim
       @>> with_term [%term (a6 : corner_cubie)] destruct_elim
       @>> with_term [%term (a7 : corner_cubie)] destruct_elim
       @>> with_term [%term (a3 : edge_cubie)] destruct_elim
       @>> with_term [%term (a7 : edge_cubie)] destruct_elim
       @>> with_term [%term (a10 : edge_cubie)] destruct_elim
       @>> with_term [%term (a11 : edge_cubie)] destruct_elim
       @>> simp ~exclude:[ "co_add"; "eo_add" ]
  end
  [@quiet]

let%def cc_ori (corner : corner_cubie) : corner_ori =
  match corner with Corner (pos, ori) -> ori

(*sum of corner orientations*)
let%def co_sum (c : cube) : corner_ori =
  match c with
  | Cube (corners, edges) -> (
      match (corners : corners) with
      | Corners (c0, c1, c2, c3, c4, c5, c6, c7) ->
          co_add (cc_ori c0)
            (co_add (cc_ori c1)
               (co_add (cc_ori c2)
                  (co_add (cc_ori c3)
                     (co_add (cc_ori c4)
                        (co_add (cc_ori c5) (co_add (cc_ori c6) (cc_ori c7)))))))
      )

let%thm co_sum_solved = co_sum solved_cube = C0
and proof = simp ~exclude:[ "co_add"; "eo_add" ] [@quiet]

let auto =
  with_no_automation_trace
    (Auto.with_dfs'
       (pick
          [
            simp ~exclude:[ "co_add"; "eo_add" ];
            gen;
            intro;
            truth;
            assumption;
            neg_intro;
            elim_disj_asm;
            conj;
            elim_conj_asm;
            elim_exists_asm;
            eq_true_elim_asm;
            false_elim;
            or_;
            with_assumptions (with_first_term apply_asm);
            with_assumptions apply;
            simp_asm;
            cond;
            discriminate;
          ]))

let%thm co_add_comm_true (c1 : corner_ori) (c2 : corner_ori) =
  co_add c1 c2 = co_add c2 c1 = true

and proof =
  begin
    noop >> intros >> eq_true_elim
    >> with_term [%term (c1 : corner_ori)] destruct_elim
       @>> with_term [%term (c2 : corner_ori)] destruct_elim
       @>> try_ (with_repeat elim_disj_asm)
       @>> simp
  end
  [@quiet]

let%thm co_add_comm (c1 : corner_ori) (c2 : corner_ori) =
  co_add c1 c2 = co_add c2 c1

and proof =
  begin
    intros >> rewrite_at "co_add_comm_true" >> truth
  end
  [@quiet]

let%thm co_add_comm_left (c1 : corner_ori) (c2 : corner_ori) (c3 : corner_ori) =
  co_add c1 (co_add c2 c3) = co_add c2 (co_add c1 c3)

and proof =
  begin
    noop >> intros
    >> with_proven [ "co_add_assoc" ] @@ with_flip_rules @@ rewrite ~position:1
    >> with_proven [ "co_add_comm" ] @@ with_flip_rules @@ rewrite ~position:3
    >> with_proven [ "co_add_assoc" ] @@ rewrite ~position:0
    >> refl
  end
  [@quiet]

let destruct_cube =
  with_term [%term (c : cube)] destruct_elim
  @>> with_term [%term (a0 : corners)] destruct_elim
  @>> with_term [%term (a1 : edges)] destruct_elim

let destruct_corners =
  with_term [%term (a0 : corner_cubie)] destruct_elim
  @>> with_term [%term (a1 : corner_cubie)] destruct_elim
  @>> with_term [%term (a2 : corner_cubie)] destruct_elim
  @>> with_term [%term (a3 : corner_cubie)] destruct_elim
  @>> with_term [%term (a4 : corner_cubie)] destruct_elim
  @>> with_term [%term (a5 : corner_cubie)] destruct_elim
  @>> with_term [%term (a6 : corner_cubie)] destruct_elim
  @>> with_term [%term (a7 : corner_cubie)] destruct_elim

let destruct_edges =
  with_term [%term (a0 : edge_cubie)] destruct_elim
  @>> with_term [%term (a1 : edge_cubie)] destruct_elim
  @>> with_term [%term (a2 : edge_cubie)] destruct_elim
  @>> with_term [%term (a3 : edge_cubie)] destruct_elim
  @>> with_term [%term (a4 : edge_cubie)] destruct_elim
  @>> with_term [%term (a5 : edge_cubie)] destruct_elim
  @>> with_term [%term (a6 : edge_cubie)] destruct_elim
  @>> with_term [%term (a7 : edge_cubie)] destruct_elim
  @>> with_term [%term (a8 : edge_cubie)] destruct_elim
  @>> with_term [%term (a9 : edge_cubie)] destruct_elim
  @>> with_term [%term (a10 : edge_cubie)] destruct_elim
  @>> with_term [%term (a11 : edge_cubie)] destruct_elim

let%thm co_sum_inv_U (c : cube) = co_sum (move_U c) = co_sum c

and proof =
  begin
    gen
    >> destruct_cube @>> destruct_corners
    >> simp ~exclude:[ "co_add"; "eo_add" ]
    >> with_repeat @@ ac_norm "co_add"
    >> refl
  end
  [@quiet]

let%thm co_sum_inv_D (c : cube) = co_sum (move_D c) = co_sum c

and proof =
  begin
    gen
    >> destruct_cube @>> destruct_corners
    >> simp ~exclude:[ "co_add"; "eo_add" ]
    >> with_repeat @@ ac_norm "co_add"
    >> refl
  end
  [@quiet]

let%thm co_add_1122 = co_add C1 (co_add C1 (co_add C2 C2)) = C0
and proof = simp [@quiet] [@simp]

let%thm co_sum_inv_L (c : cube) = co_sum (move_L c) = co_sum c

and proof =
  begin
    gen
    >> destruct_cube @>> destruct_corners
    >> simp ~exclude:[ "co_add"; "eo_add" ]
    >> with_repeat (with_proven [ "co_add_assoc" ] rewrite)
    >> with_repeat @@ ac_norm "co_add"
    >> simp ~exclude:[ "co_add"; "eo_add" ]
  end
  [@quiet]

let%thm co_sum_inv_R (c : cube) = co_sum (move_R c) = co_sum c

and proof =
  begin
    gen
    >> destruct_cube @>> destruct_corners
    >> simp ~exclude:[ "co_add"; "eo_add" ]
    >> with_repeat (with_proven [ "co_add_assoc" ] rewrite)
    >> with_repeat @@ ac_norm "co_add"
    >> simp ~exclude:[ "co_add"; "eo_add" ]
  end
  [@quiet]

let%thm co_sum_inv_F (c : cube) = co_sum (move_F c) = co_sum c

and proof =
  begin
    gen
    >> destruct_cube @>> destruct_corners @>> destruct_edges
    >> simp ~exclude:[ "co_add"; "eo_add" ]
    >> with_repeat (with_proven [ "co_add_assoc" ] rewrite)
    >> with_repeat @@ ac_norm "co_add"
    >> simp ~exclude:[ "co_add"; "eo_add" ]
  end
  [@quiet]

let%thm co_sum_inv_B (c : cube) = co_sum (move_B c) = co_sum c

and proof =
  begin
    gen
    >> destruct_cube @>> destruct_corners @>> destruct_edges
    >> simp ~exclude:[ "co_add"; "eo_add" ]
    >> with_repeat (with_proven [ "co_add_assoc" ] rewrite)
    >> with_repeat @@ ac_norm "co_add"
    >> simp ~exclude:[ "co_add"; "eo_add" ]
  end
  [@quiet]
