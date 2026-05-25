type corner_pos = URF | UFL | ULB | UBR | DFR | DLF | DBL | DRB
type edge_pos = UR | UF | UL | UB | DR | DF | DL | DB | FR | FL | BL | BR
type corner_ori = C0 | C1 | C2
type edge_ori = E0 | E1
type corner_cubie = Corner of corner_pos * corner_ori
type edge_cubie = Edge of edge_pos * edge_ori

type corners =
  | Corners of
      corner_cubie (* slot 1: URF home *)
      * corner_cubie (* slot 2: UFL home *)
      * corner_cubie (* slot 3: ULB home *)
      * corner_cubie (* slot 4: UBR home *)
      * corner_cubie (* slot 5: DFR home *)
      * corner_cubie (* slot 6: DLF home *)
      * corner_cubie (* slot 7: DBL home *)
      * corner_cubie (* slot 8: DRB home *)

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
      * edge_cubie (* slot 12: BR home *)

type cube = Cube of corners * edges

let solved_cube : cube =
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

let co_add (a : corner_ori) (b : corner_ori) : corner_ori =
  match a with
  | C0 -> b
  | C1 -> ( match b with C0 -> C1 | C1 -> C2 | C2 -> C0)
  | C2 -> ( match b with C0 -> C2 | C1 -> C0 | C2 -> C1)

let eo_add (a : edge_ori) (b : edge_ori) : edge_ori =
  match a with E0 -> b | E1 -> ( match b with E0 -> E1 | E1 -> E0)

let move_U (c : cube) : cube =
  match c with
  | Cube (corners, edges) -> (
      match (corners : corners) with
      | Corners (c1, c2, c3, c4, c5, c6, c7, c8) -> (
          match (edges : edges) with
          | Edges (e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12) ->
              Cube
                ( Corners (c2, c3, c4, c1, c5, c6, c7, c8),
                  Edges (e2, e3, e4, e1, e5, e6, e7, e8, e9, e10, e11, e12) )))

let move_D (c : cube) : cube =
  match c with
  | Cube (corners, edges) -> (
      match (corners : corners) with
      | Corners (c1, c2, c3, c4, c5, c6, c7, c8) -> (
          match (edges : edges) with
          | Edges (e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12) ->
              Cube
                ( Corners (c1, c2, c3, c4, c6, c7, c8, c5),
                  Edges (e1, e2, e3, e4, e6, e7, e8, e5, e9, e10, e11, e12) )))

let move_R (c : cube) : cube =
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

let move_L (c : cube) : cube =
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

let move_F (c : cube) : cube =
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

let move_B (c : cube) : cube =
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

let cc_ori (corner : corner_cubie) : corner_ori =
  match corner with Corner (pos, ori) -> ori

(*sum of corner orientations*)
let co_sum (c : cube) : corner_ori =
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

let ec_ori (edge : edge_cubie) : edge_ori =
  match edge with Edge (pos, ori) -> ori

let eo_sum (c : cube) : edge_ori =
  match c with
  | Cube (corners, edges) -> (
      match (edges : edges) with
      | Edges (e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11) ->
          eo_add (ec_ori e0)
            (eo_add (ec_ori e1)
               (eo_add (ec_ori e2)
                  (eo_add (ec_ori e3)
                     (eo_add (ec_ori e4)
                        (eo_add (ec_ori e5)
                           (eo_add (ec_ori e6)
                              (eo_add (ec_ori e7)
                                 (eo_add (ec_ori e8)
                                    (eo_add (ec_ori e9)
                                       (eo_add (ec_ori e10) (ec_ori e11)))))))))))
      )

let reachable_invariant (c : cube) : bool = co_sum c = C0 && eo_sum c = E0

type inv_dir = U | D | L | R | F | B
type face = FaceU | FaceD | FaceL | FaceR | FaceF | FaceB
type turn = CW | CCW | Half
type move = Move of face * turn

let apply_cw (f : face) (c : cube) : cube =
  match f with
  | FaceU -> move_U c
  | FaceD -> move_D c
  | FaceL -> move_L c
  | FaceR -> move_R c
  | FaceF -> move_F c
  | FaceB -> move_B c

let apply_move (m : move) (c : cube) : cube =
  match m with
  | Move (f, t) -> (
      match (t : turn) with
      | CW -> apply_cw f c
      | CCW -> apply_cw f (apply_cw f (apply_cw f c))
      | Half -> apply_cw f (apply_cw f c))

let inv_move (m : move) : move =
  match m with
  | Move (f, t) -> (
      match (t : turn) with
      | CW -> Move (f, CCW)
      | CCW -> Move (f, CW)
      | Half -> Move (f, Half))

let rec apply_moves (ms : move list) (c : cube) : cube =
  match ms with [] -> c | m :: rest -> apply_moves rest (apply_move m c)

let rec inv_moves (ms : move list) : move list =
  match ms with
  | [] -> []
  | m :: rest -> List.append (inv_moves rest) [ inv_move m ]

let cube_eq : cube -> cube -> bool = ( = )

(* let try_each : (cube -> move list option) -> cube -> move list -> move list option *)
(*     match *)
(*     [] -> None *)
(*     m :: rest ->  *)
(*       match f (apply_move m c) with *)
(*       | Some ms -> Some (m :: ms) *)
(*       | None -> try_each f c rest *)
(**)
(* let rec dfs depth cube : move list option =  *)
(*     match depth with *)
(*     | 0 -> if cube_eq cube solved_cube then Some [] else None *)
(*     | n' -> *)
(*             let n = pred n' in *)
(*             if cube_eq cube solved_cube then Some [] else *)
(**)
(**)
(*             None *)
(**)
(**)
(**)
(**)
