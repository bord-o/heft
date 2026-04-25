open Heft

(* open Result.Syntax *)
open Kernel
open Tactic
open Grimm
open Auto

let _ = with_best_first
let _ = with_grimm

(* let () = *)
(*   let%thm goal (a : bool) (b : bool) (c : bool) = a ==> (b ==> (c ==> a)) in *)
(*   let root_tac = pick [ gen; intro; assumption ] in *)
(*   let f = frontier_of_goal root_tac goal in *)
(**)
(*   let rec loop depth = *)
(*     run_proof goal (fun _goal -> search f depth); *)
(*     ignore @@ read_line (); *)
(*     loop (depth + 1) *)
(*   in *)
(*   loop 0 *)
(* let () = *)
(*   let open Kernel in *)
(*   let open Derived in *)
(*   let p = make_var "P" bool_ty in *)
(*   let q = make_var "Q" bool_ty in *)
(*   let r = make_var "R" bool_ty in *)
(*   let goal = *)
(*     ( [], *)
(*       make_imp *)
(*         (make_disj p (make_conj q r)) *)
(*         (make_conj (make_disj p q) (make_disj p r)) ) *)
(*   in *)
(*   let rec loop depth = *)
(*     run_proof goal (with_grimm ~depth ctauto); *)
(*     ignore @@ read_line (); *)
(*     loop (depth + 1) *)
(*   in *)
(*   loop 0 *)

(* let () = *)
(*   let%thm goal (a : bool) (b : bool) (c : bool) (d : bool) = *)
(*     ((a || b) && (c || d)) ==> ((a && c) || (a && d) || (b && c) || (b && d)) *)
(*   in *)
(**)
(*   run_proof goal (with_grimm ctauto) *)

(* let () = *)
(*   let goal = *)
(*     make_goal *)
(*       [%term *)
(*         exists *)
(*           (fun (nil_case : nat) (cons_case : 'a -> 'a list -> nat -> nat) -> *)
(*             (g : 'a list -> nat) [] *)
(*             = nil_case *)
(*             ==> (forall (fun (x : 'a) (xs : 'a list) -> *)
(*                      (g : 'a list -> nat) (x :: xs) *)
(*                      = cons_case x xs ((g : 'a list -> nat) xs)) *)
(*                 ==> ((g : 'a list -> nat) [ (x : 'a) ] = 1n *)
(*                     && (g : 'a list -> nat) [ (x : 'a); (y : 'a) ] = 2n)))] *)
(*   in *)
(**)
(*   let proof = *)
(*     (* with_best_first *) *)
(*     let auto g = *)
(*       register ~prob:0.5 "auto" (Unsafe 1); *)
(*       auto g *)
(*     in *)
(*     with_info_trace (pick [ with_synthetic_term 5 exists; auto ]) *)
(*   in *)
(*   let rec loop depth = *)
(*     run_proof goal (with_grimm proof); *)
(*     ignore @@ read_line (); *)
(*     loop (depth + 1) *)
(*   in *)
(*   loop 0 *)
open Nats
open Lists
open Synth

let n i = nat_of_int i
let list_nat = TyCon ("list", [ nat_ty ])
let nil_nat = Result.get_ok (type_inst [ (make_vartype "a", nat_ty) ] nil)
let cons_nat = Result.get_ok (type_inst [ (make_vartype "a", nat_ty) ] cons)

let mk_list elems =
  List.fold_right
    (fun x acc ->
      Result.get_ok (make_app (Result.get_ok (make_app cons_nat x)) acc))
    elems nil_nat

(* let plus_ty = make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty) *)
(* let plus_extra = [ ("plus", plus_ty) ] *)
(* let append_ty = make_fun_ty list_nat (make_fun_ty list_nat list_nat) *)
(* let append_extra = [ ("append", append_ty) ] *)

(* let pre_synth_two goal depth extra = *)
(*   let ty = Derived.type_of_existential goal |> Result.get_ok in *)
(*   let first_terms = Synth.enumerate ~extra [] ty depth in *)
(*   let _, bod = Derived.destruct_exists (snd goal) |> Result.get_ok in *)
(*   let sndty = Derived.type_of_existential ([], bod) |> Result.get_ok in *)
(*   let snd_terms = Synth.enumerate ~extra [] sndty depth in *)
(*   ((ty, first_terms), (sndty, snd_terms)) *)

(* TODO: make a special exists tactic which matches on the existential type
   and provides the proper precomputed terms
 *)
module D = Derived
open Printing

let () =
  let func_type = make_fun_ty list_nat (make_fun_ty list_nat list_nat) in
  let test_cases =
    [ ([ mk_list [ n 1 ]; mk_list [ n 2 ] ], mk_list [ n 1; n 2 ]) ]
  in
  let goal_tm = make_synthesis_goal ~func_type ~test_cases in
  let _goal = ([], goal_tm) in

  let goal =
    make_goal
      [%term
        exists
          (fun
            (nil_case : 'a list -> 'a list)
            (cons_case : 'a -> 'a list -> 'a list -> 'a list)
          ->
            forall (fun (ys : 'a list) ->
                (g : 'a list -> 'a list -> 'a list) [] ys = nil_case ys)
            ==> (forall (fun (x : 'a) (xs : 'a list) (ys : 'a list) ->
                     (g : 'a list -> 'a list -> 'a list) (x :: xs) ys
                     = cons_case x xs
                         ((g : 'a list -> 'a list -> 'a list) xs ys))
                ==> ((g : 'a list -> 'a list -> 'a list) [] [ (x : 'a) ]
                     = [ (x : 'a) ]
                    && (g : 'a list -> 'a list -> 'a list)
                         [ (x : 'a) ]
                         [ (y : 'a) ]
                       = [ (x : 'a); (y : 'a) ])))]
  in

  (* let terms = Synth. *)
  let proof =
    let with_synthetic_term ?(extra = []) (depth : int) : tactic_combinator =
      let terms = Hashtbl.create 16 in
      fun tac goal ->
        match tac goal with
        | effect Choose (Term _), k ->
            let r = Multicont.Deep.promote k in
            let ty = D.type_of_existential goal |> Result.get_ok in
            let terms =
              match Hashtbl.find_opt terms (ty, depth) with
              | Some ts ->
                  trace_info "cache hit";
                  ts
              | None ->
                  trace_info "cache miss";
                  let new_terms = Synth.enumerate ~extra [] ty depth in
                  let new_terms =
                    new_terms
                    |> List.sort (fun a b ->
                        compare (D.term_size a) (D.term_size b))
                  in
                  Hashtbl.add terms (ty, depth) new_terms;
                  new_terms
            in

            trace_info
              (Printf.sprintf "enumerated %d unique terms" (List.length terms));

            List.iter
              (fun t ->
                trace_dbg (Printf.sprintf "term: %s" (pretty_print_hol_term t)))
              terms;
            let t = choose_terms terms in
            trace_info
              (Printf.sprintf "chose synth: %s" (pretty_print_hol_term t));
            Multicont.Deep.resume r t
        | v -> v
    in
    (* with_best_first *)
    let auto g =
      register ~prob:1. "auto" (Safe 1);
      if Derived.is_exists (snd g) then fail () else auto g
    in

    pick [ with_synthetic_term 5 @@ exists; auto ]
  in
  let rec loop depth =
    (* run_proof goal (with_info_trace (with_grimm ~depth proof)); *)
    run_proof goal (with_info_trace (with_grimm proof));
    ignore @@ read_line ();
    loop (depth + 1)
  in
  loop 0
