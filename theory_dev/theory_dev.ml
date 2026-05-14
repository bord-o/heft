[@@@warning "-26-27-32-33"]

open Heft
open Kernel
open Tactic
open Auto
open Effect
open Effect.Deep
open Multicont
open Multicont.Deep

(* Note, tell me when a theorem doesn't exist when I expect it to (apply_at) *)
module T = Domainslib.Task

let pool = T.setup_pool ~name:"test" ~num_domains:4

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

let () =
  print_newline ();
  print_newline ()

[%%inductive type test = A | B | C]

let then_each (tacs : tactic list) : tactic_combinator =
  let tacs = ref tacs in
  let subgoals = ref [] in
  fun tac goal ->
    match tac goal with
    | effect Subgoal g, k -> (
        match !tacs with
        | [] ->
            trace_proof "more subgoals than provided tactics";
            fail ()
        | next :: rest ->
            tacs := rest;
            subgoals := g :: !subgoals;
            continue k @@ next g)
    | v ->
        print_endline "encountered subgoals: ";
        !subgoals
        |> List.iter (fun (asms, g) ->
            asms
            |> List.iter (fun (_, a) ->
                print_endline @@ Printing.pretty_print_hol_term a);
            print_endline @@ Printing.pretty_print_hol_term g;
            print_newline ());
        v

let ( >>= ) = Fun.flip then_each

let assume_tac : tactic =
 fun (_asms, conc) ->
  register "assume_tac" (Unsafe 2);
  let thm = assume conc in
  return_thm ~from:"assume_tac" thm

let collect_subgoals (tacs : tactic list) : tactic_combinator =
  let tacs = ref tacs in
  let (subgoals : (goal * tactic * (thm -> thm)) list ref) = ref [] in
  fun tac goal ->
    match tac goal with
    | effect Subgoal g, k -> (
        let r = promote k in
        match !tacs with
        | [] ->
            trace_proof "more subgoals than provided tactics";
            fail ()
        | next :: rest ->
            tacs := rest;
            subgoals := (g, next, fun (t : thm) -> resume r t) :: !subgoals;
            resume r @@ Derived.truth)
    | v -> (
        (* at this point v is bunk from our preprocessing *)
        Printf.printf "encountered count: %d\n" (List.length !subgoals);
        !subgoals
        |> List.iter (fun ((_, g), _, _) ->
            print_endline @@ Printing.pretty_print_hol_term g);
        match !subgoals with
        | [] -> fail ()
        | [
         (bottom_goal, bottom_tac, br);
         (mid_goal, mid_tac, mr);
         (top_goal, top_tac, tr);
        ] ->
            print_endline "final before ";
            let final_thm =
              match bottom_tac bottom_goal with
              | effect Subgoal _, _ ->
                  print_endline "finanl tactic should produce theorem";
                  fail ()
              | thm -> thm
            in
            print_endline @@ Printing.pretty_print_thm final_thm;
            print_endline "final after";
            (* Ok so at this point we have the thm for the last goal without computing anything up to this point, now we can go backwards
                   running the tactics for real, and when they ask for a subgoal, we already have the subthm that they need so we can resume with that
                   and get our next level theorem. rinse and repeat until the list is empty, the last thm will be what we return
                 *)
            print_endline "middle before";
            let snd_level =
              match mid_tac mid_goal with
              | effect Subgoal mg, k -> resume (promote k) final_thm
              | v -> v
            in
            print_endline @@ Printing.pretty_print_thm snd_level;
            print_endline "middle after";

            print_endline "top before";
            let top_level =
              match top_tac top_goal with
              | effect Subgoal mg, k -> resume (promote k) snd_level
              | v -> v
            in
            print_endline @@ Printing.pretty_print_thm top_level;
            print_endline "top after";
            top_level
            (* This is all working now, its just the last step that I don't know how to do, with multiple resumptions I should be able to resume the first
                   one (tr), but it gives continuation already resumed error, even though I'm promoting it
                 *)
        | _ -> fail ())

let ( >>>= ) = Fun.flip collect_subgoals

let%thm par_test1 (t : test) = t = A || t = B || t = C

and proof =
  begin
    gen
    >> with_term [%term (t : test)] destruct
       @>> try_ @@ with_repeat elim_disj_asm
    >>>= [
           auto;
           auto;
           auto;
           (* (fun g -> Unix.sleep 1; auto g); *)
           (* (fun g -> Unix.sleep 1; auto g); *)
           (* (fun g -> Unix.sleep 1; auto g); *)
         ]
  end
(* [@quiet] *)

(* let () = print_endline @@ Printing.pretty_print_thm (Rules.find_thm "par_test1" [] |> Option.get ) *)
