open Heft
open Tactic
open Rubiks
open Auto

[@@@warning "-26-27-32-33"]

let acount = Atomic.make 0
let total = 6561.
let start = Unix.gettimeofday ()

let rss_mb () =
  let pid = Unix.getpid () in
  let cmd = Printf.sprintf "ps -o rss= -p %d" pid in
  let ic = Unix.open_process_in cmd in
  let line = input_line ic in
  let _ = Unix.close_process_in ic in
  int_of_string (String.trim line) / 1024

let%thm co_sum_inv (c : cube) = co_sum (move_U c) = co_sum c

and proof =
  begin
    gen
    >> (with_term [%term (c : cube)] destruct_elim
       @>> with_term [%term (a0 : corners)] destruct_elim
       @>> with_term [%term (a1 : edges)] destruct_elim
       @>> with_term [%term (a0 : corner_cubie)] destruct_elim
       @>> with_term [%term (a1 : corner_cubie)] destruct_elim
       @>> with_term [%term (a2 : corner_cubie)] destruct_elim
       @>> with_term [%term (a3 : corner_cubie)] destruct_elim
       @>> with_term [%term (a4 : corner_cubie)] destruct_elim
       @>> with_term [%term (a5 : corner_cubie)] destruct_elim
       @>> with_term [%term (a6 : corner_cubie)] destruct_elim
       @>> with_term [%term (a7 : corner_cubie)] destruct_elim
       @>> with_term [%term (a1 : corner_ori)] destruct_elim
       @>> with_term [%term (a1' : corner_ori)] destruct_elim
       @>> with_term [%term (a1'' : corner_ori)] destruct_elim
       @>> with_term [%term (a1''' : corner_ori)] destruct_elim
       @>> with_term [%term (a1'''' : corner_ori)] destruct_elim
       @>> with_term [%term (a1''''' : corner_ori)] destruct_elim
       @>> with_term [%term (a1'''''' : corner_ori)] destruct_elim
       @>> with_term [%term (a1''''''' : corner_ori)] destruct_elim
       @>> try_ @@ with_repeat elim_disj_asm
       (* @>> sorry *)
       @>>! fun g ->
       let count = Atomic.get acount in
       if count > 1000 then (
         Printf.printf "Final system reserved: %d\n" (rss_mb ());
         fail ())
       else
         let thm =
           (with_named_rule
              [
                "move_U";
                "match_cube";
                "match_corners";
                "match_edges";
                "co_sum";
                "cc_ori";
                "match_corner_cubie";
                "co_add_C0_l";
                "co_add_C0_r";
                "co_add_comm_true";
              ]
              (try_ simp_only)
           >> sorry)
             g
         in
         (* let thm = sorry g in *)
         Atomic.incr acount;
         let total_elapsed = Unix.gettimeofday () -. start in
         Printf.printf "%f\n" total_elapsed;
         let rate = total_elapsed *. 1000. /. float_of_int count in
         Printf.printf "Finished %f%% of subgoals with rate %f ms/goal\n"
           (100. *. float_of_int count /. total)
           rate;

         (* let remaining = total -. float_of_int count in *)
         (* let estimate = rate *. remaining /. 1000. /. 60. in *)
         (* Printf.printf "ETA: %f minutes\n" estimate; *)
         if count mod 100 = 0 then begin
           Gc.compact ();
           let s = Gc.quick_stat () in
           let live_mb = float_of_int s.live_words *. 8.0 /. 1_048_576.0 in
           let heap_mb = float_of_int s.heap_words *. 8.0 /. 1_048_576.0 in
           let top_mb = float_of_int s.top_heap_words *. 8.0 /. 1_048_576.0 in
           let minor_mb = s.minor_words *. 8.0 /. 1_048_576.0 in
           let promoted_mb = s.promoted_words *. 8.0 /. 1_048_576.0 in
           let major_mb = s.major_words *. 8.0 /. 1_048_576.0 in
           Printf.printf
             "[gc] live=%.1fMB heap=%.1fMB top=%.1fMB | minor_alloc=%.0fMB \
              promoted=%.0fMB major_alloc=%.0fMB | minors=%d majors=%d \
              compacts=%d\n"
             live_mb heap_mb top_mb minor_mb promoted_mb major_mb
             s.minor_collections s.major_collections s.compactions;
           flush stdout
         end;

         thm)
    >> sorry
    (* @>> (fun g -> incr count; sorry g) *)
    (* @>> simp ~exclude:["co_add"; "eo_add"] *)
  end
  (* [@trace] *)
  [@quiet]
