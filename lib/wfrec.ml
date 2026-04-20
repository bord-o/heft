open Kernel

let functional_of name = name ^ "_functional"
let measure_of name = name ^ "_measure"
let cong_of name = name ^ "_cong"
let wf_measure_of name = name ^ "_measure_wf"
let existence_of name = name ^ "_wf_rec"
let fix_of name = name ^ "_fix"
let get_ok msg = function Ok x -> x | Error _ -> failwith ("wfrec: " ^ msg)
let get_some msg = function Some x -> x | None -> failwith ("wfrec: " ^ msg)
let app a b = Rewrite.smart_make_app a b |> get_ok "smart_make_app"

let prove_wf_measure ~name =
  let measure_const =
    make_const (measure_of name) [] |> get_ok "make_const measure"
  in
  let wf_const = make_const "wf" [] |> get_ok "make_const wf" in
  let goal_term = app wf_const measure_const in
  let goal = Tactic.make_goal goal_term in
  let tactic =
    let open Tactic in
    rewrite_at (measure_of name) >> apply_at "wf_measure"
  in
  Tactic.run_proof ~name:(wf_measure_of name) ~quiet:true goal tactic

let prove_wf_rec_existence ~name ~arg_type ~ret_type =
  let functional_const =
    make_const (functional_of name) [] |> get_ok "make_const functional"
  in
  let measure_const =
    make_const (measure_of name) [] |> get_ok "make_const measure"
  in
  let f_ty = make_fun_ty arg_type ret_type in
  let f_var = make_var "f" f_ty in
  let x_var = make_var "x" arg_type in
  let fx = app f_var x_var in
  let hfx = app (app functional_const f_var) x_var in
  let eq = safe_make_eq fx hfx |> get_ok "safe_make_eq" in
  let forall_body = Derived.make_forall x_var eq in
  let exists_body = Derived.make_exists f_var forall_body in
  let goal = Tactic.make_goal exists_body in
  let tactic =
    let open Tactic in
    noop
    >> with_specialized ~name:"wf_rec"
         ~specs:[ measure_const; functional_const ]
         apply
    >> with_proven [ wf_measure_of name ] exact
    >> with_proven [ cong_of name ] exact
  in
  Tactic.run_proof ~name:(existence_of name) ~quiet:true goal tactic

let introduce_fixpoint ~name =
  let existence_thm =
    Rules.get_proven (existence_of name)
    |> get_some (existence_of name ^ " not found")
  in
  let _ =
    Inductive.new_specification (fix_of name) existence_thm
    |> get_ok "new_specification"
  in
  ()

let define_wfrec ~name ~arg_type ~ret_type =
  prove_wf_rec_existence ~name ~arg_type ~ret_type;
  introduce_fixpoint ~name
