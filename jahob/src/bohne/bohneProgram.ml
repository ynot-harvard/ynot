open Util
open Ast
open AstUtil
open Form
open FormUtil
open TypeReconstruct
open TermRewrite
open Slice
open PrintForm
open BohneUtil
open Pred

(** Commands in a Bohne program *)
type guarded_command = {
    mutable gc_guard : form;
    mutable gc_command : basic_command list
  }

(** Control flow nodes of a Bohne program *)
type location = {
    loc_pp : program_point;
    mutable loc_cmds : (guarded_command * program_point) list;
    mutable loc_preds : pred_decl list;
    mutable loc_invariants : form list;
    mutable loc_assertions : (guarded_command * form) list
  }

(** Bohne programs *)
type bohne_program = {
    locations : (int, location) Hashtbl.t;
    entry_point : program_point;
    exit_point : program_point;
    wp : basic_command list -> form -> form;
    idents : ident list;
    assumed_invariants : form list;
    mutable initial_states : form
  }

let gc_skip () = {gc_guard = mk_true; gc_command = []}

let initial_location program =
  Hashtbl.find program.locations program.entry_point.pp_id

let is_initial_pp program pp =
  program.entry_point.pp_id = pp.pp_id 

let is_exit_pp program pp =
  program.exit_point.pp_id = pp.pp_id 

let get_location program pp =
  Hashtbl.find program.locations pp.pp_id

let compose program gc1 gc2 =
  {gc_guard = smk_and [gc1.gc_guard; program.wp gc1.gc_command gc2.gc_guard];
   gc_command = gc2.gc_command @ gc1.gc_command}

let print_command chan pp (gc, pp') =
  let out s = output_string chan s in
  let assume_guards = 
    List.map (fun f -> Assume {annot_form = f; annot_msg = ""}) (split_conjuncts gc.gc_guard) in
  out (Printf.sprintf "Location %d -> Location %d\n" pp.pp_id pp'.pp_id);
  List.iter (fun c -> out (PrintAst.pr_basic_command c)) (assume_guards @ List.rev (gc.gc_command));
  out "\n"
  
let object_vars_from_gc gc =
  List.fold_left 
    (fun acc c -> match c with
    | VarAssign ac -> 
	let object_vars = free_object_vars ac.assign_rhs in
	Util.union acc object_vars
    | _ -> acc) [] gc.gc_command


let print_program chan program =
  let out s = output_string chan s in
  let print_predicates pp_id l =
    out (Printf.sprintf "Location %d\n" pp_id);
    List.iter (print_pred_decl chan) l.loc_preds;
    out "\n"
  in  
  let print_transitions _ l =
    List.iter (print_command chan l.loc_pp) l.loc_cmds
  in
  let out_line () = out (String.make 80 '*' ^ "\n") in
  out "\n";
  out_line ();
  out "Bohne program\n";
  out_line ();
  out "\n";
  out (Printf.sprintf "Initial location: %d\n\n" program.entry_point.pp_id);
  out "Transitions:\n\n";
  Hashtbl.iter print_transitions program.locations;
  out_line ();
  out "\n";
  out "Predicates:\n\n";
  Hashtbl.iter print_predicates program.locations;
  out_line ();
  out "\n"

(** Reachability relation between control flow nodes *)
let reaches program pp1 pp2 =
  let rec reaches pp1 pp2 seen =
    pp1.pp_id = pp2.pp_id ||
    try 
      let loc1 = get_location program pp1 in 
      List.exists (fun (_, pp) -> 
	not (List.mem pp.pp_id seen) &&
	reaches pp pp2 (pp.pp_id::seen)) loc1.loc_cmds
    with Not_found -> false
  in reaches pp1 pp2 [pp1.pp_id]

(** Total order on control flow nodes *)
let compare_pps program pp1 pp2 =
  if pp1.pp_id = pp2.pp_id then 0 else
  let r_21 = reaches program pp2 pp1 
  and r_12 = reaches program pp1 pp2 in
  if r_21 && not r_12 then 1
  else if r_12 && not r_21 then -1
  else compare pp1.pp_id pp2.pp_id

(** Propagate assert and assume statements 
 and remove commands with unsatisfiable guards *)
let propagate_asserts_assumes program =
  let mk_assert f = Assert {annot_msg = ""; annot_form = f} in
  let update_assert c (gc, f) =
      let _ = match c with
      |	Assume af ->
	  gc.gc_guard <- smk_and [af.annot_form; gc.gc_guard]
      |	Assert _ | Split _ -> ()
      |	_ -> 
	  gc.gc_guard <- negation_normal_form (mk_not (program.wp [c] (mk_not gc.gc_guard)));
	  gc.gc_command <- c::gc.gc_command
      in (gc, f)
  in
  let type_annot = Str.regexp ".*type$" in
  let assumed_invariants = smk_and program.assumed_invariants in
  let propagate pp cmds =
    let remove_asserted_postconds succ_pp =
      if not (is_exit_pp program succ_pp) then fun cmds -> cmds else
      let succ_loc = get_location program succ_pp in
      let postconds = List.concat (List.map (fun a -> split_conjuncts (snd a)) succ_loc.loc_assertions) in
      let rec remove acc = function
	| Assert af::cmds' ->
	    let asserts = split_conjuncts af.annot_form in
	    (match List.filter (fun a -> not (List.exists (equal a) postconds)) asserts with
	    | [] -> remove acc cmds'
	    | rest -> 
		af.annot_form <- smk_and rest;
		remove (Assert af::acc) cmds')
	| cmds -> List.rev_append acc cmds
      in remove []
    in
    let check_c succ_pp (cmd', asserts, assumes) c =
      match c with
      |	Assume af ->
	   (* Remove assumptions which are just type annotations. 
	    * This makes the analysis significantly faster; should be done in a less dirty way. *)
	   if Str.string_match type_annot af.annot_msg 0 then 
	     (cmd', asserts, assumes)
	   else 
	  (cmd', List.rev_map (update_assert c) asserts, 
	   af.annot_form::assumes) 
      |	Assert af ->
	  let assrt = (gc_skip (), af.annot_form) in
	  (cmd', assrt::asserts, assumes)
      | NoteThat af ->
	  let assrt = (gc_skip (), af.annot_form) in
	  (cmd', assrt::List.rev_map (update_assert c) asserts,
	   af.annot_form::assumes)
      |	Split _ -> 
	  (cmd', asserts, assumes)
      |	_ -> (c::cmd', List.rev_map (update_assert c) asserts, 
	      List.rev_map (fun f -> negation_normal_form (mk_not (program.wp [c] (mk_not f)))) assumes)
    in
    let propagate_gc (assertions, cmds') (cmd, target) =
      let cs, asserts, assumes = 
	List.fold_left (check_c target) ([], [], []) 
	  (remove_asserted_postconds target (mk_assert (smk_and program.assumed_invariants)::cmd.gc_command))
      in 
      let f = mk_impl (smk_and (assumed_invariants::assumes), mk_false) in
      if BfCachedDecider.decide trivial_context f
      then (assertions, cmds') else begin
	cmd.gc_command <- List.rev cs;
	(* if is_initial_pp program pp then
	  cmd.gc_guard <- smk_and (program.initial_states::assumes)
	else *) cmd.gc_guard <- smk_and assumes;
	(List.rev_append asserts assertions, (cmd, target)::cmds')
      end
    in
    List.fold_left propagate_gc ([], []) cmds
  in
  let propagate_initial_assumes () =
    let init_loc = initial_location program in
    let guards = List.rev_map (fun (gc, _) -> gc.gc_guard) init_loc.loc_cmds in
    let init = match guards with
    | g::guards' -> 
	let common_guards = List.fold_left (fun acc f ->
	  let fs = split_conjuncts f in
	  Util.intersect acc fs) (split_conjuncts g) guards'
	in common_guards
    | _ -> []
    in
    program.initial_states <- smk_and (program.initial_states::init)
  in
  let process_location _ loc =
    let assertions, cmds' = propagate loc.loc_pp loc.loc_cmds in
    List.iter (fun (gc, f) -> gc.gc_command <- List.rev gc.gc_command) assertions;
    loc.loc_assertions <- assertions @ loc.loc_assertions;
    loc.loc_cmds <- cmds'
  in 
  Hashtbl.iter process_location program.locations;
  propagate_initial_assumes ()

(** Derive an initial set of predicates using various heuristics *)
let derive_initial_predicates program =
  let prog_vars f0 =
    let f1 = normalize_form true f0 in
    let f, env = TypeReconstruct.reconstruct_types (get_annotated_types f1) f1 in
    let seq = sequent_of_form f in 
    (* let seq = slice [slice_obj_vars; slice_obj_sets] env seq0 in *)
    let vars = List.fold_left 
	(fun vars x -> 
	  try let ty = List.assoc x env in
	  if ty = mk_object_type || ty = mk_bool_type 
	  then (x, ty)::vars else vars
	  with Not_found -> Util.warn ("missing type for variable " ^ x); vars) 
	[] (fv f)
    in
    vars
  in
  let add_var_preds pp_id vs =
    let l = Hashtbl.find program.locations pp_id in
    List.fold_left 
      (fun has_new_preds v ->
	if List.mem (fst v) program.idents then
	  let v_pred = add_var_pred_decl v in
	  if not (List.exists (fun p -> p.pred_index = v_pred.pred_index) l.loc_preds)
	  then (l.loc_preds <- v_pred :: l.loc_preds; true)
	  else has_new_preds
	else has_new_preds)
      false vs
  in
  let get_updated assertion_map = List.fold_left
      (fun updated (pp_id, assns) ->
	let vs = List.fold_left 
	    (fun vs f -> union vs (prog_vars f)) 
	    [] assns
	in
	let has_new_preds = add_var_preds pp_id vs in
	if has_new_preds then pp_id::updated else updated)
      [] assertion_map
  in
  let next_assertion_map assertion_map updated =
    let new_assns l = List.fold_left 
	(fun new_assns (c, pp') ->
	  if List.mem pp'.pp_id updated then
	    let assns' = List.map 
		(fun f -> 
		  normalize_form true (smk_impl (c.gc_guard, program.wp c.gc_command f)))
		(List.assoc pp'.pp_id assertion_map)
	    in List.rev_append assns' new_assns
	  else new_assns) 
	[] l.loc_cmds
    in
    Hashtbl.fold (fun pp_id l assertion_map' ->
      match new_assns l with
      |	[] -> assertion_map'
      |	assns -> (pp_id, assns)::assertion_map')
      program.locations []
  in
  let rec derive_var_preds assertion_map =
    match assertion_map with
    | [] -> ()
    | _ -> 
	let updated = get_updated assertion_map in
	let assertion_map' = next_assertion_map assertion_map updated in
	derive_var_preds assertion_map'
  in 
  let initial_assertion_map = 
    Hashtbl.fold
      (fun pp_id l assertion_map -> 
	if not (empty l.loc_assertions) then
	  let expanded_assns = List.rev_map
	      (fun f0 -> 
		let f = normalize_form true f0 in
		fst (rewrite true [rewrite_tree] [] f)) 
	      (List.map (fun (gc, f) ->
		smk_impl (gc.gc_guard, program.wp gc.gc_command f))
		 l.loc_assertions) 
	  in
	  (pp_id, expanded_assns)::assertion_map
	else assertion_map) 
      program.locations []
  in
  let derive_iterators () =
    let check_iterator pp_id cmds acc p_decl =
      try 
	let p, ty = 
	  find_map 
	    (function IsSingleton opt -> opt | _ -> None) 
	    p_decl.pred_props
	in
	let x1 = fresh_var "x" in
	let x2 = fresh_var "x" in
	let updates = List.fold_left (fun updates (gc, pp') ->
	  if pp_id <> pp'.pp_id then updates
	  else match normalize 2 (program.wp gc.gc_command (mk_var p)) with
	  | App (Const Impl, [_; App (Const FieldRead, [f; Var p'])])
	  | App (Const FieldRead, [f; Var p']) when p = p' -> 
	      let f = mk_eq (App (f, [mk_var x1]), mk_var x2) in
	      f :: updates
	  | _ -> updates) [] cmds
	in if empty updates then acc 
	else 
	  let iter_form =
	      App (mk_var str_rtrancl, 
		   [Binder (Lambda, [(x1, ty); (x2, ty)], mk_or updates);			   
		    mk_var p; mk_var x1])
	  in
	  let iter_def = Binder (Comprehension, [(x1, ty)], iter_form) in
	  let iter_decl = add_pred iter_def []
	  in iter_decl::acc
      with _ -> acc
    in
    Hashtbl.iter
      (fun pp_id l ->
	let var_preds = List.filter is_singleton l.loc_preds in
	let iter_preds = List.fold_left 
	    (check_iterator pp_id l.loc_cmds) [] var_preds
	in l.loc_preds <- union_preds iter_preds l.loc_preds)
      program.locations
  in
  derive_var_preds initial_assertion_map;
  derive_iterators ()

