open Util
open Form
open FormUtil
open PrintForm
open BohneUtil
open Pred
open BohneProgram
open Region
open Ast
open Bf
open Bf_set
open Abstraction
open CachedDecider
open BfCachedDecider
open BohneRefine

(** Abstract initial states *)
let abstract_init entry_location assumed_invs init =
  let preds = entry_location.loc_preds in
  let invs = smk_and assumed_invs in
  let root_region = mk_root_region entry_location.loc_pp preds (init::assumed_invs) in
  let var_preds = List.filter is_singleton preds in
  let abs_init = Bf_set.singleton (alpha preds invs init) in
  let _ = Debug.print_msg 3 (fun chan -> 
    output_string chan "\nbefore coerce:\n"; 
    print_abs_states chan abs_init)
  in
  let abs_init = coerce false preds preds trivial_context (smk_and [init; invs]) abs_init in 
  let abs_init = List.fold_left (fun acc p ->
    if is_old p then
      let new_p = pred_by_name (find_map (function IsOld p -> Some p | _ -> None) p.pred_props) in 
      Bf_set.conj acc (Bf.equi (Bf.mk_var p.pred_index) (Bf.mk_var new_p.pred_index))
    else acc) abs_init preds in
  let _ = Debug.print_msg 3 (fun chan -> 
    output_string chan "before splitting:\n"; 
    print_abs_states chan abs_init;
    output_string chan "after splitting:") 
  in
  let split_abs_init0 = split_singletons preds var_preds abs_init 
  in
  let split_abs_init = coerce false preds preds trivial_context (mk_and [init; invs]) split_abs_init0 in
  let _ = Debug.print_msg 1 (fun chan -> 
    Debug.newline ();
    print_abs_states chan split_abs_init) 
  in 
  let _ = root_region.absstates <- split_abs_init in
  root_region


(** Abstract post operator *)
let abstract_post =
  (* cache for abstract weakest preconditions *)
  let pred_upd_map : Bf.t FormHashtbl.t = FormHashtbl.create 0 in
  fun lfp region' wp ->
    let gc, new_abs_states, parent = region'.parent in
    if Bf_set.le new_abs_states Bf_set.bottom then Bf_set.bottom else
    let region = !parent in
    let _ = Debug.print_msg 2 (fun chan ->
      output_string chan "\nComputing abstract post for command:\n";
      print_command chan region.ppoint (gc, region'.ppoint))
    in
    let preds' = region'.preds in 
    let preds = region.preds in
    let wp f = normalize_form false (wp gc.gc_command f) in
    let guard = gc.gc_guard in
    let guarded_abs_states = find_in_lfp lfp region.ppoint.pp_id guard in
    let invariants = smk_and region.invariants in
    let inv_guard = smk_and [invariants; guard] in
    let _ = Debug.print_msg 3 (fun chan -> 
      output_string chan ("Invariants:\n" ^ string_of_form invariants ^ "\n"))
    in 
    (* checks whether there exists a predicate that corresponds to wp of predicate p *) 
    let get_wp_pred p wp_p =
      if is_singleton p then 
	let def_wp_p = Binder (Comprehension, typed_free_var_list 1, wp_p) in
	add_pred def_wp_p [IsSingleton None]
      else List.find (fun p' -> FormUtil.equal (pred_to_form true p') wp_p) preds
    in
    let get_context_preds f0 =
      let f = form_of_sequent (elim_fv_in_seq false (sequent_of_form f0)) in
      let object_vars = free_object_vars f in
      List.filter (fun p -> 
	try 
	  let v = Util.find_map (function IsSingleton x -> x | _ -> None) p.pred_props in
	  List.mem (fst v) object_vars
	with Not_found -> true) preds
    in
    let _ = Debug.print_msg 3 (fun chan ->
      output_string chan "Context:\n"; 
      print_abs_state chan (Bf_set.join guarded_abs_states))
    in
    let mk_context context_preds =
      if !CmdLine.useinstantiation then
	if not !CmdLine.usecontext then
	  (Bf.top, fun _ -> mk_true)
	else 
	  (Bf_set.join guarded_abs_states, stack_context context_preds)
      else 
	(Bf_set.join new_abs_states, gamma_state false preds)
    in
    (* computes predicate update for given predicate *)
    let compute_pred_update p i' preds =
      let def_p = pred_to_form true p in
      let wp_p0 = wp def_p in
      let wp_p = mk_impl (inv_guard, wp_p0) in
      let wp_notp = mk_impl (inv_guard, wp (smk_not def_p)) in
      let context = mk_context (get_context_preds wp_p0) in
      let f_context = (snd context) (fst context) in
      let key = normalize_form false (smk_impl (f_context, wp_p)) in
      let _ = Debug.print_msg 2 (fun chan -> 
	Printf.fprintf chan "Process predicate %s\nwp(%s) = %s\n\n" 
	  p.pred_name p.pred_name (PrintForm.string_of_form (wp def_p))) in
      try FormHashtbl.find pred_upd_map key
      with Not_found ->
	let abs_wp_p, abs_wp_notp = 
	  if is_state_pred p then
	    if BfCachedDecider.decide context wp_p then
	      Bf.top, Bf.bottom
	    else if BfCachedDecider.decide context wp_notp then
	      Bf.bottom, Bf.top
	    else Bf.bottom, Bf.bottom
	  else uabstract_form preds context wp_p wp_notp false in 
	let _ = Debug.print_msg 3 (fun chan -> 
	  Printf.fprintf chan "wp^#(%s) = \n" (p.pred_name); 
	  print_cubes chan abs_wp_p;
	  Printf.fprintf chan "wp^#(~%s) = \n" (p.pred_name); 
	  print_cubes chan abs_wp_notp;
	  Debug.newline ())
	in
	let pred_upd = 
	  Bf.conj (Bf.impl (abs_wp_p) i')
	    (Bf.impl (abs_wp_notp) (Bf.neg i'))
	in 
	FormHashtbl.add pred_upd_map key pred_upd; 
	pred_upd
    in
    (* compute abstract transition relation for context and given command *)
    let split_preds, ext_preds, split_rel, upd_preds, abs_trans_rel0 =
      let process_pred (split_preds, ext_preds, split_rel, upd_preds, trans_rel) p =
	let def_p = pred_to_form true p in
	let wp_p = normalize_form false (wp def_p) in
	let i' = Bf.mk_primed_var p.pred_index in
	let split_preds', ext_preds', split_update, upd_preds', pred_update = 
	  try 
	    let p' = if has_prop IsConst p then p else get_wp_pred p wp_p in 
	    let split_preds', ext_preds', split_update = 
	      if p.pred_index = p'.pred_index || 
	      not (is_singleton p') ||
	      List.exists (fun p -> p.pred_index = p'.pred_index) (preds @ split_preds)
	      then (split_preds, ext_preds, Bf.top)
	      else (p'::split_preds, union_preds [p'] ext_preds, 
		    compute_pred_update p (Bf.mk_var p'.pred_index) preds)
	    in 
	    (split_preds', ext_preds', split_update, upd_preds, Bf.equi (Bf.mk_var p'.pred_index) i')
	  with Not_found ->
     	    if not (List.mem p region'.best_preds) &&  (List.mem p preds || is_state_pred p) 
	    then (split_preds, ext_preds, Bf.top, p::upd_preds, Bf.top)
	    else
	      let def_wp_p = 
		if is_state_pred p then wp_p
		else Binder (Comprehension, typed_free_var_list 1, wp_p) in
	      let p' = add_pred def_wp_p p.pred_props in
	      (split_preds, union_preds [p'] ext_preds, 
	       compute_pred_update p (Bf.mk_var p'.pred_index) preds, upd_preds, 
	       Bf.equi (Bf.mk_var p'.pred_index) i')
	in
	(split_preds', ext_preds', Bf.conj split_rel split_update, 
	 upd_preds', Bf.conj trans_rel pred_update)
      in
      List.fold_left process_pred ([], [], Bf.top, [], Bf.top) preds' 
    in
    let total_preds = union_preds ext_preds preds in
    let abs_trans_rel = 
      let preds = union_preds preds split_preds in
      let abs_trans_rel1 = List.fold_left (fun abs_trans_rel p ->
	let i' = Bf.mk_primed_var p.pred_index in
	Bf.conj abs_trans_rel (compute_pred_update p i' preds))
	  Bf.top upd_preds
      in Bf.conj abs_trans_rel0 abs_trans_rel1
    in
    (* split abstract states *)
    let abs_states = 
      let context = mk_context preds in
      let refined_abs_states = Bf_set.conj new_abs_states split_rel in
      let split_abs_states = 
	split_singletons total_preds split_preds refined_abs_states 
      in
      coerce region'.use_best_post ext_preds total_preds context 
	inv_guard split_abs_states
    in
    let _ = Debug.print_msg 3 (fun chan ->
      output_string chan "Final input states:\n"; 
      print_abs_states chan abs_states)
    in
    (* compute abstract post of split states *)
    let abs_post =
      let _ = Debug.print_msg 3 (fun chan ->
	output_string chan "Split predicates: ";
	List.iter (fun p -> output_string chan (p.pred_name ^ " ")) split_preds;
	Debug.newline ())
      in
      Bf_set.map 
	(fun abs_state ->
	  Debug.print_msg 2 
	    (fun chan -> 
	      output_string chan "Input state:\n"; 
	      print_cubes chan (Bf.conj abs_state abs_trans_rel));
	  let post = Bf.rel_prod abs_state abs_trans_rel in
	  Debug.print_msg 2
	    (fun chan ->
	      output_string chan "Output state:\n"; 
	      print_abs_state chan post);
	  post) abs_states
    in abs_post
  
(** Compute least fixed point *)
let fix program root_region =
  let module Pq = 
    PriorityQueue(struct 
      type el = region 
      type context = bohne_program
      let equal = region_equal	
      let compare prog r1 r2 =
	let _, _, r1_parent = r1.parent in
	let _, _, r2_parent = r2.parent in
	let res = compare_pps prog !r1_parent.ppoint !r2_parent.ppoint in
	if res = 0 then compare_pps prog r1.ppoint r2.ppoint 
	else res
    end) in
  let lfp = Hashtbl.create (Hashtbl.length program.locations) in
  let insert = Pq.insert program in
  let extract = Pq.extract program in
  let remove = Pq.remove program in
  let assumed_invs = program.assumed_invariants in
  let insert_succs region unprocessed =
    let invariants = smk_and region.invariants in
    let loc = Hashtbl.find program.locations region.ppoint.pp_id in
    let get_uncovered guard =
      let inv_guard = smk_and [invariants;guard] in
      let covered = find_in_lfp lfp region.ppoint.pp_id guard in
      let may_sat_guard = Bf_set.filter 
	  (fun absstate -> 
	    satisfiable trivial_context
	      inv_guard (stack_context region.preds absstate))
	  region.absstates
      in
      (* let sat_guard = coerce false [] region.preds trivial_context inv_guard may_sat_guard in *)
      let uncovered = Bf_set.diff may_sat_guard covered in
      (* update fixpoint data structure *)
      let _ = update_lfp_by_guard lfp region.ppoint.pp_id guard uncovered in
      uncovered
    in
    (* create successor region for given guarded command *)
    let create_succ_region (gc, succ_pp) =
      let succ_loc = get_location program succ_pp in
      let inherited = List.filter (has_prop Inherit) region.preds in
      let succ_preds = Pred.union_preds inherited succ_loc.loc_preds in
      let succ_invs = assumed_invs @ succ_loc.loc_invariants in
      let uncovered = get_uncovered gc.gc_guard in      
      let _ = add_preds_to_lfp lfp succ_pp.pp_id succ_preds in
      let succ_region = mk_succ region gc succ_pp succ_preds uncovered succ_invs in
      let _ = if !CmdLine.abstract_final && is_exit_pp program succ_pp then 
	succ_region.best_preds <- succ_region.preds 
      in succ_region
    in
    let unprocessed' = List.fold_left 
	(fun unprocessed' (gc, succ_pp) ->
	  if is_exit_pp program succ_pp && not !CmdLine.abstract_final
	  then begin
	    ignore (update_lfp_by_guard lfp region.ppoint.pp_id gc.gc_guard region.absstates);
	    unprocessed'
	  end 
	  else insert unprocessed' (create_succ_region (gc, succ_pp)))
	unprocessed loc.loc_cmds
    in 
    let _ = match loc.loc_cmds with 
    | [] -> ignore (update_lfp_by_guard lfp region.ppoint.pp_id mk_true region.absstates)
    | _ -> ()
    in
    unprocessed'
  in
  (* compute abstract states for region [region] and update list of unprocessed regions *)
  let compute_post region acc =
    let post_states = abstract_post lfp region program.wp 
    in
    let covered, _ = project_lfp_by_guard lfp region.ppoint.pp_id mk_true in
    if Bf_set.le post_states covered then acc else
    let new_absstates = Bf_set.diff post_states covered in
    let _ = region.absstates <- new_absstates in
    (* let _ = update_lfp lfp region.ppoint.pp_id new_absstates in *)
    (* check assertions if abstraction refinement *)
    match BohneRefine.check program region with
    | Some (region', new_preds) -> 
        (* found spurious error trace starting in [region']: *)
        (* remove subtree from region graph and recompute lfp *)
	let remove_unprocessed unproc r =
	  remove (fun r' -> is_parent r r') unproc
	in
	let acc' = remove_subtree remove_unprocessed acc region' in
	let _ = recompute_lfp lfp root_region in
        (* insert refined region in list of unprocessed regions *)
	let _ = match new_preds with
	| [] when not region'.use_best_post ->
	    let _ = Util.amsg("(r2) ") in
	    region'.use_best_post <- true;
	    region'.best_preds <- region'.preds
	| _ ->
	    let pred_diff = difference new_preds region'.preds in
	    if empty pred_diff then 
	      if empty (difference new_preds region'.best_preds) then begin
		print_endline "\nInfinite refinement loop detected. Abort analysis.";
		exit 1
	      end
	      else begin
		let _ = Util.amsg("(r2) ") in
		region'.use_best_post <- true;
		region'.best_preds <- union_preds region'.best_preds new_preds
	      end
	    else begin
	      let _ = Util.amsg("(r1) ") in
	      region'.best_preds <- union_preds region'.best_preds (intersect new_preds region'.preds);
	      add_preds lfp region' new_preds
	    end
	in insert acc' region'
    | None ->
	(* no counter-examples found: *)
        (* insert successors of [region] into list of unprocessed regions *)
	insert_succs region acc
  in
  (* fix point computation loop *)
  let rec fix unprocessed =
    if unprocessed = Pq.empty then lfp else
    let region, unprocessed' = extract unprocessed in
    let unprocessed' = compute_post region unprocessed' in 
    let _ = Util.amsg("(f) ") in
    fix unprocessed'
  in
  (* initialize list of unprocessed regions *)
  let region_queue = insert_succs root_region Pq.empty in
  fix region_queue

(** Analyze program *)
let analyze program =
  let entry_location = Hashtbl.find program.locations program.entry_point.pp_id in
  let start_time = 
    let ptime = Unix.times () in
    ptime.Unix.tms_utime +. ptime.Unix.tms_cutime  
  in
  let print_post_stats () =
    let total_time = 
      let ptime = Unix.times () in
      ptime.Unix.tms_utime +. ptime.Unix.tms_cutime -. start_time
    in 
    let dp_stats = stats ()
    and _ = reset_stats () in
    let max_row = max_row_length () in
    let dp_rel_time = dp_stats.total_time /. total_time *. 100.0 
    and dp_rel_cache_hits = float dp_stats.cache_hits /. float dp_stats.calls *. 100.0 in
    let stats = "\nSTATISTICS\n" ^
      Printf.sprintf "  # predicates: %d\n" (Pred.max_index ()) ^
      Printf.sprintf "  running time for analysis: %.2fs (DP: %.2f%%)\n" total_time dp_rel_time ^
      (* Printf.sprintf "  total running time for MONA: %.2fs (%.0f%%)\n" dp_stats.total_time  ^ *)
      Printf.sprintf "  avrg. running time for single call to DP: %.2fs\n" (dp_stats.total_time /. float_of_int (dp_stats.calls - dp_stats.cache_hits))^
      Printf.sprintf "  max. running time for single call to DP: %.2fs\n" dp_stats.max_time ^
      Printf.sprintf "  # calls to DP: %d\n" dp_stats.calls ^
      Printf.sprintf "  # cache hits: %d (%.2f%%)\n" dp_stats.cache_hits dp_rel_cache_hits ^
      Printf.sprintf "  max. cache row length: %d\n" max_row ^
      Printf.sprintf "  # calls for coerce: %d (%d)\n" !coerce_calls !coerce_calls_cached ^
      Printf.sprintf "  running time for coerce: %.2fs \n" !coerce_time ^
      Printf.sprintf "  # calls for split: %d (%d)\n" !split_calls !split_calls_cached ^ 
      Printf.sprintf "  running time for split: %.2fs \n" !split_time (* ^
      Printf.sprintf "  most expensive query:\n%s\n" (string_of_form dp_stats.max_query) *)
    in
    Util.msg stats
    (*  ;let f, row = max_row () in
    print_endline (string_of_form f ^ "\n");
    List.iter (fun (a, res) -> 
      print_abs_state stdout a; 
      Printf.printf "%B\n\n" res) row *)
  in
  let assumed_invariants = program.assumed_invariants in
  (* let _ = phase "Precomputing empty cubes" 
      (fun preds -> 
	empty_cubes := compute_empty_cubes (smk_and assumed_invariants) mk_true preds;
        Debug.print_msg 2 (fun chan -> Debug.newline (); print_cubes chan !empty_cubes))
      (get_all_preds ())
  in *)
  let root_region = phase "Computing initial abstract states"
      (abstract_init entry_location assumed_invariants) program.initial_states
  in
  let lfp = phase "Computing least fixed point"
      (fix program) root_region
  in 
  let _ = if !CmdLine.abstract_final then
    Debug.print_msg 1 
      (fun chan ->
	let exit_states, _ = project_lfp_by_guard lfp program.exit_point.pp_id mk_true in
	(* let exit_states = coerce preds (smk_and root_region.invariants) exit_states0 in *)
	output_string chan "\nFinal abstract states:\n";
	print_abs_states chan exit_states
      )
  in 
  (* let _ = print_cache stdout in *)
  print_post_stats ();
  lfp, root_region
