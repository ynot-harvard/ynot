open Util
open Ast
open AstUtil
open Form
open FormUtil
open PrintForm
open BohneUtil
open BohneProgram
open Pred

(** assume formulas in [fs] at all program location reachable from pp *)
let propagate program pp fs =
  let rec prop pp fs seen =
    let loc = get_location program pp in
    let fs' = List.filter (fun f ->
      List.for_all (fun f' -> not (equal f f')) loc.loc_invariants) fs
    in match fs' with
    | [] -> ()
    | _ ->
	let seen' = pp::seen in
	if not (is_exit_pp program pp)
	then loc.loc_invariants <- fs' @ loc.loc_invariants;
	List.iter (fun (_, succ_pp) ->
	  if not (List.mem succ_pp seen') then
	    prop succ_pp fs' seen') loc.loc_cmds
  in
  prop pp fs []

(** Perform a syntactic analysis of the program to derive some
 simple but useful facts *)
let speculate program =
  let wp = program.wp in
  let process_cmd pp (gc, succ_pp) =
    let succ_loc = get_location program succ_pp in
    let candidates =
      List.fold_left (fun acc p ->
	try
	  let x, _ = get_ident p in
	  (match normalize_form false (wp gc.gc_command (mk_var x)) with
	  | App(Const FieldRead, [fld; arg]) 
	  | App(fld, [arg])
	  | TypedForm (App(Const FieldRead, [fld; arg]), _)
	  | TypedForm (App(fld, [arg]), _) ->
	      if equal fld (normalize_form false (wp gc.gc_command fld)) then
		(x, fld, arg)::acc
	      else acc
	  | _ -> acc)
	with Not_found -> acc) 
	[] succ_loc.loc_preds
    in
    let potential_invs = 
      List.fold_left (fun acc p ->
	try
	  let x', _ = get_ident p in
	  let wp_x' = normalize_form false (wp gc.gc_command (mk_var x')) in
	  try
	    if not (equal wp_x' (mk_var x')) then
	      let x, fld, _ =
		List.find (fun (_, _, arg) -> equal arg wp_x') candidates
	      in 
	      let f = mk_eq (App(fld, [mk_var x']), mk_var x) in
	      f::acc
	    else acc
	  with Not_found -> acc
	with Not_found -> acc) [] 
	succ_loc.loc_preds
    in 
    let new_preds = List.map (fun f -> add_pred f []) potential_invs in
    succ_loc.loc_preds <- union_preds succ_loc.loc_preds new_preds; 
    propagate program succ_pp potential_invs
  in 
  let process_loc loc_pp loc =
    List.iter (process_cmd loc_pp) loc.loc_cmds
  in Hashtbl.iter process_loc program.locations

(** recursively remove all previously assumed, but not provable facts *)
let fix program =
  let module Pq = 
    PriorityQueue(struct 
      type el = location
      type context = bohne_program
	    
      let equal l1 l2 =
	l1.loc_pp.pp_id = l2.loc_pp.pp_id
	  
      let compare prog l1 l2 = compare_pps prog l1.loc_pp l2.loc_pp
    end) in
  let assumed_invs = program.assumed_invariants in
  let insert = Pq.insert program in
  let extract = Pq.extract program in
  let is_preserved invs gc f = 
    let wp_f = program.wp gc.gc_command f in
    let g = (smk_impl (smk_and (gc.gc_guard::invs @ assumed_invs), 
		       wp_f))
    in (* print_endline (string_of_form g ^ "\n"); *)
    BfCachedDecider.decide trivial_context g      
  in
  let update_todo loc todo =
    let invs = loc.loc_invariants in
    List.fold_left 
      (fun todo' (gc, succ_pp) ->
	let succ_loc = get_location program succ_pp in
	if succ_pp.pp_id = program.exit_point.pp_id then
	  (succ_loc.loc_invariants <- [];
	   todo')
	else
	  let old_invs = succ_loc.loc_invariants in
	  let new_invs, has_changed = 
	    List.fold_left 
	      (fun (invs', has_changed) f ->
		if (* List.mem f old_invs && *) is_preserved invs gc f then
		  (f::invs', has_changed)
		else 
		  (invs', true))
	      ([], false) old_invs (* invs *)
	  in
	  if has_changed then
	    (succ_loc.loc_invariants <- new_invs;
	     insert todo' loc)
	  else todo')
      todo loc.loc_cmds 
  in
  let rec fix todo = 
    if todo = Pq.empty then () else
    let loc, todo' = extract todo in
    fix (update_todo loc todo')
  in 
  let todo = Hashtbl.fold 
      (fun _ loc todo -> insert todo loc)
      program.locations Pq.empty
  in 
  fix todo;
  (* remove all state predicates that are invariant *)
  Hashtbl.iter 
    (fun _ loc ->
      let inv_preds = List.fold_left
	(fun acc f ->
	  try get_pred_by_def f::acc
	  with Not_found -> acc) 
	  [] loc.loc_invariants
      in
      let preds = 
	List.filter (fun p -> 
	  not (List.exists (fun p' -> p'.pred_index = p.pred_index) inv_preds))
	  loc.loc_preds 
      in loc.loc_preds <- preds)
    program.locations  

(** Find some simple invariants and propagate them along with 
   conjuncts from initial states formula *)
let analyze program =
  speculate program; 
  propagate program program.entry_point (split_conjuncts program.initial_states);
  fix program
