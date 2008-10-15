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

let guard_marker = "__guard"

let mark_as_guard f =
  match f with
  | App (Const Comment, [Const (StringConst s); f]) when s = guard_marker -> f
  |  _ -> mk_comment guard_marker f

(** Report counter-example *)
let report_counter_example is_real region trace last_wp = 
  if is_real then print_endline "\n\nCOUNTER-EXAMPLE:\n"
  else print_endline "\n\nSPURIOUS COUNTER-EXAMPLE:\n";
  print_endline "Error trace:\n";
  let prettify_form f =
    let f0 = normalize_form false f in
    let f1 = strip_types f0 in
    string_of_form (unlambda f1)
  in
  let _ = List.fold_left (fun pp (region, gc, pp'_opt) ->
    print_abs_state stdout (Bf_set.join region.absstates);
    let pp' = safe_unsome (AstUtil.fresh_program_point ()) pp'_opt in
    print_newline ();
    print_command stdout pp (gc, pp'); pp') region.ppoint trace
  in
  (* Printf.printf "Violated property:\n\n%s\n\n" (prettify_form orig_assn); *)
  if not is_real then 
    Printf.printf "Last violated weakest precondition:\n\n%s\n\n" 
      (prettify_form last_wp);
  exit 0

let is_guard_comment =
  let guard_regexp = Str.regexp (".*" ^ guard_marker) in
  fun c -> try Str.search_forward guard_regexp c 0 >= 0 with Not_found -> false

(** Extracts predicates from a formula *)
let extract_preds (f : form) =
  let rec atoms acc = function
    | App (Const Not, fs)
    | App (Const Or, fs)
    | App (Const And, fs)
    | App (Const MetaAnd, fs)
    | App (Const Impl, fs) 
    | App (Const MetaImpl, fs)
    | App (Const Iff, fs) ->
	List.fold_left atoms acc fs
    | App (Const Comment, [Const StringConst c; f0]) ->
	if is_guard_comment c then acc
	else atoms acc f0
    | TypedForm (f0, _) -> atoms acc f0
    | App (Const Eq, [TypedForm (Var _, ty); TypedForm (Var _, _)]) 
    | App (Const Eq, [TypedForm (Const NullConst, ty); TypedForm (Var _, _)]) 
    | App (Const Eq, [TypedForm (Var _, ty); TypedForm (Const NullConst, _)]) 
    | App (Const Eq, [TypedForm (Const NullConst, ty); TypedForm (Const NullConst, _)]) 
      when ty = TypeApp(TypeObject, []) -> acc
    | f -> if Decider.test_valid ([], f) || Decider.test_valid ([f], mk_false) ||
      List.exists (equal f) acc then acc else f::acc
  in atoms [] f

(* simplify formula for predicate extraction *)
let simplify_form skolem_consts f0 =
  let sq, _ = elim_free_vars false skolem_consts (sequent_of_form f0) in
  let f1 = unlambda (form_of_sequent sq) in
  let f2, env = TypeReconstruct.reconstruct_types (get_annotated_types f1) f1 in
  let f3, env1 = 
    TermRewrite.rewrite true 
      [TermRewrite.rewrite_tree; 
       TermRewrite.rewrite_FieldRead_FieldWrite] 
      env f2
  in
  elim_quants f3, env1


let refine trace f0 skolem_consts_env =
  (* extract region from error trace which is going to be refined *)
  let region, _, _ = List.hd trace in
  (* remove type information from skolem constants *)
  let skolem_consts = List.map fst skolem_consts_env in
  let f, env = simplify_form skolem_consts f0 in
  let _ = Debug.print_msg 1 (fun chan ->
    Printf.fprintf chan "\nRefining region for pp. %d with:\n" region.ppoint.pp_id;
    output_string chan (string_of_sequent (sequent_of_form f) ^ "\n"))
  in
  let region_join = Bf_set.join region.absstates in
  let context =
    (region_join, concretize_invariant region.preds)    
  in
  let inv = smk_and region.invariants in
  (* extract atomic formulae from f *)
  let atoms = extract_preds f in
  (* generate predicates from atoms *)
  let new_preds = List.fold_left (fun acc p ->
    match Util.intersect (fv p) skolem_consts with
    | [] -> 
	(* state predicate *)
	if decide context (smk_impl (inv, p)) ||
	decide context (smk_impl (inv, smk_not p))
	then acc else 
	  add_pred p [Inherit]::acc
    | [v] when List.assoc v env = mk_object_type ->
	(* unary predicate on objects *)
	let p_def = Binder (Comprehension, [(v, mk_object_type)], p) in
	union_preds [add_pred p_def [Inherit]] acc
    | _ -> 
	(* for now ignore all others *)
	acc) [] atoms
  in
  let _ = Debug.print_msg 1 (fun chan -> 
    output_string chan "Adding predicates:\n";    
    List.iter (fun p -> print_pred_decl chan p) new_preds)
  in
  Some (region, new_preds)


(* try to factorize a conjunct from a disjunction of conjunctions to improve
   splitting into prove subgoals.
   e.g. (A & B | ~A & C | ~A | D)) becomes (A --> B) & (~A --> C | D) *)
let factorize disj =
  let rec conjuncts d =
    match d with
    | App (Const And, fs)
    | App (Const MetaAnd, fs) -> List.concat (List.rev_map conjuncts fs)
    | App (Const Not, [App (Const Or, fs)]) -> List.concat (List.rev_map (fun f -> conjuncts (smk_not f)) fs) 
    | _ -> [d]
  in
  match disj with
  | d::disj' ->
      (try find_map (fun f ->
	try let pos, neg = 
	  List.fold_left (fun (pos, neg) d ->
	    let cs, kind = List.fold_left 
		(fun (cs, kind) c -> 
		  if equal f c then (cs, Some true)
		  else if equal f (smk_not c) then (cs, Some false)
		  else (c::cs, kind)) ([], None) (conjuncts d)
	    in match kind with
	    | Some true -> (smk_and cs::pos, neg)
	    | Some false -> (pos, smk_and cs::neg)
	    | None -> raise Not_found) ([], []) disj
	in Some [smk_impl (f, smk_or pos); smk_impl (smk_not f, smk_or neg)]
	with Not_found -> None)
	  (conjuncts d)
      with Not_found -> [smk_or disj])
  | _ -> [smk_or disj]

(** Check assertions and analyze potential counter-examples *)
let check_assertions program region gc_assns =
  let rec analyze region trace pp_opt skolem_consts (src_states, gc, assn) =
   let region_join = Bf_set.join src_states in
    let context =
      (region_join, concretize_invariant region.preds)    
    in
    let inv = smk_and region.invariants in
    (* recursively split violated assertions to find a smallest violated subformula *)
    let rec check_assn skolem_consts wp_assn =
      if not (decide context (smk_impl (inv, wp_assn))) then
	let split_assn = wp_assn in
	let env = 
	  TypeReconstruct.get_env 
	    (form_of_sequent ([snd context (fst context); inv], split_assn)) 
	in
	let split_assn1, _ = 
	  TermRewrite.rewrite true 
	    [TermRewrite.rewrite_tree; 
	     TermRewrite.rewrite_FieldRead_FieldWrite] 
	    env (TypeReconstruct.disambiguate split_assn)
	in
	let split_assn2 = elim_quants split_assn1 in
	let split_assns = 
	  List.map (fun ((asms, hyp), env) ->
	    let env' = env @ skolem_consts in
	    let hyp', _ =  TermRewrite.rewrite true [TermRewrite.rewrite_sets] env' hyp in
	    env' , form_of_sequent (asms, elim_quants hyp')) (Decider.generate_sequents [] split_assn2) 
	in
	try (match split_assns with
	| [cs, f] ->
	    (match f with
	    | App (Const MetaImpl, [f;f1]) 
	    | App (Const Impl, [f;f1]) ->
		(match f1 with 
		| App(Const Or, disj)
		| App(Const Comment, [_; App(Const Or, disj)]) ->
		    (match factorize disj with
		    | [f] -> Some (f, cs)
		    | assns' ->   
			Some (Util.find_map (check_assn cs) (List.rev_map (curry smk_impl f) assns')))
		| App (Const Iff, [f11; f12])
		| App (Const Comment, [_; App(Const Iff, [f11; f12])]) ->
		    Some (Util.find_map (uncurry check_assn) 
			    [cs, smk_impl (smk_and [f; f11], f12);
			     cs, smk_impl (smk_and [f; f12], f11)])
		| App (Const And, fs) 
		| App (Const Comment, [_; App(Const And, fs)]) ->
		    Some (Util.find_map (check_assn cs) (List.rev_map (curry smk_impl f) fs))
		| App (Const Not, [App (Const Or, fs)])
		| App (Const Comment, [_; App (Const Not, [App(Const Or, fs)])]) ->
		    Some (Util.find_map (check_assn cs) (List.rev_map (fun f' -> smk_impl (f, smk_not f')) fs))
		| App (Const Not, [App (Const And, f2::fs)])
		| App (Const Comment, [_; App (Const Not, [App(Const And, f2::fs)])]) ->
		    check_assn cs (smk_impl (smk_and [f;f2], smk_not (smk_and fs)))
 		| f1 -> Some (smk_impl (f, f1), cs))
	    | _ -> Some (f, cs))
	| _ -> Some (Util.find_map (uncurry check_assn) split_assns))
	with Not_found -> None
      else None
    in
    let trace' = (region, gc, pp_opt)::trace in
    let mk_wp f = smk_impl (mark_as_guard gc.gc_guard, program.wp gc.gc_command f) in
    let wp_assn = mk_wp assn in
    let _ = if pp_opt = None then 
      Debug.print_msg 3 (fun chan -> 
	output_string chan ("\nChecking assertion:\n" ^ (string_of_form (strip_types wp_assn)) ^ "\n"))
    in
     match check_assn skolem_consts wp_assn with
    (* assertion is violated in current region *)
    | Some (wp_assn', skolem_consts') ->
	Debug.print_msg 3 (fun chan ->
	  output_string chan 
	    ("\nViolated formula:\n" ^ 
	     string_of_form (form_of_sequent ([snd context (fst context);inv], wp_assn')) ^ "\n"));
	if is_root region then 
	  let f = smk_impl (program.initial_states, wp_assn') in
	  if not (decide trivial_context f)
	  then (* found real counter-example *)
	    report_counter_example true region trace' wp_assn'
	  else (* full trace is spurious *)
	    refine trace' wp_assn' skolem_consts'
	else (* continue analysis with parent region *)
	  let parent_gc, src_states, parent_region = region.parent in 
	  analyze !parent_region trace' (Some region.ppoint) skolem_consts' (src_states, parent_gc, wp_assn') 
    (* assertion is not violated in current region *)
    | None -> 
	(match pp_opt with
	| None -> 
            (* empty error trace, i.e. assertion verifies *) None
	| Some pp -> 
	    (* spurious part of trace starts from current region *)
	    refine trace assn skolem_consts)
  in
  try Some (Util.find_map (analyze region [] None []) ((* List.rev *)gc_assns))
  with Not_found -> None


(* count maximal number of quantified variables in the same scope *)
let count_max_bound =
  let add xs (x, _) = if List.mem x xs then xs else x::xs in
  let rec count bound old_max = function
    | App (Const Or, fs)
    | App (Const And, fs)
    | App (Const MetaAnd, fs)
    | App (Const Comment, Const StringConst _::fs)
    | App (Const Impl, fs) 
    | App (Const MetaImpl, fs)
    | App (Const Not, fs)
    | App (Const Iff, fs) ->
	List.fold_left (count bound) old_max fs
    | TypedForm (f1, _) -> count bound old_max f1
    | Binder (Forall, vs, f1)
    | Binder (Exists, vs, f1) ->
	count (List.fold_left add bound vs) old_max f1
    | _ -> max old_max (List.length bound)
  in count [] 0
  

(* check assertions for region [region] *)
let check program region =
  if not !CmdLine.refine then None else
  let loc = get_location program region.ppoint in
  let exit_loc = get_location program program.exit_point in
  let postconds gc1 = 
    List.map (fun (gc2, f) -> (region.absstates, compose program gc1 gc2, f))
      exit_loc.loc_assertions 
  in  
  let assertions = List.fold_left 
      (fun assertions (gc, succ_pp) ->
	if is_exit_pp program succ_pp && not !CmdLine.abstract_final
	then assertions @ postconds gc else assertions)
      (List.map (fun (gc, f) -> (region.absstates, gc, f)) loc.loc_assertions) loc.loc_cmds
  in
  let checked_region, assertions = 
    if not (is_exit_pp program region.ppoint) then
      region, assertions
    else
      let gc1, src_states, parent_ref = region.parent in
      let exit_invariant = concretize_invariant region.preds (Bf_set.join region.absstates) in
      let assertions = List.map (fun (gc2, f) -> 
	(src_states, compose program gc1 gc2, smk_impl (mark_as_guard exit_invariant, f))) exit_loc.loc_assertions
      in !parent_ref, assertions
  in
  let split_assertions = 
    List.concat (List.map (fun (r, c, f) ->
      List.map (fun f -> (r, c, f)) (split_conjuncts f)) assertions)
  in
  let sorted_assertions =
    let extended = List.rev_map (fun (_,_, f as a) ->
      (a, count_max_bound (fst (simplify_form [] f)))) split_assertions in
    let sorted = List.stable_sort (fun (_, c1) (_, c2) -> compare c1 c2) extended in
    List.map fst sorted
  in check_assertions program checked_region sorted_assertions
