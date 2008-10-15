open BohneUtil
open BohneProgram
open Bf
open Bf_set
open Pred
open Form
open FormUtil


let entails_fast context f g =
  let f_impl_g = smk_impl (f, g) in
  BfCachedDecider.decide_fast context (concretize_preds f_impl_g)

let entails context f g =
  let f_impl_g = smk_impl (f, g) in
  BfCachedDecider.decide context (concretize_preds f_impl_g)

let satisfiable context guard f =
  let not_f = smk_impl (smk_and (guard::get_all_defs ()), smk_not f) in
  not (BfCachedDecider.decide context not_f)


(* maximal length of cubes *)
let max_cube_length = ref 2
    
let empty_cubes = ref Bf.bottom
	
let set_max_cube_length n = 
  max_cube_length := n

let print_cubes outchan cs =
  Bf.print outchan get_pred_name cs
    
let print_abs_state = print_cubes
    
let print_abs_states outchan abs_states =
  Bf_set.print outchan get_pred_name abs_states
    
let project_unknown preds bf =
  let preds_to_indices = List.map 
      (fun p -> p.pred_index)
  in
  let unknown = Util.difference 
      (preds_to_indices (get_all_preds ())) 
      (preds_to_indices preds)
  in Bf.exists unknown bf
  
let project_old_preds preds bf =
  let old_preds = List.fold_left 
      (fun acc p ->
	if is_old p then p.pred_index::acc
	else acc) 
      [] preds 
  in Bf.exists old_preds bf

    
let gamma_objs project_old preds abs_obj =
  let res = ref [] in
  let preds =
    if project_old then List.filter (fun p -> not (is_old p)) preds
    else preds
  in
  let convert_cube c =
    let cube = List.fold_left
	(fun cube p -> 
	  if c (Bf.var_index p.pred_index) = 0 then 
	    smk_not (pred_to_form false p)::cube 
	  else if c (Bf.var_index p.pred_index) = 1 then 
	    pred_to_form false p::cube
	  else cube) [] preds in
    res := mk_and cube::!res
  in
  Bf.foreach_cube abs_obj convert_cube;
  smk_or !res
	
let gamma_state project_old preds abs_state =
  let max_arity = List.fold_left (fun m p -> max p.pred_arity m) 0 preds in
  mk_foralls (typed_free_var_list max_arity, gamma_objs project_old preds abs_state)


let gamma_not_state project_old preds abs_state =
  let max_arity = List.fold_left (fun m p -> max p.pred_arity m) 0 preds in
  mk_foralls (typed_free_var_list max_arity, smk_not (gamma_objs project_old preds abs_state))

let gamma project_old preds abs_states =
  let process acc abs_state = gamma_state project_old preds abs_state::acc in
  smk_or (Bf_set.fold process [] abs_states)


let concretize_state_invariant preds abs_inv = 
  let null_inv =
    let null_cube = Bf.exists [null_pred] (Bf.upper_cube (Bf.conj abs_inv (Bf.mk_var null_pred))) in
    subst [(free_var_name 0, mk_null)] (gamma_objs false preds null_cube)	
  in
  let state_pred_inv =
    let invs =  List.fold_left (fun acc p ->
      let pv = Bf.mk_var (p.pred_index) in
      let p_inv =
	if Bf.le abs_inv pv then pred_to_form false p
	else if Bf.le abs_inv (Bf.neg pv) then mk_not (pred_to_form false p)
	else mk_true 
      in p_inv::acc) [] preds
    in smk_and invs
  in smk_and (state_pred_inv::null_inv::get_pred_defs preds)

let concretize_invariant preds abs_inv =
  let state_inv = concretize_state_invariant preds abs_inv in
  let full_inv = gamma_state false preds abs_inv in 
  smk_and [state_inv;full_inv]
	

(* heuristic that checks whether a predicate [p] is relevant 
 * for the abstraction of a formula [f] *)
let is_relevant f =
  let filter env = 
    Util.filter_map (fun (_, ty) -> ty = mk_object_type) fst env
  in
  let fv_f = free_object_vars (concretize_preds f) in
  fun p ->
    not (is_old p) 
    (* this heuristic tends to make things worse *)
    (* &&
    let fv_p = filter p.pred_env in
    not !CmdLine.useheuristics || fv_f = [] || fv_p = [] || 
    List.exists (fun v -> List.mem v fv_p) fv_f *)

let is_relevant4ec f =
  let filter env = 
    Util.filter_map (fun (_, ty) -> ty = mk_object_type) fst env
  in
  let fv_f = free_object_vars (concretize_preds f) in
  fun p ->
    not (is_old p) &&
    let fv_p = filter p.pred_env in
    fv_f = [] || fv_p = [] || 
    List.exists (fun v -> List.mem v fv_p) fv_f

let project_irrelevant preds f bf =
  let irrel_preds = List.fold_left 
      (fun acc p -> if is_relevant f p then acc else 
      p.pred_index::acc) [] preds
  in Bf.exists irrel_preds bf
    

let build_cubes preds exclude max_length =
  let rec extend_cubes preds complete_cubes acc acc_len =
    match preds with
    | p::preds' ->
	let skip_me = extend_cubes preds' complete_cubes acc acc_len in
	if exclude Bf.top true p && exclude Bf.top false p then skip_me
	else
	  let i = p.pred_index in
	  let acc' = 
	    List.fold_left 
	      (fun cs c -> 
		if exclude c false p then 
		  if exclude c true p then cs 
		  else Bf.conj (Bf.mk_var i) c::cs
		else
		  if exclude c true p then
		    Bf.conj (Bf.neg (Bf.mk_var i)) c::cs
		  else 
		    Bf.conj (Bf.mk_var i) c::
		    Bf.conj (Bf.neg (Bf.mk_var i)) c::cs)
	      [] acc
	  in
	  if not (acc' = []) then
	    if acc_len + 1 = max_length then
	      extend_cubes preds' (List.rev_append acc' skip_me) [Bf.top] 0
	    else 
	      extend_cubes preds' skip_me acc' (acc_len + 1)
	  else 
	    skip_me
    | _ -> complete_cubes
  in
  if max_length = 0 then [] else 
  extend_cubes preds [] [Bf.top] 0 
  

let compute_empty_cubes invs f preds =
  (* if not !CmdLine.useheuristics then Bf.bottom else *)
  (* restrict to cubes of length 2 *
   * cubes that are only build from singletons are never empty *)
  let is_empty c = entails trivial_context (smk_and [invs; f]) (smk_not (gamma_objs true preds c)) in
  let vars = List.fold_left 
      (fun acc p -> 
	if is_singleton p then
	  Bf.disj (Bf.mk_var p.pred_index) acc
	else acc)
      Bf.bottom preds
  in
  let exclude c s p = 
    is_old p ||
    not (Bf.eq c Bf.top) && (not (is_relevant4ec (gamma_state true preds c) p) || 
    is_singleton p && (Bf.le c vars || Bf.le (Bf.neg c) vars)) in 
  let cubes = build_cubes preds exclude 2 in
  List.fold_left 
    (fun acc c -> 
      if is_empty c then Bf.disj acc c
      else acc) 
    Bf.bottom cubes

let conj s p c = 
  Bf.conj c (if s then Bf.mk_var p.pred_index
  else Bf.neg (Bf.mk_var p.pred_index))

let disj s p c = 
  Bf.disj c (if s then Bf.mk_var p.pred_index
  else Bf.neg (Bf.mk_var p.pred_index))
 
let build_exclude_map preds max_length context f notf =
  let exclude_map = Hashtbl.create 0 in
  let check_pred ((f_cs, ge_f, notf_cs, ge_notf) as res) p =
    let i = p.pred_index in
    if not (is_old p) && is_relevant f p then
      let p_def = pred_to_form true p in
      let add sp sf =
	Hashtbl.add exclude_map i true;
	if sf then (disj sp p f_cs, ge_f, notf_cs, conj (not sp) p ge_notf) 
	else (f_cs, conj (not sp) p ge_f, disj sp p notf_cs, ge_notf)
      in	  
      let check sp sf cont () =
	if entails context 
	    (if sp then p_def else smk_not p_def)
	    (if sf then f else notf)
	then add sp sf else cont ()
      in
      if Bf.le (fst context) (Bf.mk_var i) 
      then check true true 
   (check true false (fun () -> Hashtbl.add exclude_map i true; res)) ()
      else if Bf.le (fst context) (Bf.neg (Bf.mk_var i)) 
      then check false true (check false false (fun () -> Hashtbl.add exclude_map i true; res)) ()
      else 
	check true true
	   (check true false
	     (check false false 
		(check false true (fun () -> res)))) ()
    else begin
      Hashtbl.add exclude_map i true; 
      res
    end
  in 
  let f_cubes, ge_f, notf_cubes, ge_notf = 
    List.fold_left check_pred (Bf.bottom, Bf.top, Bf.bottom, Bf.top) preds in
  let max_length = 
    min max_length (List.length preds - Hashtbl.length exclude_map) 
  in
  (* check whether over-approximations are precise *)
  let f_cubes, ge_f, notf_cubes, ge_notf =
    if not (Bf.eq ge_f Bf.top) &&
      entails context (gamma_objs true preds ge_f) f 
    then (Bf.disj f_cubes ge_f, Bf.top, notf_cubes, ge_notf)
    else if not (Bf.eq ge_notf Bf.top) &&
      entails context (gamma_objs true preds ge_notf) notf
    then (f_cubes, ge_f, Bf.disj notf_cubes ge_notf, Bf.top) 
    else (f_cubes, ge_f, notf_cubes, ge_notf)
  in 
  (exclude_map, ge_f, f_cubes, ge_notf, notf_cubes, max_length)
	
let uabstract_form preds context f notf skip_notf =
  let known_nonempty = project_unknown preds (Bf.neg !empty_cubes) in
  let conj s p c = 
    Bf.conj c (if s then Bf.mk_var p.pred_index
    else Bf.neg (Bf.mk_var p.pred_index))
  in 
  let exclude_map, ge_f, f_cubes, ge_notf, notf_cubes, max_length = 
    build_exclude_map preds !max_cube_length context f notf
  in
  let _ = Debug.print_msg 3 (fun chan -> 
    output_string chan "ge_f = ";  print_cubes chan ge_f;
    output_string chan "f_cubes = "; print_cubes chan f_cubes;
    output_string chan "ge_notf = "; print_cubes chan ge_notf;
    output_string chan "notf_cubes = "; print_cubes chan notf_cubes;
    Printf.fprintf chan "max_cube_length = %d\n" max_length;
    Printf.fprintf chan "exclude_map ="; print_cubes chan
      (Hashtbl.fold (fun i _ acc -> Bf.conj (Bf.mk_var i) acc) exclude_map Bf.top))
  in
  let rec uabstract k abs_f abs_notf =
    if k > max_length then 
      (Bf.conj abs_f (known_nonempty), Bf.conj abs_notf (known_nonempty))
    else
      let exclude_cubes = Bf.disj (Bf.disj !empty_cubes abs_f) abs_notf in 
      let exclude c s p = 
	Hashtbl.mem exclude_map p.pred_index || 
	Bf.le (conj s p c) exclude_cubes
      in
      let cubes = build_cubes preds exclude k in 
      let process_cube (abs_f, abs_notf) c = 
	let c_f = Bf.conj ge_f c in
	let def_c_f = gamma_objs true preds c_f in
	let c_notf = Bf.conj ge_notf c in
	let def_c_notf = gamma_objs true preds c_notf in
	let _ = Debug.print_msg 4 (fun chan -> print_cubes chan c_f) in
	if Bf.le c_f (fst context) then 
	  if entails context def_c_f f then 
	    (Bf.disj c_f abs_f, abs_notf)
	  else if not skip_notf && Bf.le c_notf (fst context) then
	    let _ = Debug.print_msg 4 (fun chan -> print_cubes chan c_notf) in
	    if entails context def_c_notf notf then 
	      (abs_f, Bf.disj c_notf abs_notf)
	    else (abs_f, abs_notf)
	  else (abs_f, abs_notf)
	else (abs_f, abs_notf)
      in
      let abs_f', abs_notf' = List.fold_left process_cube (abs_f, abs_notf) cubes in
      uabstract (k + 1) abs_f' abs_notf'
  in
  let abs_f, abs_notf = uabstract 2 f_cubes notf_cubes in
  (abs_f, abs_notf)

open CachedDecider

let split_calls = ref 0
let split_calls_cached = ref 0
let split_time = ref 0.0
let coerce_calls = ref 0
let coerce_calls_cached = ref 0
let coerce_time = ref 0.0
	
let stack_context preds abs_state =
  if not !CmdLine.useinstantiation then gamma_state true (Pred.get_all_preds ()) abs_state else
  let stack_info = List.fold_left 
      (fun acc p -> 
	let pv = Bf.mk_var p.pred_index in
	try 
	  let var = 
	    (* if p = null_decl then mk_null else *)
	    let var_name, _ = Util.find_map 
		(function IsSingleton x -> x | _ -> None) 
		p.pred_props
	    in mk_var var_name
	  in
	  let cube = gamma_objs true preds 
	      (Bf.upper_cube (Bf.conj abs_state pv))
	  in
	  subst [(free_var_name 0, var)] cube
	  :: acc
	with Not_found -> 
	  (* if Bf.le abs_state pv then gamma_state true [p] pv::acc else
	  if Bf.le abs_state (Bf.neg pv) then gamma_state true [p] (Bf.neg pv)::acc
	  else *) acc) [] preds
  in 
  smk_and (stack_info)



let coerce more_precise split_preds preds context guard absstates =
  let vars = List.fold_left 
      (fun acc p -> 
	if is_singleton p then
	  Bf.disj (Bf.mk_var p.pred_index) acc
	else acc)
      Bf.bottom preds
  in
  let res = ref Bf.top in
  let check_cube absstate c =
    let context absstate = 
      (absstate, 
       if not more_precise then stack_context preds 
       else fun absstate -> smk_and [stack_context preds absstate; gamma_state true split_preds absstate]) in  
    let monoms_c =
      List.fold_left
	(fun cubes q ->
	  let qi = q.pred_index in
	  if c (Bf.var_index qi) = 1 then
	    List.rev_map (conj true q) cubes
	  else if c (Bf.var_index qi) = 0 then 
	    List.rev_map (conj false q) cubes
	  else if c (Bf.var_index qi) = 2 && is_relevant guard q && List.mem q split_preds
	  then
	    List.fold_left 
	      (fun acc c -> 
		let c_and_q = conj true q c 
		and c_and_notq = conj false q c in
		let c1 = 
		  if not (Bf.le c_and_notq !empty_cubes)
		  then [c_and_notq] else []
		and c2 = 
		  if not (Bf.le c_and_q !empty_cubes)
		  then [c_and_q] else []
		in c1 @ c2 @ acc)
	      [] cubes
	  else cubes)
	[Bf.top] preds
    in
    match monoms_c with
    | [c] when Bf.le c vars -> ()
    | _ -> List.iter (fun c -> 
	let cached = (BfCachedDecider.stats ()).cache_hits in
	let time = (BfCachedDecider.stats ()).total_time in
	if entails (context absstate) guard (gamma_not_state true preds c)
	then res := Bf.conj !res (Bf.neg c);
	let cached' = (BfCachedDecider.stats ()).cache_hits in
	let time' = (BfCachedDecider.stats ()).total_time in
	coerce_calls_cached := !coerce_calls_cached + (cached' - cached);
	coerce_calls := !coerce_calls + 1;
	coerce_time := !coerce_time +. (time' -. time)) monoms_c
  in
  let prune_empty absstate =
    (* let context' = 
      (Bf.conj context absstate, 
       fun absstate -> smk_and [fn context; gamma_state true preds absstate])
    in *)
    let cached = (BfCachedDecider.stats ()).cache_hits in
    let time = (BfCachedDecider.stats ()).total_time in
    let res =
      if not (entails context guard (smk_not (stack_context preds absstate))) 
      then absstate else Bf.bottom
    in
    let cached' = (BfCachedDecider.stats ()).cache_hits in
    let time' = (BfCachedDecider.stats ()).total_time in
    split_calls_cached := !split_calls_cached + (cached' - cached);
    split_calls := !split_calls + 1;
    split_time := !split_time +. (time' -. time);
    res
  in
  let pruned = Bf_set.map prune_empty absstates in
  Bf_set.map (fun absstate ->
    let non_var_cubes = if more_precise then absstate else Bf.conj (Bf.neg vars) absstate in
    res := absstate; Bf.foreach_cube non_var_cubes (check_cube absstate); !res) pruned


let alpha preds invariants f0 =
  let f = mk_impl (invariants, f0) in
  let notf = mk_impl (invariants, smk_not f0) in
  let known_nonempty = project_unknown preds (Bf.neg !empty_cubes) in
  let abs_notf, _ = uabstract_form preds trivial_context notf f true in
  let abs_f = project_unknown preds (Bf.conj (Bf.neg abs_notf) known_nonempty) in
  abs_f 
    

let split_singletons preds split_preds absstates =
  let known_nonempty = project_unknown preds (Bf.neg !empty_cubes) in
  let process p acc absstate =
    let res = ref acc in
    let p_cubes = Bf.conj absstate (Bf.mk_var p.pred_index) in
    let notp_cubes = Bf.conj absstate (Bf.neg (Bf.mk_var p.pred_index)) in
    let process_cube c =
      let p_cubes = List.fold_left
	  (fun p_cubes q ->
	    let qi = q.pred_index in
	    if c (Bf.var_index qi) = 1 then
	      List.rev_map (Bf.conj (Bf.mk_var qi)) p_cubes
	    else if c (Bf.var_index qi) = 0 then 
	      List.rev_map (Bf.conj (Bf.neg (Bf.mk_var qi))) p_cubes
	    else if c (Bf.var_index qi) = 2 && (is_relevant (p.pred_def) q) && not (is_state_pred q) 
	    then List.fold_left 
		(fun acc c -> 
		  let c_and_q = Bf.conj (Bf.mk_var qi) c 
		  and c_and_notq = Bf.conj (Bf.neg (Bf.mk_var qi)) c in
		  if not (Bf.le c_and_q !empty_cubes) then 
		    if not (Bf.le c_and_notq !empty_cubes) then
		      c_and_q::c_and_notq::acc
		    else c_and_q::acc
		  else c_and_notq::acc) [] p_cubes
	    else p_cubes
	  ) [Bf.top] preds in
      List.iter (fun c -> 
	let absstate' = Bf.disj notp_cubes c in
	res := Bf_set.add !res absstate') p_cubes
    in
    let _ = Bf.foreach_cube p_cubes process_cube in
    !res
  in
  let process_p acc p =
    Bf_set.fold (process p) Bf_set.bottom acc
  in
  List.fold_left process_p absstates split_preds
  
