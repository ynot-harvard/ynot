open Util
open Ast
open AstUtil
open Form
open FormUtil
open PrintForm
open Sast
open Vcgen
open BohneUtil
open Pred
open BohneProgram
open Region
open Abstraction
open Bohne

(** Find program point of command *) 
let find_program_point exit_point c =
  let rec find_in_list cs =
      List.fold_left (fun acc c ->
	if acc = exit_point then find c else acc)
	exit_point cs
  and find c = 
    match c with 
    | Basic bc -> bc.bcell_point
    | Seq cs | Choice cs -> find_in_list cs
    | If ic -> find_in_list [ic.if_then; ic.if_else]
    | Loop lc -> find_in_list [lc.loop_prebody; lc.loop_postbody]
    | Return _ -> exit_point
  in find c


(** Identify candidate loop invariants which would be useful for the 
   synthesis (currently tree and field constraints) *)
let find_candidate_invariants pre_cond =
  let pres = split_conjuncts pre_cond in
  List.fold_left 
    (fun (pre_cond', helper_invs) f ->
      if is_tree_constraint f || is_field_constraint f 
      then (pre_cond', f::helper_invs)
      else (f::pre_cond', helper_invs))
    ([], []) pres
  
(** Expand definitions of specvars [todo] in specvars [acc] *)
let rec expand_vardefs acc todo =
  match todo with
  | (v, _ as vdef)::todo' ->
      let s (v, def) = (v, subst [vdef] def) in
      expand_vardefs (List.map s acc) (List.map s todo') 
  | _ -> acc


(** Desugar procedure into a Bohne program *)
let convert_proc prog im spec m0 p =
  let shorthands = expand_vardefs im.im_vardefs im.im_vardefs in
  let m = expand_vardefs m0 im.im_vardefs in
  let exit_point = fresh_program_point () in
  let entry_point = find_program_point exit_point p.p_body in
  let idents = 
    List.map (fun d -> d.global_name) prog.p_globals @
    List.map (fun d -> d.field_name) prog.p_ref_fields @
    List.map (fun d -> d.field_name) prog.p_prim_fields @
    List.fold_left (fun acc d -> if d.vd_ghost then acc else d.vd_name::acc) [] p.p_locals @
    List.map (fun d -> d.vd_name) p.p_header.p_formals @
    List.map fst m @
    pseudo_constants
  in 
  let wp cs f = 
    let wp_bc = wp_bc prog im p spec m None in
    let wp_f = List.fold_left (fun f c -> wp_bc c f) f cs in
    (* alpha_rename (Util.union idents (fv f)) *) wp_f
  in
  let pre_cond0 = concretized_pre prog im spec in
  let _ = Debug.lmsg 2 (fun () ->
    "Initial states of procedure:\n" ^ string_of_form pre_cond0 ^ "\n") in
  let post_cond0 = concretized_post prog im p spec in
  let post_cond = subst shorthands (post_cond0) in
  let pre_cond1, invs = find_candidate_invariants (subst shorthands pre_cond0) in
  let _ =  Debug.lmsg 3 (fun () ->
    "Loop invariant candidates:\n" ^ string_of_form (smk_and invs) ^ "\n") 
  in
  let pre_cond = smk_and (pre_cond1 (* @ Background.get_alloc_conditions prog *)) in
  let program = 
    {locations = Hashtbl.create 0;
     entry_point = entry_point;
     exit_point = exit_point;
     wp = wp;
     assumed_invariants = invs;
     initial_states = pre_cond;
     idents = idents}
  in
  (* collect predicates that are explicitely mentioned in pre- and postcondition *)
  let collect_preds = 
    List.fold_left 
      (fun preds (x, ty) ->
	match normalize_type ty with
	| TypeApp (TypeObject, []) | TypeApp (TypeSet, [TypeApp (TypeObject, [])]) | TypeApp (TypeBool, []) ->
	if is_oldname x || List.exists (fun (x', _) -> x' = x) m then
	  let def = 
	    if is_oldname x then 
	      Binder (Comprehension, [typed_free_var 0],
		      mk_elem (free_var 0, mk_var x))
	    else List.assoc x m
	  in
	  let props = Inherit :: 
	    (if is_oldname x then [IsConst; IsOld (unoldname x)]
	    else []) @
	    (match normalize_type ty with
	    | TypeApp (TypeInt, [])
	    | TypeApp (TypeObject, [])
	    | TypeApp (TypeString, [])
	      -> [IsSingleton None]
	    | _ -> [])
	  in
	  let x_pred = add_pred_decl x def props in
	  union_preds [x_pred] preds
	else preds
	| _ -> preds)
  in 
  let final_preds = 
    collect_preds [] (get_annotated_types post_cond0) 
  in
  let initial_preds =
    collect_preds (null_decl::final_preds) (get_annotated_types pre_cond0)
  in
  let add_location exit (preds, seqs) asserts =
    let mk_gc guard seq = {gc_guard = guard; gc_command = seq} in
    let process_seq (entry, seq) =
      let loc = 
	try Hashtbl.find program.locations entry.pp_id 
	with Not_found ->
	  let new_loc = 
	    {loc_pp = entry;
	     loc_cmds = [];
	     loc_preds = [];
	     loc_invariants = [] (* invs *);
	     loc_assertions = List.map (fun a -> (gc_skip (), a)) asserts}
	  in Hashtbl.add program.locations entry.pp_id new_loc; new_loc
      in 
      loc.loc_preds <- union_preds loc.loc_preds preds;
      if not (empty seq) then 
	loc.loc_cmds <- (mk_gc mk_true seq, exit) :: loc.loc_cmds
    in
    List.iter process_seq seqs
  in
  let _ = add_location exit_point (final_preds, [(exit_point, [])]) [post_cond] in
  let mk_annot_form fs = {annot_form = smk_and fs; annot_msg = ""} in
  let add_cmd (preds, seqs) c0 = 
    let expand af =
      {annot_form = subst shorthands af.annot_form; 
       annot_msg = af.annot_msg}
    in
    let c = match c0 with
    | Assume af -> Assume (expand af)
    | Assert af -> Assert (expand af)
    | NoteThat af -> NoteThat (expand af)
    | Split af -> Split (expand af)
    | _ -> c0
    in
    (preds, List.rev_map (fun (entry, seq) -> (entry, c::seq)) seqs)
  in
  let vardefs = expand_vardefs p.p_vardefs im.im_vardefs @ m in
  let add_pred (preds, seqs) specvar = 
    let def = 
      try List.assoc specvar (vardefs)
      with Not_found -> 
	Util.warn ("Tracked unknown specvar '" ^ specvar ^ "'"); 
	mk_true 
    in
    let preds' = 
      let ty = TypeReconstruct.get_type [] def in
      if ty = mk_set_type mk_object_type ||
      ty = mk_object_type ||
      ty = mk_bool_type then
	let pred = add_pred_decl specvar def [] in
	union_preds [pred] preds
      else preds
    in (preds', seqs)
  in    
  let append_seqs (preds1, seqs1) (preds2, seqs2) =
    (union_preds preds1 preds2, List.rev_append seqs1 seqs2)
  in
  let rec convert_command seqs cs =
	match cs with
	| c::cs' -> (match c with
	  | Basic bc -> 
	      (match bc.bcell_cmd with
	      |	Hint (TrackSpecvar tsv) ->
		  convert_command (add_pred seqs tsv.track_var) cs'
	      (* treat "assume false" as a return statement *)
	      |	Assume afc when afc.annot_form = mk_false ->
		  add_location exit_point seqs []; ([], [])  
	      |	cmd -> convert_command (add_cmd seqs cmd) cs') 
	  | Seq cs -> convert_command seqs (cs @ cs')
	  | Choice cs -> 
	      let seqs' = List.fold_left (fun acc c -> 
		append_seqs (convert_command seqs [c]) acc) ([], []) cs 
	      in convert_command seqs' cs'
	  | If ic -> 
	      let it_cond = Assume (mk_annot_form [ic.if_condition])
	      and ie_cond = Assume (mk_annot_form [smk_not ic.if_condition]) in
	      let seqs_it = convert_command (add_cmd seqs it_cond) [ic.if_then]
	      and seqs_ie = convert_command (add_cmd seqs ie_cond) [ic.if_else] in
	      convert_command (append_seqs seqs_it seqs_ie) cs'
	  | Loop lc ->
	      let loop_point = find_program_point exit_point c in
	      let _ = add_location loop_point seqs [] in
	      let loop_inv = 
		try NoteThat (mk_annot_form [unsome lc.loop_inv])
		with _ -> Skip		  
	      in
	      let assume_enter = Assume (mk_annot_form [lc.loop_test]) in
	      let assume_exit = Assume (mk_annot_form [smk_not lc.loop_test]) in
	      let loop_preseqs = 
		let seqs = convert_command ([], [(loop_point, [])]) [lc.loop_prebody] in
		add_cmd seqs loop_inv
	      in
	      let loop_bodyseqs = 
		convert_command (add_cmd loop_preseqs assume_enter) [lc.loop_postbody] 
	      in
	      let _ = add_location loop_point loop_bodyseqs [] in
	      convert_command (add_cmd loop_preseqs assume_exit) cs'
	  | Return rc ->
	      let seqs' =
		match rc.return_exp with
		| None -> seqs
		| Some e -> 
		    let return_c = VarAssign 
			{assign_lhs = result_var; 
			 assign_tlhs = (result_var, spec.p_restype); 
			 assign_rhs = e}
		    in add_cmd seqs return_c
	      in add_location exit_point seqs' []; ([], []))
	  | [] -> seqs
  in 
  let _ = match convert_command (initial_preds, [(entry_point, [])]) [p.p_body] with
  | (_, []) -> ()
  | seqs -> add_location exit_point seqs []
  in program

(** Initialize all modules *)
let init () =
  BfCachedDecider.reset_stats ();


open Bf
open Bf_set

(** Annotate procedure with result of analysis *)
let annotate_proc program lfp root_region p =
  let mk_assume f msg =
    let mk_basic_cell c = Basic
	{bcell_cmd = c;
	   bcell_point = fresh_program_point ();
	 bcell_known_before = [];
	 bcell_known_after = []}
    in
    if f = mk_true then [] else
    [mk_basic_cell (Assume {annot_form = f; annot_msg = msg})]
  in
  let mk_decaf_inv pp = 
    let loc = get_location program pp in
    let _ = Debug.print_msg 1 (fun chan -> 
      Printf.fprintf chan "Annotating invariant for location %d:\n" pp.pp_id;
      output_string chan (string_of_form (strip_types (smk_and loc.loc_invariants)) ^ "\n"))
    in smk_and loc.loc_invariants
  in
  let mk_bohne_inv pp =
    let loc = get_location program pp in
    let preds = loc.loc_preds in
    let abs_state_list, lfp_preds = project_lfp lfp pp.pp_id in
    let inv_preds = if is_exit_pp program pp then preds else lfp_preds in
    let abs_inv = List.fold_left (fun acc (_, s) -> Bf.disj s acc) Bf.bottom abs_state_list in
    let state_inv = concretize_state_invariant inv_preds abs_inv in
    let abs_region_invs = collect root_region pp in
    let _ = Debug.print_msg 1 (fun chan -> 
      Printf.fprintf chan "Annotating invariant for location %d:\n" pp.pp_id;
      print_abs_states chan (List.fold_left (fun acc s -> Bf_set.union acc (Bf_set.singleton s)) Bf_set.bottom abs_region_invs))
    in    
    let region_invs = smk_or (List.rev_map (gamma_state false inv_preds) abs_region_invs) in
    smk_and [state_inv; region_invs]
  in
  let final_assumes = 
    if !CmdLine.abstract_final then 
      mk_assume (mk_bohne_inv program.exit_point) "Bohne decaf claims" @
      mk_assume (mk_decaf_inv program.exit_point) "Bohne claims"
    else []
  in
  let rec write_back c =
    match c with 
    | Basic bc -> 
	(match bc.bcell_cmd with
	 (* treat "assume false" as a return statement *)
	| Assume afc when afc.annot_form = mk_false ->
	    Seq (final_assumes @ [c])
	| _ -> c)
    | Return _ -> Seq (final_assumes @ [c])
    | Seq cs -> Seq (List.map write_back cs)
    | Choice cs -> Choice (List.map write_back cs)
    | If ic -> 
	let it' = write_back ic.if_then in
	let ie' = write_back ic.if_else in
	let ic' = {if_condition = ic.if_condition;
		   if_then = it';
		   if_else = ie'}
	in If ic'
    | Loop lc -> 
	let pp = find_program_point program.exit_point c in
	let decaf_assumes = mk_assume (mk_decaf_inv pp) "Bohne decaf claims" in
	let loop_assumes = mk_assume (mk_bohne_inv pp) "Bohne claims" in
	let loop_inv' = smk_and (safe_unsome mk_true lc.loop_inv::program.assumed_invariants) in 
	let lc' = {loop_inv = Some loop_inv';
		   loop_prebody = Seq (decaf_assumes @ loop_assumes @ [write_back lc.loop_prebody]);
		   loop_test = lc.loop_test;
		   loop_postbody = write_back lc.loop_postbody}
	in Loop lc'
  in 
  let p_body' = write_back p.p_body in
  {p_header = p.p_header;
   p_locals = p.p_locals;
   p_vardefs = p.p_vardefs;
   p_body = Seq (p_body'::final_assumes);
   p_simple_body = p.p_simple_body}

(** Main procedure *)
let analyze_proc (prog : program) (im : impl_module)
    (p : proc_def) (spec : proc_header) (m : specvar_def list) : proc_def =
  (* initialize all modules *)
  let _ = init () in
  (* convert proc p into a Bohne program *)
  let program = convert_proc prog im spec m p in
  let _ = propagate_asserts_assumes program in
  let _ = 
    if !CmdLine.derive_preds then
      phase "Deriving initial predicates" derive_initial_predicates program 
  in 
  let _ = 
    phase "Propagating context" BohneDecaf.analyze program 
  in 
  let _ = Debug.print_msg 1 (fun chan -> print_program chan program) in
  (* analyze Bohne program *)
  let lfp, root_region = Bohne.analyze program in
  annotate_proc program lfp root_region p
