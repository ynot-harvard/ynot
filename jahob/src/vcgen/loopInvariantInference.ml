(** Loop invariant inference *)

open Ast
open Form
open FormUtil

exception Invariant_violation

(* Generate a fresh variable. *)
let id_counter : int ref = ref 0
let increment_id (i : ident) : ident =
  id_counter := !id_counter + 1;
  (i ^ "_" ^ (string_of_int !id_counter))

let get_callee_header (pc : proc_call) : proc_header =
  match pc.callee_hdr with
    | None -> failwith ("LoopInvariantInference: unresolved call to " ^ pc.callee_name ^ "\n")
    | Some header -> header

(* Compute the strongest postcondition of f over (VarAssign ac) *)
let sp_VarAssign (ac : assign_command) (f : form) : form =
  let x = ac.assign_lhs in
  let e = ac.assign_rhs in
  let x0 = (increment_id x) in
  let v0 = mk_var x0 in (* give a new name to the old value of the variable *)
  let renameMap = [(x, v0)] in
  let f0 = subst renameMap f in (* substitute the new variable for the old in f *)
  let e0 = subst renameMap e in (* substitute the new variable for the old in e *)
  let f1 = smk_and [f0; mk_eq((mk_var x), e0)] in
    (* Implicitly existential quantified, needs to be on LHS of implication. *)
    FormUtil.smk_fixand_eq [x0] f1 (* get rid of some equalities *)
    
(* Compute the strongest postcondition of f over (Alloc ac) *)
let sp_Alloc (ac : alloc_command) (f : form) : form =
  let x = ac.alloc_lhs in
  let t = ac.alloc_type in
  let v = mk_var x in
  let x_in_alloc = mk_elem(v, all_alloc_objsf) in (* x is in the set of allocated objects *)
  let x_type = mk_elem(v, mk_var (obj_var t)) in (* x is in the set of objects of type t *)
  let x_nonnull = mk_neq(v, mk_null) in (* x ~= null *)
    (smk_and [f; x_in_alloc; x_type; x_nonnull])
 
(* Compute the strongest postcondition of f over (ArrayAlloc aac) *)
let sp_ArrayAlloc (aac : array_alloc_command) (f : form) : form =
  let x = aac.arr_alloc_lhs in
  let t = aac.arr_alloc_type in
  let dims = aac.arr_alloc_dims in
    match dims with
      | d0 :: drest ->
	  let v = mk_var x in
	  let x_in_alloc = mk_elem (v, all_alloc_objsf) in 
	  let x_has_type = mk_elem (v, mk_var (obj_var t)) in 
	  let x_nonnull = mk_neq (v, mk_null) in
	  let array_len = mk_eq ((mk_arrayLength v), d0) in
	    (smk_and [f; x_in_alloc; x_has_type; x_nonnull; array_len])
      | [] -> Util.warn ("LoopInvariantInference: array " ^ x ^ " has no dimensions.\n"); f

(* Compute the strongest postcondition of f over (Havoc hc) *)
let sp_Havoc (hc : havoc_command) (f : form) : form =
  let hr = hc.havoc_regions in
    if (List.length hr = 0) then f (* nothing to do here *)
    else
      let havoc_var (il : ident list) (to_havoc : form) : ident list =
	match to_havoc with
	  | Var x -> x :: il
	  | _ -> Util.warn ("LoopInvariantInference: don't know how to havoc " ^ 
			      (PrintForm.string_of_form to_havoc) ^ "\n"); il
      in
      let old_xs = List.fold_left havoc_var [] hr in (* collect identifiers *)
      let new_xs = List.map (fun (x) -> (increment_id x)) old_xs in (* get fresh names *)
      let new_vs = List.map (fun (x0) -> (mk_var x0)) new_xs in (* make new variables *)
      let renameMap = List.combine old_xs new_vs in
      let f0 = subst renameMap f in (* substitute the new variable for the old in f *)
      let til = List.map (fun (x) -> (x, TypeUniverse)) new_xs in
	smk_exists (til, f0)

(* Find equalities in the formula, and return the list of ident's for
   use with smk_fixand_eq. *)
let rec get_candidates_for_substitution (ids : ident list) (f : form) : ident list =
  match f with
    | Var _ 
    | Const _ -> ids
    | App(Const Eq, [Var v; _])
    | App(Const Eq, [_; Var v]) -> 
	if (not (List.mem v ids)) then
	  v :: ids
	else
	  ids
    | App(f0, fs) ->
	let ids0 = get_candidates_for_substitution ids f0 in
	  List.fold_left get_candidates_for_substitution ids0 fs
    | Binder(_, _, f0)
    | TypedForm(f0, _) ->
	get_candidates_for_substitution ids f0

(* Compute the strongest postcondition for a basic command. Since we
   are only using this for inference, we don't have to check asserts
   when we get to them.
*)
let sp_bc (bc : basic_command) (f : form) : form =
  match bc with
    | Skip
    | Hint _ -> f (* Hint is a special ast for Bohne. *)
    | VarAssign ac -> (sp_VarAssign ac f)
    | Alloc ac -> (sp_Alloc ac f)
    | ArrayAlloc aac -> (sp_ArrayAlloc aac f)
    | Assert {annot_form = af; annot_msg = am}
	(* We don't check asserts, but that's ok for inference. *)
    | NoteThat {annot_form = af; annot_msg = am}
	(* "NoteThat x" desugars into "Assert x; Assume x". Again, assert not checked. *)
    | Assume {annot_form = af; annot_msg = am} -> 
	smk_and [f; (mk_comment am af)]
    | Split {annot_form = af; annot_msg = am} ->
	(* "Split x" desugars into "Assert x; Havoc *; Assume x". Again, assert not checked. *)
	(mk_comment am af)
    | Havoc hc -> (sp_Havoc hc f)
    | ProcCall _ -> failwith "LoopInvariantInference: ProcCall should be desugared.\n"

(* Strongest postcondition with loops unrolled i times. Returns true
   if successful, false if a loop invariant is violated. *)
let sp_unrolled (f : form) (c : command) (i : int) : bool =
  let rec sp_unrolled_rec (f : form) (c : command) : form =
    (*
    print_string ("Strongest postcondition with unrolling of:\n");
    print_string ((PrintForm.string_of_form f) ^ "\n\n");
    print_string ("Over:\n");
    print_string ((PrintAst.pr_command c) ^ "\n\n");
    flush_all ();
    *)
    match c with
      | Basic {bcell_cmd = bc} -> (sp_bc bc f)
      | Seq cl -> (List.fold_left sp_unrolled_rec f cl)
      | Choice cl -> smk_or (List.map (sp_unrolled_rec f) cl)
      | If {if_condition = ic; if_then = it; if_else = ie} ->
	  let tbranch = smk_and [ic; (sp_unrolled_rec f it)] in
	  let fbranch = smk_and [(smk_not ic); (sp_unrolled_rec f ie)] in
	    smk_or [tbranch; fbranch]
      | Loop lc -> 
	  begin
	    match lc.loop_inv with
	      | None -> 
		  se_loop_unroll lc f i
	      | Some loop_inv -> 
		  se_loop_inv lc f loop_inv
	  end
      | Return {return_exp = re} ->
	    match re with
	      | None -> f
	      | Some f0 -> smk_and [f; mk_eq (result_f, f0)]
  and se_loop_unroll (lc : loop_command) (f : form) (j : int) : form =
    print_string ("Executing iteration " ^ (string_of_int j) ^ "\n");
    flush_all ();
    let after_pre = sp_unrolled_rec f lc.loop_prebody in
      if (j = 0) then 
	smk_and [after_pre; (smk_not lc.loop_test)]
      else
	let after_test = smk_and [after_pre; lc.loop_test] in
	let after_post = sp_unrolled_rec after_test lc.loop_postbody in
	  (se_loop_unroll lc after_post (j - 1))
  and se_loop_inv (lc : loop_command) (f : form) (loop_inv : form) : form =
    (*
    print_string ("Handling loop with loop invariant:\n");
    print_string ((PrintForm.string_of_form loop_inv) ^ "\n\n");
    flush_all ();
    *)
    let implies_inv = smk_impl (f, loop_inv) in
      (*
      print_string ("ASSERT BEFORE LOOP:\n");
      print_string ((PrintForm.string_of_form implies_inv) ^ "\n\n");
      flush_all ();
      *)
      if (not (Decider.valid implies_inv)) then
	raise Invariant_violation;
      let after_pre = sp_unrolled_rec loop_inv lc.loop_prebody in
      let after_test = smk_and [after_pre; lc.loop_test] in
      let after_post = sp_unrolled_rec after_test lc.loop_postbody in
      let inductive = smk_impl (after_post, loop_inv) in
	(*
	print_string ("ASSERT INDUCTIVE:\n");
	print_string ((PrintForm.string_of_form inductive) ^ "\n\n");
	flush_all ();
	*)
	if (not (Decider.valid inductive)) then
	  raise Invariant_violation;
	smk_and [after_pre; (smk_not lc.loop_test)] in
    try
      let _ = (sp_unrolled_rec f c) in true
    with Invariant_violation -> false

(* Compute the maximum loop depth by recursive descent. *)
let rec get_loop_depth (c : command) : int =
  match c with
    | Seq cl
    | Choice cl ->
	let get_max_depth (d : int) (c0 : command) : int =
	  let d0 = get_loop_depth c0 in
	    if (d0 > d) then d0 else d
	in
	  (List.fold_left get_max_depth 0 cl)
    | If {if_then = it; if_else = ie} ->
	let it_d = get_loop_depth it in
	let ie_d = get_loop_depth ie in
	  if (it_d > ie_d) then it_d else ie_d
    | Loop lc ->
	let pre_d = get_loop_depth lc.loop_prebody in
	let post_d = get_loop_depth lc.loop_postbody in
	  if (pre_d > post_d) then (pre_d + 1) else (post_d + 1)
    | _ -> 0

(* Since the modified variables of a loop are also the modified
   variables of the outer loops, we want to have a cache. *)
let get_modified_variables (c : command) (cache : (loop_command, ident list) Hashtbl.t) : ident list =
  let rec get_modified_variables_rec (ids : ident list) (c : command) : ident list =
    match c with
      | Basic {bcell_cmd = bc} ->
	  begin
	    match bc with
	      | VarAssign {assign_lhs = id} -> 
		  if (List.mem id ids) then ids else (id :: ids)
	      | _ -> ids
	  end
      | Seq cl
      | Choice cl ->
	  (List.fold_left get_modified_variables_rec ids cl)
      | If {if_then = it; if_else = ie} ->
	  let it_mv = (get_modified_variables_rec ids it) in
	    (get_modified_variables_rec it_mv ie)
      | Loop lc ->
	  begin
	    try (Hashtbl.find cache lc)
	    with Not_found ->
	      let pre_mv = (get_modified_variables_rec ids lc.loop_prebody) in
	      let post_mv = (get_modified_variables_rec ids lc.loop_postbody) in
		(Hashtbl.add cache lc post_mv); post_mv
	  end
      | _ -> ids
  in
    (get_modified_variables_rec [] c)

(* Gather together all the formulas in a given command. *)
let rec find_forms_in_command (c : command) : form list =
  begin
    match c with
      | Basic {bcell_cmd = bc} ->
	  begin
	    match bc with
	      | VarAssign ac -> [ac.assign_rhs]
	      | ArrayAlloc aac -> aac.arr_alloc_dims
	      | Assert afc | NoteThat afc | Assume afc | Split afc
		  -> [afc.annot_form]
	      | Havoc hc -> hc.havoc_regions
	      | ProcCall pc -> pc.callee_args
	      | _ -> []
	  end
      | Seq cl
      | Choice cl -> List.flatten (List.map find_forms_in_command cl)
      | If {if_condition = ic; if_then = it; if_else = ie} ->
	  let it_forms = (find_forms_in_command it) in
	  let ie_forms = (find_forms_in_command ie) in
	    [ic] @ it_forms @ ie_forms
      | Loop lc ->
	  let pre = (find_forms_in_command lc.loop_prebody) in
	  let post = (find_forms_in_command lc.loop_postbody) in
	    pre @ [lc.loop_test] @ post
      | Return {return_exp = re} ->
	  match re with
	    | Some f -> [f]
	    | None -> []
  end

(* Return the list of unique boolean formulas with the given formula, excluding boolean variables. *)
let rec get_unique_boolean_formulas (fl : form list) (f : form) : form list =
  match f with
    | App(Const op, _) when (op = Lt || op = Gt || op = LtEq || op = GtEq) ->
	if (List.mem f fl) then fl else (f :: fl)
    | App(Const op, fl0) ->
	List.fold_left get_unique_boolean_formulas fl fl0
    | TypedForm (f, tf) -> get_unique_boolean_formulas fl f
    | _ -> fl

(* Make a unique list of variable comparisons. *)
let rec make_unique_boolean_formulas (fl : form list) (f : form) : form list =
  fl

let get_loop_variables (lc : loop_command) : ident list =
  let rec get_dependencies (c : command) (ids : ident list) : ident list =
    match c with
      | Basic {bcell_cmd = bc} ->
	  begin
	    match bc with
	      | VarAssign ac -> 
		  let ids0 = List.filter (fun (id0 : ident) -> (not (id0 = ac.assign_lhs))) ids in
		    if ((List.length ids) = (List.length ids0)) then
		      ids
		    else
		      ids0 @ (FormUtil.fv ac.assign_rhs)
	      | _ -> ids
	  end
      | Seq cs -> List.fold_right get_dependencies cs ids
      | If {if_condition = ic; if_then = it; if_else = ie} -> 
	  let it_ids = get_dependencies it ids in
	  let ie_ids = get_dependencies ie ids in
	  let ids0 = it_ids @ (List.filter (fun (id) -> (not (List.mem id it_ids))) ie_ids) in
	    ids0 @ (FormUtil.fv ic)
      | _ -> Util.warn ("\nget_loop_variables did not expect: " ^ (PrintAst.pr_command c) ^ "\n"); ids
  in
    match lc.loop_test with
      | Var id
      | TypedForm (Var id, TypeApp(TypeBool, [])) ->
	  (* Because of the way ast's are constructed, the loop test
	     should always be a boolean variable. This means we need to do
	     some extra work to get at the actual ("working") variables that the loop
	     termination depends on. *)
	  get_dependencies lc.loop_prebody [id]
      | _ -> Util.warn ("\nget_loop_variables did not expect: " ^ 
			  (PrintForm.string_of_form lc.loop_test) ^ "\n"); []
	  
let make_loop_variable_comparisons
    (proc : proc_def) (lc : loop_command) (outer_loops : loop_command list) : form list =
  let num_outer_loops = List.length outer_loops in
  let outermost = if (num_outer_loops < 1) then lc else (List.nth outer_loops (num_outer_loops - 1)) in
  let cache_size = get_loop_depth (Loop outermost) in
  let cache = Hashtbl.create cache_size in
  let modified_variables = get_modified_variables (Loop lc) cache in
  let mod_vars_decls, unmod_vars_decls = 
    List.partition (fun (d) -> List.mem d.vd_name modified_variables) proc.p_locals in
  let rec make_loop_variable_comparisons (comparisons : form list) (f : form) : form list =
    let make_comparisons (id : ident) (ops : constValue list) (d : var_decl) : form list =
      let make_comparison (op : constValue) : form = 
	App(Const op, [(Var id); (Var d.vd_name)]) in
	List.map make_comparison ops
    in
      match f with
	| App(Const op, [(TypedForm ((Var id0), _)); _])
	| App(Const op, [_; (TypedForm ((Var id0), _))])
	| App(Const op, [(Var id0); _])
	| App(Const op, [_; (Var id0)]) when (op = Lt || op = Gt || op = LtEq || op = GtEq) ->
	    print_string ("MATCHED: " ^ (PrintForm.string_of_form f) ^ "\n");
	    begin
	      try
		let decl0 = List.find (fun (d) -> d.vd_name = id0) mod_vars_decls in
		let compare_with = List.filter (fun (d) -> d.vd_type = decl0.vd_type) unmod_vars_decls in
		  print_string ("COMPARE WITH: ");
		  List.iter (fun (x) -> (print_string (x.vd_name ^ " "))) compare_with;
		  print_string ("\n\n");
		  let comparisons0 = List.map (make_comparisons id0 [Lt; Gt; LtEq; GtEq]) compare_with in
		    (List.flatten comparisons0) @ comparisons
	      with Not_found -> comparisons
	    end
	| App(Const op, fl) ->
	    List.fold_left make_loop_variable_comparisons comparisons fl
	| TypedForm (f, tf) -> make_loop_variable_comparisons comparisons f
	| _ -> comparisons
  in
  let is_modified (id : ident) : bool = List.mem id modified_variables in
  let loop_variables = List.filter is_modified (get_loop_variables lc) in
  let outer_loop_variables = List.filter is_modified (List.flatten (List.map get_loop_variables outer_loops)) in
    print_string ("LOOP VARIABLES: ");
    List.iter (fun (id) -> (print_string (id ^ " "))) loop_variables;
    print_string ("\nOUTER LOOP VARIABLES: ");
    List.iter (fun (id) -> (print_string (id ^ " "))) outer_loop_variables;
    print_string ("\nUNMODIFIED VARIABLES: ");
    List.iter (fun (x) -> (print_string (x.vd_name ^ " "))) unmod_vars_decls;
    print_string ("\nMODIFIED VARIABLES: ");
    List.iter (fun (x) -> (print_string (x.vd_name ^ " "))) mod_vars_decls;
    print_string ("\n\n");
    print_string ((PrintForm.string_of_form lc.loop_test) ^ "\n");
    let fs = find_forms_in_command (Loop lc) in
    let fbf = List.fold_left get_unique_boolean_formulas [] fs in      
    let loop_variable_comparisons = List.fold_left make_loop_variable_comparisons [] fs in
      print_string ("FORMS:\n");
      List.iter (fun (x) -> (print_string ("\t" ^ (PrintForm.string_of_form x) ^ "\n"))) fs;
      print_string ("UNIQUE:\n");
      List.iter (fun (x) -> (print_string ("\t" ^ (PrintForm.string_of_form x) ^ "\n"))) fbf;
      print_string ("\nCOMPARISONS:\n");
      List.iter (fun (x) -> (print_string ("\t" ^ (PrintForm.string_of_form x) ^ "\n"))) loop_variable_comparisons;
      loop_variable_comparisons

(* Remove user-annotated loop invariants from the code. *)
let rec remove_loop_invariants (c : command) : unit =
  match c with
    | Seq cl 
    | Choice cl -> List.iter remove_loop_invariants cl
    | If {if_then = it; if_else = ie} ->
	remove_loop_invariants it;
	remove_loop_invariants ie
    | Loop lc -> 
	lc.loop_inv <- None;
	remove_loop_invariants lc.loop_prebody;
	remove_loop_invariants lc.loop_postbody;
    | Basic _
    | Return _ -> ()

(* Returns a topologically-sorted list of the loops in the
   program. Outer loops occur before the loops they enclose. Loops
   that occur earlier in the code will appear earlier in the list.
*)
let rec get_loops (c : command) : command list =
  match c with
    | Seq cl 
    | Choice cl -> 
	List.flatten (List.map get_loops cl)
    | If {if_then = it; if_else = ie} ->
	(get_loops it) @ (get_loops ie)
    | Loop lc ->
	let pre_loops = (get_loops lc.loop_prebody) in
	let post_loops = (get_loops lc.loop_postbody) in
	  (Loop lc) :: (pre_loops @ post_loops)
    | Basic _
    | Return _ -> []

let loop_iterations = 1

(* Check to see if the formula is trivial. *)
let trivial (f : form) : bool =
  (* If all the variables it talks about are old, then it's trivial. *)
  if (List.for_all is_oldname (fv f)) then true
  else match f with
    | App(Const Eq, [Var x; Var y])
    | App(Const Eq, [(TypedForm (Var x, _)); Var y])
    | App(Const Eq, [(TypedForm (Var x, _)); (TypedForm (Var y, _))])
    | App(Const Eq, [Var x; (TypedForm (Var y, _))]) when (x = y) -> true
    | _ -> false

(* Get formulas from program code. *)
let get_code_forms (c : command) : form list =
  let rec get_code_forms_rec (c : command) : form list =
    match c with
      | Basic {bcell_cmd = bc} ->
	  begin
	    match bc with
	      | VarAssign {assign_rhs = f} 
	      | Assert {annot_form = f}
	      | NoteThat {annot_form = f}
	      | Assume {annot_form = f}
	      | Split {annot_form = f} -> [f]
	      | ArrayAlloc {arr_alloc_dims = fs}
	      | Havoc {havoc_regions = fs}
	      | ProcCall {callee_args = fs} -> fs
	      | _ -> []
	  end
      | Seq cl
      | Choice cl ->
	  List.flatten (List.map get_code_forms_rec cl)
      | If {if_condition = ic; if_then = it; if_else = ie}  ->
	  let fit = get_code_forms_rec it in
	  let fie = get_code_forms_rec ie in
	    ic :: (fit @ fie)
      | Loop {loop_prebody = pre; loop_test = test; loop_postbody = post} ->
	  let fpre = get_code_forms_rec pre in
	  let fpost = get_code_forms_rec post in
	    fpre @ (test :: fpost)
      | Return {return_exp = re} ->
	  match re with
	    | None -> []
	    | Some f -> [f] in
    Util.remove_dups (get_code_forms_rec c)
      
let rec is_simple_expr (f : form) : bool =
  match f with
      Const _ 
    | Var _ -> true
    | TypedForm(f0, _) 
    | App(Const Comment, [_; f0]) -> is_simple_expr f0
    | _ -> false

let rec form_comp (f0 : form) (f1 : form) : int =
  let const_comp (c0 : constValue) (c1 : constValue) : int =
    match c0, c1 with
      | IntConst i0, IntConst i1 -> i0 - i1
      | BoolConst b0, BoolConst b1 ->
	  if (b0 = b1) then 0
	  else if (b0) then -1 else 1
      | StringConst s0, StringConst s1 ->
	  String.compare s0 s1
      | _ -> String.compare (string_of_const c0) (string_of_const c1) in
  let binder_comp (b0 : binderKind) (b1 : binderKind) : int =
    let binder_int (b : binderKind) : int =
      match b with
	  Forall -> 0
	| Exists -> 1
	| Comprehension -> 2
	| Lambda -> 3 in
      ((binder_int b0) - (binder_int b1)) in
  let rec til_comp (til0 : typedIdent list) (til1 : typedIdent list) : int =
    match til0, til1 with
	[], [] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | (id0, _) :: tilrest0, (id1, _) :: tilrest1 ->
	  let r0 = String.compare id0 id1 in
	    if (r0 = 0) then
	      til_comp tilrest0 tilrest1
	    else r0 in
    match f0, f1 with
      | App(Const Comment, [_; g0]), App(Const Comment, [_; g1])
      | TypedForm(g0, _), TypedForm(g1, _) -> form_comp g0 g1
      | App(Const Comment, [_; g0]), _
      | TypedForm(g0, _), _ -> form_comp g0 f1
      | _, App(Const Comment, [_; g1])
      | _, TypedForm(g1, _) -> form_comp f0 g1
      |	Const c0, Const c1 -> const_comp c0 c1
      | Const _, _ -> -1
      | _, Const _ -> 1
      | Var id0, Var id1 -> String.compare id0 id1
      | Var _, _ -> -1
      | _, Var _ -> 1
      | App(g0, gs0), App(g1, gs1) ->
	  let r0 = form_comp g0 g1 in
	    if (r0 = 0) then
	      form_comp_list gs0 gs1
	    else r0
      | App(_, _), _ -> -1
      | _, App(_, _) -> 1
      | Binder(b0, til0, g0), Binder(b1, til1, g1) ->
	  let r0 = binder_comp b0 b1 in
	    if (r0 = 0) then
	      let r1 = til_comp til0 til1 in
		if (r1 = 0) then
		  form_comp g0 g1
		else r1
	    else r0
and form_comp_list (fs0 : form list) (fs1 : form list) : int =
  match fs0, fs1 with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | f0 :: frest0, f1 :: frest1 ->
	let r0 = form_comp f0 f1 in
	  if (r0 = 0) then
	    form_comp_list frest0 frest1
	  else r0

let symmetric (c : constValue) : bool =
  match c with
      Eq | MetaEq | Or | And | MetaAnd 
    | Disjoint | Cap | Cup | Seteq | Plus | Mult
	  -> true
    | _ -> false

(* Some basic normalizations to make it easier to identify duplicate
   formulas. Should be applied after remove_comments_and_typedform. *)
let rec normalize (f0 : form) : form =
  match f0 with
      | App(Const op, fs) when (symmetric op) ->
	  let fs0 = List.map normalize fs in
	  let fs1 = List.sort form_comp fs0 in
	    App(Const op, fs1)
      | App(f1, fs) ->
	  App((normalize f1), (List.map normalize fs))
      | Binder(b, til, f1) ->
	  Binder(b, til, (normalize f1))
      | _ -> f0

let eval (op : constValue) (i0 : int) (i1 : int) : form =
  match op with
    | Eq -> Const (BoolConst (i0 = i1))
    | Lt -> Const (BoolConst (i0 < i1))
    | Gt -> Const (BoolConst (i0 > i1))
    | LtEq -> Const (BoolConst (i0 <= i1))
    | GtEq -> Const (BoolConst (i0 >= i1))
    | Plus -> Const (IntConst (i0 + i1))
    | Minus -> Const (IntConst (i0 - i1))
    | Mult -> Const (IntConst (i0 * i1))
    | Div -> Const (IntConst (i0 / i1))
    | _ -> App(Const op, [Const (IntConst i0); Const (IntConst i1)])

(* Should be applied on normalized formulas. *)
let rec simplify (f : form) : form =
  match f with
    | App(Const op, [Const (IntConst x); Const (IntConst y)]) ->
	eval op x y
    | App(Const Minus, [(Var x); (Var y)]) when (x = y) ->
	Const (IntConst 0)
    | App(Const Plus, [Const (IntConst 0); f0])
    | App(Const Minus, [f0; Const (IntConst 0)]) ->
	simplify f0
    | App(Const Lt, [(Var x); (Var y)])
    | App(Const Gt, [(Var x); (Var y)]) when (x = y) ->
	Const (BoolConst false)
    | App(Const Eq, [(Var x); (Var y)])
    | App(Const LtEq, [(Var x); (Var y)])
    | App(Const GtEq, [(Var x); (Var y)]) when (x = y) ->
	Const (BoolConst true)
    | App(Const Mult, [Const (IntConst 1); f0]) ->
	simplify f0
    | App(Const Mult, [Const (IntConst 0); _]) ->
	Const (IntConst 0)
    | App(f0, fs) ->
	App((simplify f0), (List.map simplify fs))
    | Binder(b, til, f0) ->
	Binder(b, til, (simplify f0))
    | _ -> f

let clean_up (f : form) : form =
  simplify (normalize (remove_comments_and_typedform f))

(* Find expressions of the given type in f. *)
let exprs_of_type (tf : typeForm) (f : form) : form list =
  let rec exprs_of_type_rec (tf : typeForm) (el : form list) (f : form) : form list =
      match f with
	| App(Const op, fs) when 
	    ((tf = TypeApp (TypeInt, [])) && 
	       (op = Plus || op = Minus || op = Mult || op = Div)) ->
	    let el0 = if (List.for_all is_simple_expr fs) then  (el @ [f]) else el in
	      List.fold_left (exprs_of_type_rec tf) el0 fs
	| App(Const Eq, [TypedForm(f0, tf0); f1])
	| App(Const Eq, [f1; TypedForm(f0, tf0)]) when (tf0 = tf) ->
	  let el0 = if (is_simple_expr f0) then el else (el @ [f0]) in
	  let el1 = exprs_of_type_rec tf el0 f0 in
	  let el2 = if (is_simple_expr f1) then el1 else (el1 @ [f1]) in
	    exprs_of_type_rec tf el2 f1
	| App(f0, fs) ->
	  let el0 = exprs_of_type_rec tf el f0 in
	    List.fold_left (exprs_of_type_rec tf) el0 fs
	| Binder(_, _, f0) ->
	    exprs_of_type_rec tf el f0
	| _ -> el in
    Util.remove_dups (exprs_of_type_rec tf [] f)

(* Returns true if c is an operator whose arguments are of the same
   type as its result. *)
let ec_preserving_op (c : constValue) : bool =
  match c with
    | MetaEq | MetaAnd | Or | And | Not | Impl | Iff 
    | UMinus | Plus | Minus | Mult | Div | Mod | Old -> true
    | _ -> false

(* Returns true if c is an operator of multiple arguments of the same
   type. *)
let same_ec_args (c : constValue) : bool =
  match c with
    | Eq | MetaEq
    | Or | And | MetaAnd | Impl | MetaImpl | Iff | Disjoint 
    | Lt | Gt | LtEq | GtEq
    | Cap | Cup | Diff 
    | Subseteq | Subset | Seteq
    | Plus | Minus | Mult | Div | Mod -> true
    | _ -> false

let print_form (f : form) : unit =
  print_string ((PrintForm.string_of_form f) ^ "\n")

let print_equiv_classes (ecs : form list list) : unit =
  print_string ("\n\nEQUIVALENT CLASSES:\n\n");
  List.iter (fun (fs) ->
	       print_string ("BEGIN\n");
	       List.iter print_form (List.sort form_comp fs);
	       print_string ("END\n\n")) ecs

(* Find the equivalence class of the given formula. *)
let get_equiv_class (f0 : form) (ecs : form list list) : form list * form list list =
  let ecs0, ecs_rest = List.partition (fun (ec) -> List.mem f0 ec) ecs in
    match ecs0 with
      | [] -> [f0], ecs_rest
      | [ec0] -> ec0, ecs_rest
      | _ -> failwith "There is a bug in equiv_classes.\n"
	  
(* Add f to the given equivalence class. *)
let add_to_equiv_class 
    (f0 : form) 
    (ec : form list) 
    (ecs : form list list) : form list * form list list =
  if (List.mem f0 ec) then 
    ec, ecs (* already in the same equivalence class *)
  else
    let ec0, ecs_rest = get_equiv_class f0 ecs in
      (ec @ ec0), ecs_rest (* merge the two equivalence classes *)

(* Puts f in the given equivalence class and recursively descends f to
   compute more equivalence classes. *)
let rec make_equiv ((ec : form list), (ecs : form list list)) (f : form) : form list * form list list =
  match f with
    | Var _
    | Const _ -> add_to_equiv_class f ec ecs
    | TypedForm(f0, _) 
    | App(Const Comment, [_; f0]) -> 
	make_equiv (ec, ecs) f0
    | App(Const op, fs) when (ec_preserving_op op) ->
	let ec0, ecs0 = add_to_equiv_class f ec ecs in
	  List.fold_left make_equiv (ec0, ecs0) fs
    | App(Const op, f0 :: fs) when (same_ec_args op) ->
	let ec0, ecs0 = add_to_equiv_class f ec ecs in
	let ec1, ecs1 = make_equiv ([], (ec0 :: ecs0)) f0 in
	let ec2, ecs2 = List.fold_left make_equiv (ec1, ecs1) fs in
	  get_equiv_class f (ec2 :: ecs2)
    | App(f0, fs) ->
	let ec0, ecs0 = add_to_equiv_class f ec ecs in
	let ec1, ecs1 = ([], descend (ec0 :: ecs0) fs) in
	  get_equiv_class f (ec1 :: ecs1)
    | Binder(b, til, f0) ->
	let ec0, ecs0 = add_to_equiv_class f ec ecs in
	  make_equiv (ec0, ecs0) f0 
and descend (ecs : form list list) (fs : form list) : form list list =
  match fs with
    | [] -> ecs
    | f0 :: fs0 ->
	let ec0, ecs0 = make_equiv ([], ecs) f0 in
	  descend (ec0 :: ecs0) fs0

(* Compute equivalence classes for the given formula. *)
let compute_equiv (f : form) (ecs : form list list) : form list list =
  let ec0, ecs0 = make_equiv ([], ecs) f in
    ec0 :: ecs0

(* Compute equivalence classes of variables and expressions in c. *)
let make_equiv_classes (c : command) : form list list =
  let rec equiv_classes_rec (ecs : form list list) (c : command) : form list list =
    match c with 
      | Basic {bcell_cmd = bc} ->
	  begin
	    match bc with
	      | VarAssign {assign_lhs = id; assign_rhs = f} ->
		  let ec0, ecs_rest = get_equiv_class (Var id) ecs in
		  let ec1, ecs1 = make_equiv (ec0, ecs_rest) (clean_up f) in
		    ec1 :: ecs1
	      | ArrayAlloc {arr_alloc_dims = fs}
	      | Havoc {havoc_regions = fs}
	      | ProcCall {callee_args = fs} -> descend ecs fs
	      | Assert {annot_form = f}
	      | NoteThat {annot_form = f}
	      | Assume {annot_form = f}
	      | Split {annot_form = f} -> 
		  let ec0, ecs0 = make_equiv ([], ecs) (clean_up f) in
		    ec0 :: ecs0
	      | _ -> ecs
	  end
      | Seq cl 
      | Choice cl ->
	  List.fold_left equiv_classes_rec ecs cl
      | If {if_condition = f; if_then = it; if_else = ie} ->
	  let ecs0 = descend ecs [(clean_up f)] in
	  let ecs1 = equiv_classes_rec ecs0 it in
	    equiv_classes_rec ecs1 ie
      | Loop {loop_prebody = pre; loop_test = f; loop_postbody = post} ->
	  let ecs0 = equiv_classes_rec ecs pre in
	  let ecs1 = descend ecs0 [(clean_up f)] in
	    equiv_classes_rec ecs1 post
      | Return {return_exp = fo} ->
	  match fo with
	    | None -> ecs
	    | Some f -> descend ecs [(clean_up f)] in
    equiv_classes_rec [] c

let print_results (label : string) (fs : form list) : unit =
  print_string ("\n\n" ^ label ^ ":\n");
  List.iter print_form fs;
  print_string ("\n");
  flush_all ()

let rec add_if_not_dup lst elm =
  match lst with
      [] -> [elm]
    | elm0 :: rest ->
	if (elm0 = elm) then lst
	else elm0 :: (add_if_not_dup rest elm)

(* Return the list of constant values in the formula. *)
let get_consts (f : form) : constValue list =
  let rec get_consts_rec (f : form) : constValue list =
    match f with
	Const c ->
	  begin
	    match c with
		IntConst _
	      | BoolConst _
	      | NullConst
	      | StringConst _
	      | EmptysetConst -> [c]
	      | _ -> []
	  end
      | App(f0, fs) ->
	  (get_consts_rec f0) @ (List.flatten (List.map get_consts_rec fs))
      | Binder(_, _, f0)
      | TypedForm(f0, _) ->
	  get_consts_rec f0
      | _ -> [] in
    Util.remove_dups (get_consts_rec f)

type cSubstMap = (constValue * form) list

(* Substitute constant values in the formula according to sm. *)
let subst_const (sm : cSubstMap) (f : form) : form =
  let rec subst_const_rec (f : form) : form =
    match f with
	Const c ->
	  begin
	    try
	      List.assoc c sm
	    with Not_found -> f
	  end
      | App(f0, fs) ->
	  App((subst_const_rec f0), (List.map subst_const_rec fs))
      | Binder(b, til, f0) ->
	  Binder(b, til, (subst_const_rec f0))
      | TypedForm(f0, ty) ->
	  TypedForm((subst_const_rec f0), ty)
      | _ -> f in
    subst_const_rec f

(* For each loop: *)
(* Step 1: Create a set of candidate invariants. *)
(* Step 2: For each invariant, test to see if implied. *)
(* Step 3: Take the conjunction of the candidate invariants that passed Step 3. *)
(* Step 4: Let the result of Step 4 be the loop invariant. *)
(* Step 5: If end of program is reached, run standard vcgen. Otherwise goto Step 1. *)

(* Heuristics for creating candidate invariants. *)

(* TEMPLATES *)
(* 1. Module invariant. *)
(* 2. Procedure precondition. *)
(* 3. Procedure postcondition. *)

(* HEURISTICS *)
(* 4. If inner loop, relate inner and outer loop variables using <, <= ,> and >=. *)
(* 5. Replace one of the bounds in the template with the loop variable. *)

let infer_loop_invariants
    (prog : program)
    (impl : impl_module)
    (proc : proc_def)
    (phdr : proc_header)
    (conc : specvar_def list) (* concretization *) : unit =
  print_string ((PrintAst.pr_command proc.p_body) ^ "\n");
  (* First, remove user-annotated loop invariants, if any. *)
  remove_loop_invariants proc.p_body;
  (* Here we do the work that is common to the entire procedure. *)
  let precond = Sast.concretized_pre prog impl phdr in
  let pre_conjuncts = FormUtil.get_conjuncts precond in
    print_results "PRECOND CONJUNCTS" pre_conjuncts;
  let postcond = Sast.concretized_post prog impl proc phdr in
  let post_conjuncts = FormUtil.get_conjuncts postcond in
    print_results "POSTCOND CONJUNCTS" post_conjuncts;
  let templates = Util.remove_dups (pre_conjuncts @ post_conjuncts) in
  let make_eq_to_old (id : ident) : form =
    mk_eq ((Var id), (Var (FormUtil.oldname id))) in
  let ids_to_old = AstUtil.get_variables_to_old proc.p_body in
  let old_fs = List.map make_eq_to_old ids_to_old in
  let precond_and_old = smk_and (precond :: old_fs) in
    print_results "PRECOND WITH OLD" [precond_and_old];
  let equiv_classes = make_equiv_classes proc.p_body in
  let equiv_classes = compute_equiv (clean_up precond_and_old) equiv_classes in
  let equiv_classes = compute_equiv (clean_up postcond) equiv_classes in
  let contains_var_or_const (fs : form list) : bool =
    List.exists (fun (f) -> match f with | Var _ | Const _ -> true | _ -> false) fs in
  let ecsr = ref (List.filter contains_var_or_const equiv_classes) in
    print_equiv_classes !ecsr;
  let infer (lc : loop_command) (outer_loops : command list) : unit =
      print_string ("\nINFERRING FOR:\n" ^ (PrintAst.pr_command (Loop lc)) ^ "\n\n");
    let try_executing (loop_invariant : form) : bool =
      lc.loop_inv <- Some loop_invariant;
      print_string ("\n\nTRYING: " ^ (PrintForm.string_of_form loop_invariant));
      flush_all ();
      sp_unrolled precond_and_old proc.p_body loop_iterations in
    let templates = List.map clean_up templates in
    let passed, failed = List.partition try_executing templates in
      print_results "PASSED" passed;
      print_results "FAILED" failed;
    let check_candidate (passed, failed) (f : form) : form list * form list =
      let inv = smk_and passed in
	if ((trivial f) || 
	      List.mem f passed || 
	      List.mem f failed || 
	      Decider.valid (smk_impl (inv, f)) ||
	      (not (try_executing f))) then
	  passed, (failed @ [f])
	else
	  (passed @ [f]), failed in
    let simple_replacement (ecs : form list list) (template : form) : form list =
      let make_substMaps (to_rename : ident) : substMap list =
	let exprs = fst (get_equiv_class (Var to_rename) ecs) in
	  List.map (fun (expr) -> [(to_rename, expr)]) exprs in
      let rmsv = List.flatten (List.map make_substMaps (fv template)) in
      let fsv = List.map (fun (rm) -> clean_up (subst rm template)) rmsv in
      let make_cSubstMaps (to_rename : constValue) : cSubstMap list =
	let exprs = fst (get_equiv_class (Const to_rename) ecs) in
	  List.map (fun (expr) -> [(to_rename, expr)]) exprs in
      let rmsc = List.flatten (List.map make_cSubstMaps (get_consts template)) in
      let fsc = List.map (fun (rm) -> clean_up (subst_const rm template)) rmsc in
	fsv @ fsc in
    let sr_candidates = List.flatten (List.map (simple_replacement !ecsr) templates) in
    let unique_cs = Util.remove_dups sr_candidates in
    let new_cs = Util.difference unique_cs (passed @ failed) in
    let sorted_cs = List.sort form_comp new_cs in
    let passed, failed = List.fold_left check_candidate (passed, failed) sorted_cs in
      print_results "SIMPLE REPLACEMENT" passed;
    let smart_replacement (ecs : form list list) (template : form) : form list =
      (* Don't substitute with expressions. This is to limit the depth
	 of resulting formulas. *)
      let make_substMaps (to_rename : ident) : substMap list =
	let exprs = fst (get_equiv_class (Var to_rename) ecs) in
	let exprs = List.filter is_simple_expr exprs in
	  List.map (fun (expr) -> [(to_rename, expr)]) exprs in
      let make_cSubstMaps (to_rename : constValue) : cSubstMap list =
	let exprs = fst (get_equiv_class (Const to_rename) ecs) in
	let exprs = List.filter is_simple_expr exprs in
	  List.map (fun (expr) -> [(to_rename, expr)]) exprs in
      let not_constant (f : form) : bool = 
	match f with Const _ -> false | _ -> true in
      let rmsv = List.flatten (List.map make_substMaps (fv template)) in
      let fsv = List.map (fun (rm) -> clean_up (subst rm template)) rmsv in
      let rmsc = List.flatten (List.map make_cSubstMaps (get_consts template)) in
      let fsc = List.map (fun (rm) -> clean_up (subst_const rm template)) rmsc in
	List.filter not_constant (fsc @ fsv) in
    let iterate_exprs (ecs : form list list) : form list list =
      let rec iterate_expr (processed : form list) (to_process : form list) : form list =
	match to_process with
	    [] -> processed
	  | f :: fs -> 
	      if (is_simple_expr f) then 
		iterate_expr (processed @ [f]) fs
	      else
		iterate_expr (processed @ (f :: (smart_replacement !ecsr f))) fs  in
	List.map (fun (ec) -> Util.remove_dups (iterate_expr [] ec)) ecs in
    let rec iterate_until 
	(n : int)
	(passed : form list)
	(failed : form list) : form list * form list =
      if (n = 0) then
	passed, failed
      else
	let p0, f0 = iterate_until (n - 1) passed failed in
	  ecsr := iterate_exprs !ecsr;
	  print_equiv_classes !ecsr;
	  let candidates = List.flatten (List.map (simple_replacement !ecsr) templates) in
	  let unique_cs = Util.remove_dups candidates in
	  let new_cs = Util.difference unique_cs (p0 @ f0) in
	  let sorted_cs = List.sort form_comp new_cs in
	    if (sorted_cs = []) then
	      p0, f0
	    else
	      let p1, f1 = List.fold_left check_candidate (p0, f0) sorted_cs in
		print_results ("BEFORE CHECKING") sorted_cs;
		print_results ("ITERATION " ^ (string_of_int n)) p1;
		p1, f1 in
    let passed, failed = iterate_until 2 passed failed in
    let result = smk_and passed in
      lc.loop_inv <- Some result;
      print_string ("THE INFERRED LOOP INVARIANT IS:\n");
      print_string ((PrintForm.string_of_form result) ^ "\n");
      flush_all () in
  let rec handle_next_loop (outer_loops : command list) (c : command) : unit =
    match c with
      | Seq cl 
      | Choice cl -> 
	  List.iter (handle_next_loop outer_loops) cl
      | If {if_then = it; if_else = ie} ->
	  handle_next_loop outer_loops it;
	  handle_next_loop outer_loops ie
      | Loop lc ->
	  infer lc outer_loops;
	  handle_next_loop (c :: outer_loops) lc.loop_prebody;
	  handle_next_loop (c :: outer_loops) lc.loop_postbody
      | Basic _
      | Return _ -> () in
    handle_next_loop [] proc.p_body

