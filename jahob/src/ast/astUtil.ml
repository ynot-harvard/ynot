(** Utility functions: searching {!Ast}. *)

open Ast
open Form
open FormUtil

let arrayVd = {
  vd_name = arrayStateId;
  vd_type = 
    mk_field_type (mk_array mk_object_type);
  vd_init = None;
  vd_abstract = false;
  vd_def = None;
  vd_field = true;
  vd_ghost = true;
  vd_owner = None;
}


let mkbasic_pp (pp : program_point) (c : basic_command) 
    : command = 
  Basic {
    bcell_cmd = c;
    bcell_point = pp;
    bcell_known_before = [];
    bcell_known_after = [];
  }

let dummy_program_point : program_point = {
  pp_file = "";
  pp_line = 0;
  pp_class = "";
  pp_proc = "";
  pp_id = 0;
}

let pp_counter : int ref = ref 0
let fresh_program_point () =
  pp_counter := !pp_counter + 1;
  { dummy_program_point with pp_id = !pp_counter}


let mkbasic (c : basic_command) : command = 
  mkbasic_pp (fresh_program_point ()) c

(** Make sequence of commands while flattening *)
let smk_cmd_seq (cs : command list) : command =
  let rec mk (cs : command list) : command list =
    match cs with
      | (Seq cs2)::cs1 -> mk (cs2 @ cs1)
      | c::cs1 -> 
	  (match c with 
	     | Basic{bcell_cmd=Assume {annot_form=f}} 
		 when (f = mk_false) -> [c]  (* chop rest asfter 'assume false' *)
	     | _ -> c::mk cs1)
      | [] -> []
  in
    Seq (mk cs)

let mk_assert f msg = mkbasic (Assert {
				 annot_form = f;
				 annot_msg = msg
			       })

let mk_assume f msg = mkbasic (Assume {
				 annot_form = f;
				 annot_msg = msg
			       })
let mk_assign lhs res = mkbasic (VarAssign {
				   assign_lhs = lhs;
				   assign_tlhs = (lhs,TypeUniverse);
				   assign_rhs = res
				 })

let mk_havoc (fs : form list) : command =
  mkbasic (Havoc {havoc_regions=fs})

let c_name (base : string) (v : string) = base ^ "." ^ v

let find_im (imn : string) (p : program) : impl_module option =
  let rec search ims = match ims with
    | [] -> None
    | im::ims1 -> if im.im_name = imn then Some im else search ims1
  in search p.p_impls

let must_find_im imn p = match find_im imn p with
  | None -> Util.fail ("Could not find impl module " ^ imn)
  | Some im -> im

let find_sm (smn : string) (p : program) : spec_module option =
  let rec search ims = match ims with
    | [] -> None
    | sm::sms1 -> if sm.sm_name = smn then Some sm else search sms1
  in search p.p_specs

let must_find_sm smn p = match find_sm smn p with
  | None -> 
      (Util.warn ("Could not find spec module " ^ smn ^ " returning Object");
      match (find_sm "object" p) with
	| None -> Util.fail ("Util.must_find_sm no 'Object', we are doomed")
	| Some sm1 -> sm1)
  | Some sm -> sm

let find_proc (pn : string) (im : impl_module) : proc_def option =
  let rec search ps = match ps with
    | [] -> None
    | p::ps1 -> if p.p_header.p_name = pn then Some p else search ps1 
  in search im.im_procs

let find_lemma (ln : string) (im : impl_module) : form option =
  let rec search ls = match ls with
    | [] -> None
    | (ln0,f)::ls1 -> if ln0 = ln then Some f else search ls1
  in search im.im_lemmas

let find_proc_header (pn : string) (sm : spec_module) : proc_header option =
  let rec search phs = match phs with
    | [] -> None
    | ph::phs1 -> if ph.p_name = pn then Some ph else search phs1 
  in search sm.sm_proc_specs

let rec find_var (vname : string) (vds : var_decl list) : var_decl option =
  match vds with
    | [] -> None
    | vd::vds1 -> 
	if vd.vd_name = vname then Some vd
	else find_var vname vds1

(** Other utility functions. *)

(* Apply abstraction function to variables in a formula.   
NOT USED
let map_formula
    (impl_vars : ident list)
    (spec_vars : ident list)
    (m : specvar_def list)
    (f : form) : form =
  let rec apply_map 
      (is_old : bool) 
      (m : (ident * form) list) 
      (v : ident) 
      (f : form) : form = 
    match m with
      | [] -> Debug.msg("The abstract variable " ^ v ^ 
			" is not defined in given refinement.\n"); f
      | (v1,f1)::m1 ->
	  if v1=v then
	    let sub = if is_old then 
	      [(oldname v, oldify true (fv f1) f1)]
	    else [(v1,f1)] 
	    in
	      subst sub f
	  else apply_map is_old m1 v f in
  let rec check_var (v : ident) (f : form) : form =
    let is_old = is_oldname v in
    let uv = if is_old then unoldname v else v in
    if List.mem uv impl_vars then f
    else if List.mem uv spec_vars then
      apply_map is_old m uv f
    else (Debug.msg("Could not map unknown variable " ^ v ^ ".\n"); f) in
  let fvs = fv f in
    List.fold_right check_var fvs f
*)

let mk_result_vd (t : typeForm) : var_decl = {
  vd_name = result_var;
  vd_type = t;
  vd_init = None;
  vd_abstract = false;
  vd_def = None;
  vd_field = false;
  vd_ghost = true;
  vd_owner = None;
}

(** The list of specification variables from all modules except {!smname}. *)
let specvars_except (smname : string) (prog : program) : var_decl list =
  let get_vars (sm : spec_module) = 
    if sm.sm_name=smname then [] else sm.sm_spec_vars in
  List.concat (List.map get_vars prog.p_specs)

(** Convert variable definition into a specvar. *)
let vd_of_specvar 
    (is_field : bool)
    (is_abstract : bool) ((id,f) : specvar_def) : var_decl = {
  vd_name = id;
  vd_type = TypeUniverse;
  vd_init = None;
  vd_abstract = is_abstract;
  vd_def = None; (** real value is determined later *)
  vd_field = is_field;
  vd_ghost = false;
  vd_owner = None; (** should not be used *)
}


(** Get specvars accessible to a given module in the program.
    Those include:
    - specvars of mn
    - specvars directly claimed by mn
*** specvars of modules with same owner as mn
    - specvars of modules not claimed by any module *)
let accessible_specvars (p : program) (mn : string) : var_decl list =
  let get_specvars (sm : spec_module) = 
    let res() = (List.map (vd_of_specvar false true) sm.sm_constdefs) 
                 @ sm.sm_spec_vars in
      match find_im sm.sm_name p with
	| None -> res()
	| Some im ->
	    (match im.im_owner with
	       | None -> res()
	       | Some mn1 when mn1=mn -> res()
	       | _ -> [])
  in
    List.concat (List.map get_specvars p.p_specs)

let deps_lookup 
    (vd : var_decl)
    (vdefs : specvar_def list) : ident list option =
  try 
    let def = List.assoc vd.vd_name vdefs in
      Some (fv def)
  with Not_found -> None

(** Compute the set of variable names on which a given variable
    directly (non-transitively) depends, from the viewpoint of given
    module. *)
let support_of 
    (p : program)
    (mname : string)
    (varid : ident) : ident list =
  let check_abst (vd : var_decl) (im : impl_module) : ident list =
    let rec check (maps : mapping list) (acc : ident list) : ident list =
      match maps with
	| [] -> acc
	| map::maps1 ->
	    if map.map_impl = im then
	      (match deps_lookup vd map.map_abst with
		 | Some ids -> check maps1 (List.rev_append ids acc)
		 | None -> check maps1 acc)
	    else check maps1 acc
    in
      check p.p_maps []
  in
    match Util.split_by "." varid with
      | [m;v] ->
	  if m=mname then
	    (* it can be implementation or specification variable *)
	  let sm = must_find_sm mname p in
	  let im = must_find_im mname p in    
	    match find_var varid im.im_vars with
	      | Some vd -> 
		  (match deps_lookup vd im.im_vardefs with
		     | Some ids -> ids
		     | None -> [])
	      | None ->
		  (match find_var varid sm.sm_spec_vars with
		     | Some vd ->
			 (match deps_lookup vd sm.sm_vardefs with
			    | Some ids -> ids
			    | None -> check_abst vd im)
		     | None -> [])
	else
	  (* because it is outside mname,
	     varid is required to be public variable *)
	  let sm = must_find_sm m p in
	    (match find_var varid sm.sm_spec_vars with
	       | Some vd -> 
		   (match deps_lookup vd sm.sm_vardefs with
		     | Some ids -> ids
		     | None -> [])
	       | None -> [])
    | _ -> []

(** Reflextive transitive closure of support_of *)
let rtrancl_support_of 
    (p : program)
    (mname : string)
    (varid : ident) : ident list =
  let rec closures (ids : ident list) =
    List.concat (List.map closure1 ids)
  and closure1 (id : ident) : ident list =
    match closure id with
      | [] -> [id]
      | ids -> ids
  and closure (id : ident) : ident list =
    closures (support_of p mname id) 
  in
    closure1 varid

(** Dependency relation *)
type def_deps = (ident * ident list) list

let string_of_defdeps (deps : def_deps) : string =
  let pr (v,ids) = v ^ "<-" ^ String.concat "," ids in
    "[" ^ String.concat "; " (List.map pr deps) ^ "]"

let rtrancl_support_of_all
    (p : program)
    (mname : string)
    (varids : ident list) : def_deps =
  let is_dotted (id : ident) : bool = 
    match Util.split_by "." id with
      | [m;v] -> true
      | _ -> false
  in
  let mk_dep (v : ident) = 
    (v, 
     List.filter is_dotted (rtrancl_support_of p mname v)) in
    List.map mk_dep varids

(** Inverse of support.  Takes precomputed dependency relation as argument. *)
let affected_by
    (deps : def_deps)
    (id : ident) : ident list =
  let rec collect 
      (deps : def_deps) 
      (acc : ident list) : ident list =
    match deps with
      | [] -> acc
      | (v,dependants)::deps1 -> 
	  if List.mem id dependants then 
	    collect deps1 (v::acc)
	  else
	    collect deps1 acc
  in
    Util.remove_dups (collect deps [])

(** Version of affected_by that accumulates dependencies of a list of variables. *)
let affected_by_ids
    (deps : def_deps)
    (ids : ident list) : ident list =
  Util.remove_dups 
    (List.concat (ids::(List.map (affected_by deps) ids)))

(** Check whether varid is a representation variable 
    for module im in the program prog. *)
let is_rep_var
    (varid : ident)
    (im : impl_module)
    (prog : program) : bool =
  let imn = im.im_name in
  match Util.split_by "." varid with
    | [m;v] ->
	if m=imn then
	  (* it should be implementation variable *)
	  (match find_var varid im.im_vars with
	     | Some vd -> true
	     | None -> false)
	else
	  (* because it is outside mname,
	     varid is required to be public variable *)
	  let sm = must_find_sm m prog in
	  let im1 = must_find_im m prog in
	    (match find_var varid sm.sm_spec_vars with
	       | Some vd -> 
		   (vd.vd_owner = Some imn) ||
                     (im1.im_owner = Some imn)
	       | None -> false)
	
    | _ -> false


(** Get all variables in module sm that are directly
    claimed by module im *)
let pub_mod_vars_claimed_by
    (im : impl_module) (* module that claims *)
    (sm : spec_module) (* module where we take variables from *)
    : var_decl list =
  let is_claimed (vd : var_decl) : bool =
    match vd.vd_owner with
      | Some mn when mn=im.im_name -> true
      | _ -> false
  in
    List.filter is_claimed sm.sm_spec_vars

(** Get all variables in program that are directly
    claimed by module im *)
let pub_prog_vars_claimed_by
    (im : impl_module)
    (prog : program) : var_decl list =
  List.concat (List.map (pub_mod_vars_claimed_by im) prog.p_specs)

(** Get specification modules of modules claimed by im *)
let modules_claimed_by
    (im : impl_module)
    (prog : program) : spec_module list =
  let imn = im.im_name in
  let rec collect 
      (ims : impl_module list) 
      (acc : spec_module list) : spec_module list =
    match ims with
      | [] -> acc
      | im0::ims1 ->
	  (match im0.im_owner with
	     | Some mn when mn=imn  -> 
		 collect ims1 (must_find_sm im0.im_name prog::acc)
	     | _ -> collect ims1 acc)
  in
    collect prog.p_impls []

(** Get variables that are not claimed from the list of
    variables of a given specification module *)
let get_unclaimed_vars
    (sm : spec_module) : var_decl list =
  let unclaimed (vd : var_decl) = 
    match vd.vd_owner with
      | None -> true
      | _ -> false
  in
    List.filter unclaimed sm.sm_spec_vars

(* Concise display of variable declaration list *)
let pr_vds (vds : var_decl list) =
  let get_name vd = vd.vd_name in
    String.concat ", " (List.map get_name vds)


(** Return a list of declarations of representation
    variables for a module in program, consisting of:

  - private variables of im
  - public variables of modules claimed by im that 
    are not claimed as variables by any module
  - public variables claimed by im
 *)
let get_rep_vars
    (im : impl_module)
    (prog : program) : var_decl list =
  im.im_vars @ pub_prog_vars_claimed_by im prog @ 
    List.concat (List.map get_unclaimed_vars (modules_claimed_by im prog))

let global_var_type (id : ident) (prog : program) : typeForm =
  match Util.split_by "." id with
    | [mname;var] -> 
	let sm = must_find_sm mname prog in
	  (match find_var var sm.sm_spec_vars with
	    | None -> 
		(Util.warn ("astUtil.global_var_type: Could not find " 
				 ^ var ^ " in " ^ mname ^ ", returning unit");
		 mk_unit_type)
	    | Some vd -> vd.vd_type)
    | _ -> 
	(Util.warn ("astUtil.global_var_type: '" ^ id ^ 
		      " is not a qualified variable, returning unit");
	 mk_unit_type)

(** Get the source of a reference or primitive CONCRETE field *)
let field_source (field : ident) (prog : program) : ident =
  let rec find (fds : field_def list) : ident =
    match fds with
      | [] -> (Util.warn ("astUtil.field_source: could not find field " ^ field);
	       "unknownField")
      | fd::fds1 ->
	  if fd.field_name = field then fd.field_from
	  else find fds1
  in
    find (prog.p_ref_fields @ prog.p_prim_fields)

let mk_owner_of (obj : form) : form =
  mk_fieldRead owner_field obj

let mk_old_owner_of (obj : form) : form =
  mk_fieldRead old_owner_field obj

let mk_class_token_name (cln : string) : ident =
  token_name ^ "." ^ cln

let mk_class_token (cln : string) : form =
  mk_var (mk_class_token_name cln)

let no_owner_token = mk_class_token no_owner_name

let is_field (id : string) (p : program) : bool =
  match Util.split_by "." id with
    | [mname;var] -> 
	(match find_sm mname p with
	   | Some sm -> 
	       (match find_var id sm.sm_spec_vars with
		  | Some vd -> vd.vd_field
		  | None -> 
		      (match find_im mname p with
			 | Some im -> 
			     (match find_var id im.im_vars with
				| Some vd -> vd.vd_field
				| None -> false)
			 | None -> false))
	   | None -> false)
    | _ -> false

(*

(** variable dependencies for derived variables *)
type var_deps = {
  vdep_dep : (ident * ident list) list; 
  (** for each var, list of vars it ultimately depends on;
      the domain and range are disjoint;
      if associated list is empty, the var is a constant *)
  vdep_affects : (ident * ident list) list;
  (** inverse of vdep_dep: for each var, which variables depend on it *)
}


(** Compute all (abstract) variables which depend on a given set of
    variables *)

let support
    (id : ident) 
    (vds : (ident * form) list) : ident list =
  try fv (List.assoc id vds)
  with Not_found -> []

let trans_support
    (id : ident)
    (vds : (ident * form) list) : ident list =

let trans_affected_by
    (ids : ident list)
    (vds : (ident * form) list) : ident list =
*)

let mk_track_specvar (id : ident) =
  Hint (TrackSpecvar {track_var=id})

let get_class_names (prog : program) : ident list =
  let get_class_name (sm : spec_module) : ident = sm.sm_name 
  in
    List.map get_class_name prog.p_specs

(* Returns the list of variables that are modified or used but not
   allocated in c. If c is the entire procedure, then for any variable
   x in the list, x = old(x) at the beginning of the procedure. *)
let get_variables_to_old (c : command) : ident list =
  let rec get_variables_to_old_rec (c : command) (ids : ident list) : ident list =
    (* ids may contain duplicates *)
    match c with
      | Basic {bcell_cmd = bc} ->
	  begin
	    match bc with
	      | VarAssign {assign_lhs = id} -> id :: ids
	      | Alloc {alloc_lhs = id}
	      | ArrayAlloc {arr_alloc_lhs = id} ->
		  List.filter (fun (x) -> (not (x = id))) ids
	      | ProcCall {callee_res = ido} ->
		  begin
		    match ido with
		      | None -> ids
		      | Some id -> id :: ids
		  end
	      | _ -> ids
	  end
      | Seq cl -> (List.fold_right get_variables_to_old_rec cl ids)
      | Choice cl -> 
	  List.flatten (List.map (fun (x) -> (get_variables_to_old_rec x ids)) cl)
      | If {if_then = it; if_else = ie} ->
	  let it_ids = get_variables_to_old_rec it ids in
	  let ie_ids = get_variables_to_old_rec ie ids in
	    (it_ids @ ie_ids)
      | Loop {loop_prebody = pre; loop_postbody = post} ->
	  let post_ids = get_variables_to_old_rec post ids in
	    get_variables_to_old_rec pre post_ids
      | _ -> ids in
    Util.remove_dups (get_variables_to_old_rec c [])


(* Returns the list of all variables in c. *)
let get_all_variables_by_type (c : command) : typedIdent list =
  let rec get_all_variables_rec (tids : typedIdent list) (c : command) : typedIdent list =
    let not_declared (id : ident) : bool =
      not (List.exists (fun (id0, tf) -> id = id0) tids) in
    let check_declared (ids : ident list) : unit =
      let not_declared_ids = List.filter not_declared ids in
	if (not (not_declared_ids = [])) then
	  begin
	    print_string ("WARNING: The following variables are not declared.\n");
	    List.iter (fun (id) -> print_string (id ^ " ")) not_declared_ids;
	    print_string ("\n")
	  end; in
    (* ids may contain duplicates *)
      match c with
	| Basic {bcell_cmd = bc} ->
	    begin
	      match bc with
		| VarAssign {assign_tlhs = tid; assign_rhs = f} ->
		    check_declared (FormUtil.fv f);
		    tids @ [tid]
		| Alloc {alloc_tlhs = tid} -> 
		    tids @ [tid]
		| ArrayAlloc {arr_alloc_tlhs = tid; arr_alloc_dims = fs} ->
		    let f_ids = List.flatten (List.map FormUtil.fv fs) in
		      check_declared f_ids;
		      tids @ [tid]
		| ProcCall {callee_res = ido; callee_args = fs; callee_hdr = hdro} ->
		    let f_ids = List.flatten (List.map FormUtil.fv fs) in
		      check_declared f_ids;
		      begin
			match ido with
			  | None -> tids
			  | Some id -> 
			      match hdro with
				| None ->
				    print_string ("WARNING: Missing callee header.\n"); tids
				| Some hdr ->
				    (id, hdr.p_restype) :: tids
		      end
		| _ -> tids
	    end
	| Seq cl -> (List.fold_left get_all_variables_rec tids cl)
	| Choice cl -> 
	    List.flatten (List.map (fun (x) -> (get_all_variables_rec tids x)) cl)
	| If {if_condition = ic; if_then = it; if_else = ie} ->
	    check_declared (FormUtil.fv ic);
	    let it_tids = get_all_variables_rec tids it in
	    let ie_tids = get_all_variables_rec tids ie in
	      (it_tids @ ie_tids)
	| Loop {loop_prebody = pre; loop_test = test; loop_postbody = post} ->
	    check_declared (FormUtil.fv test);
	    let pre_tids = get_all_variables_rec tids pre in
	      get_all_variables_rec pre_tids post
	| Return {return_exp = re} ->
	    match re with
	      | None -> tids
	      | Some f -> check_declared (FormUtil.fv f); tids in
    Util.remove_dups (get_all_variables_rec [] c)
