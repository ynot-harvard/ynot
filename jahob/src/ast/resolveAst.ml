(** Check and potentially disambiguate (resolve) identifiers in a program,
    represented as {!Ast} tree. *)

open Ast
open AstUtil
open Form
open FormUtil

let pr_opt_form (fo : form option) : string =
match fo with
  | None -> "<None>"
  | Some f -> PrintForm.string_of_form f

(** Resolving identifiers *)

let this_id = "this"
let (this_tv : typedIdent) = (this_id,mk_object_type)

type resolverData = {
  mutable std_idents : typedIdent list;
}
let (resolver_data : resolverData option ref) = ref None

let std_of_string (sf : string) : typedIdent list =
  let dummy_vt = ("standardIdentifier", mk_unit_type) in
  let f = ParseForm.parse_formula sf in
  let get_tydent (f : form) : typedIdent =
    match f with
      | TypedForm(Var v,t) -> (v,t)
      | _ -> (Util.warn "resolveAst.std_of_string: expected a typed identifier";
	      dummy_vt)
  in 
    match f with
      | App(Const Tuple, fs) -> List.map get_tydent fs
      | _ -> (Util.warn "resolveAst.std_of_string: expected a tuple of typed identifiers";
	      [])

let init_resolver() =
  let _ = match !resolver_data with
    | Some _ -> Util.warn "resolveAst.init_resolver: resolver initialized twice"
    | None -> () in
  let fname = Util.lib_name "StdIdents.form" in
  let fstr = Util.string_of_file fname in
    resolver_data := Some {std_idents = std_of_string fstr}

let resolver_add (tv : typedIdent) : unit =
  match !resolver_data with
    | None -> Util.warn "resolveAst.init_resolver: resolver not initialized"
    | Some rd -> 
	(rd.std_idents <- tv::rd.std_idents)

let rec get_typed_var 
    (vds : var_decl list) 
    (id : string) : typedIdent option =
  match vds with
    | [] -> None
    | vd::vds1 -> 
	if vd.vd_name=id then Some (vd.vd_name,vd.vd_type)
	else get_typed_var vds1 id

let get_standard (id : ident) : typedIdent option =
  if id=this_id then 
    Some (this_id,mk_object_type)
  else 
    match !resolver_data with
      | Some {std_idents=ids} -> 
	  (try Some (id, List.assoc id ids) with Not_found -> None)
      | _ -> 
	  (Util.warn ("Standard identifier list not resolved; call resolveAst.init_resolver.");
	   None)

(** Resolve a formula identifier in a formula of module mname with
    variables 'vars' that may be used only exactly as declared, and
    'mod_vars' that may be used unqualified or qualified with mname.  If a
    variable appears in both lists, 'vars' list takes precedence. *)
let resolve_form_ident
    (mname : ident) 
    (vars : var_decl list)
    (mod_vars : var_decl list)
    (id : string) : typedIdent option =  
  let res = match get_standard id with
    | Some vt -> Some vt
    | None -> 
	(match Util.split_by "." id with
	   | [x;y] when x=token_name -> 
	       Some (id,mk_object_type)
	   | _ -> 
	       (match get_typed_var vars id with
		  | Some tv -> Some tv
		  | None ->
		      (let qident = Util.qualify_if_needed mname id in
			 get_typed_var mod_vars qident)))
  in match res with
    | None -> None
    | Some (v,t) -> Some (v,fresh_type_vars t)

(** Resolve the implicit 'this' variable in specifications. *)
let resolve_this (mname : string) 
    (vars : var_decl list) (* variables that might hide parameters *)
    (mod_vars : var_decl list) 
    (f0 : form) : form =
  let _ = Debug.lmsg 3 (fun () -> "resolve_this-BEFORE: " ^ PrintForm.string_of_form f0 ^ "\n") in
  let qualify v = mname ^ "." ^ v in
  let get_name (vd : var_decl) = vd.vd_name in
  let var_names = List.map get_name vars in
  let is_field_var (vd : var_decl) = 
    vd.vd_field && (not (List.mem (Util.unqualify vd.vd_name) var_names)) in
  let field_vars = List.map get_name (List.filter is_field_var mod_vars) in
  let rec walk (notdotted : bool) (f : form) =
    let walk1 = walk true in
      match f with
    | Var v ->
	if notdotted && List.mem (qualify v) field_vars 
	then mk_fieldRead (Var v) (mk_var this_id)
	else (Var v)
    | App(Const FieldRead,[fieldf;objf]) ->
	App(Const FieldRead,[walk false fieldf;walk1 objf])
    | App(Const FieldWrite,[fieldf;objf;valf]) ->
	App(Const FieldWrite,[walk false fieldf;walk1 objf;walk1 valf])
    | Const _ -> f
    | App(f1,fs) -> App(walk1 f1, List.map walk1 fs)
    | Binder(k,vts,f1) -> Binder(k,vts,walk1 f1) (* !!! var capture *)
    | TypedForm(f1,t) -> TypedForm(walk1 f1,t)
  in 
  let res = walk true f0 in
  let _ = Debug.lmsg 3 (fun () -> "resolve_this-AFTER: " ^ PrintForm.string_of_form res ^ "\n\n") in
    res

(** Expand shorthands *)

let rep_shorthand_name = "tokenrep"
let expand_shorthands (current_class : string) (f : form) : form =
  expand_function rep_shorthand_name 
    (fun args -> 
       match args with
	 | [arg] -> mk_eq(mk_owner_of arg,mk_class_token current_class)
	 | _ -> 
	     (Util.warn ("resolveAst: Wrong arguments to 'rep' shorthand, expected 1 argument, but got [" ^ 
			   String.concat ", " (List.map PrintForm.string_of_form args));
	      App(Var rep_shorthand_name, args))
    ) f

let pr_vds msg (vds : var_decl list) : string =
  let pr_vd (vd : var_decl) =  vd.vd_name in
    "\n" ^ msg ^ ": " ^ String.concat ", " (List.map pr_vd vds)

(** Resolve each free variable in a formula using
    {!resolve_form_ident}.  Print 'msg' for the identifiers that cannot be
    resolved using 'vars' and 'mod_vars'.  Also add types to integer
    constants.
    Also expand shorthands.
*)
let resolve_form
    (mname : string) 
    (vars : var_decl list)
    (mod_vars : var_decl list)
    (msg : string)
    (f0 : form) : form =
  let mk_m (v : ident) : (ident * form) =
    match resolve_form_ident mname vars mod_vars v with
      | None -> (Util.warn ("Could not resolve identifier " ^ 
			      v ^ ", " ^ msg);
		 Debug.msg ("resolveAst.resolve_form: \nknown vars:" ^
			      pr_vds "vars" vars ^
			      pr_vds "mod_vars" mod_vars);
		 (v,mk_var v))
      | Some (v0,t0) -> (v,mk_typedform(mk_var v0,t0)) in
  let fvs = fv f0 in
    expand_shorthands mname (type_int_consts (subst (List.map mk_m fvs) f0))

let typecheck msg (f : form) : form =
  if !CmdLine.typecheck && not (TypeReconstruct.well_typed [] f) 
  then Util.warn ("Type error; " ^ msg);
  f

let resolve_form_tch
    (mname : string)
    (vars : var_decl list)
    (mod_vars : var_decl list)
    (msg : string)
    (f0 : form) : form =
  typecheck msg (resolve_form mname vars mod_vars msg f0)

let resolve_form_and_this_tch_notc
    (mname : string) 
    (vars : var_decl list)
    (mod_vars : var_decl list)
    (msg : string)
    (f : form) : form =
  resolve_form mname vars mod_vars msg 
    (resolve_this mname vars mod_vars f)

let resolve_form_and_this_tch
    (mname : string) 
    (vars : var_decl list)
    (mod_vars : var_decl list)
    (msg : string)
    (f : form) : form =
  typecheck msg
    (resolve_form_and_this_tch_notc mname vars mod_vars msg f)

let resolve_vardef
    (mn : string) (* module name *)
    (lhs_vars : var_decl list) (* left-hand sides of var definitions? *)
    (vars : var_decl list) (* vars for rhs *)
    (mod_vars : var_decl list) (* mod_vars for rhs *)
    (locals : var_decl list) (* local variables, if any *)
    ((v,f) : specvar_def) : specvar_def  =
  let v1 = 
    if List.mem v (List.map (fun vd -> vd.vd_name) locals) then v 
    else Util.qualify_if_needed mn v in
  let ovd = find_var v1 (locals @ lhs_vars) in
  let is_field = match ovd with
    | None -> 
	Util.warn ("Defining a non-existing abstract variable " ^ v1);
	false
    | Some vd -> vd.vd_field in
  let add_this_lambda f = 
    if is_field then Binder(Lambda,[this_tv],f)
    else f in
  let msg = "while resolving definition of abstract variable " ^ v1 ^ 
    " in class " ^ mn 
  in
    (v1,add_this_lambda (resolve_form_and_this_tch mn (locals @ vars) mod_vars msg f))

(** Ensure that formula contains no 'old' construct. *)
let check_no_old (msg : string) (f0 : form) : unit =
  if contains_old f0 then Util.warn ("Found construct 'old'; " ^ msg)
  else ()

(** Check whether two list of variable declarations
    have disjoint names *)
let disjoint_vds 
    (vds1 : var_decl list) (vds2 : var_decl list) : bool =
  let get_name (vd : var_decl) : string = vd.vd_name in 
  let ns1 = List.map get_name vds1 in
  let ns2 = List.map get_name vds2 in
    Util.disjoint ns1 ns2

(** Universally quantify over "this" variable. *)
let add_forall_this (classn : string) (f : form) : form =
  if List.mem this_id (fv f) then
    smk_foralls([this_tv],
		smk_impl(mk_and [mk_elem(mk_var this_id, all_alloc_objsf);
				mk_elem(mk_var this_id, mk_var classn)], f))
  else f
(*
  smk_foralls([this_tv],f)
*)

(** Check that claimedby relationship on classes refers to existing
    modules, and has no cycles, so it forms a tree. *)
let check_class_claim (prog : program) : unit =
  let rec check 
      (remaining : impl_module list) 
      (checked : string list) : unit =
    match remaining with
      | [] -> ()
      | im::ims1 -> 
	  let checked1 = check_cycle im [] checked in
	    check ims1 checked1
  and check_cycle 
      (im : impl_module)
      (path : string list)
      (checked : string list) : string list =
    let imn = im.im_name in
      if List.mem imn path then
	(Util.warn 
	   ("Cyclic class claims: " ^ 
	      String.concat " -> " (imn::path));
	 (path @ checked))
      else if List.mem imn checked then (path @ checked)
      else match im.im_owner with
	| None -> imn :: (path @ checked)
	| Some mo -> 
	    match find_im mo prog with
	      | None -> 
		  (Util.warn ("Class " ^ imn ^ 
				" is declared as claimed by an unknown class " ^ mo);
		   path @ checked)
	      | Some im1 -> check_cycle im1 (imn :: path) checked
  in    
    check prog.p_impls []
      

let check_var_status 
    (place : string)
    (decls : var_decl list)
    (defs : specvar_def list) : unit =
  let check (vd : var_decl) : unit =
    if vd.vd_abstract && (not vd.vd_ghost) then
      if List.mem_assoc vd.vd_name defs then ()
	else Util.warn ("Missing definition for non-ghost variable " 
			^ vd.vd_name ^ " in " ^ place)
    else ()
  in
    List.iter check decls

(** Resolve formula identifiers and procedure calls in programs.
    Also transform 'old' construct where appropriate 
    by replacing applications of old with new 
    variables with canonical names.
    
    Typechecks using Isabelle; extracts types of free
    variables for formulas, resolves integer constants
    to int type.
*)
let resolve_program (p : program) : unit =   
  let resolve_body
      (im : impl_module)
      (proc : proc_def) =
    let imn = im.im_name in
    let pn = proc.p_header.p_name in
    let sm = must_find_sm imn p in
    let aspecvars = accessible_specvars p im.im_name in
    let vars = proc.p_locals @ proc.p_header.p_formals @ aspecvars in 
    let mod_vars = sm.sm_spec_vars @ im.im_vars in
    let res_form (f : form) : form =
      let msg = "in the body of procedure " ^ imn ^ "." ^ pn in
	typecheck msg (transform_old 
			 (resolve_form_and_this_tch_notc imn vars mod_vars msg f))
    in
    let ores_form (fo : form option) : form option = match fo with
      | None -> None
      | Some f -> Some (res_form f) in      
    let is_assignable vd = 
      if vd.vd_abstract then false
      else match vd.vd_owner with
	| None -> true
	| Some cn when cn=imn -> true
	| Some _ -> false
    in
    let res_lhs1 (id : ident) : typedIdent =
      match resolve_form_ident imn vars mod_vars id with
	| None -> 
	    (let get_name vd = vd.vd_name in
	      Util.warn ("resolveAst.res_lhs1: Could not resolve lhs '" ^ id ^ 
			   "' of assignment in " ^ imn ^ ".\n");
	     (id,TypeUniverse))
	| Some vt -> vt in
    let resolve_call (pc : proc_call) =
      if imn=pc.callee_module then
	match find_proc pc.callee_name im with
	  | None -> Util.fail ("Could not resolve a call to procedure " ^
				 pc.callee_module ^ "." ^ pc.callee_name)
	  | Some pd -> pc.callee_hdr <- Some pd.p_header
      else 
	match find_sm pc.callee_module p with
	  | None -> Util.fail ("Could not find module " ^ pc.callee_module)
	  | Some sm -> 
	      (match find_proc_header pc.callee_name sm with
		 | None -> Util.fail ("Could not resolve a call to procedure " ^
					pc.callee_module ^ "." ^ pc.callee_name)
		 | Some ph -> pc.callee_hdr <- Some ph) in
    let res_lhs (id : string) = 
      Debug.lmsg 3 (fun () -> "Resolving lhs: " ^ id ^"\n");
      let (resid,t) = res_lhs1 id in
	Debug.lmsg 3 (fun () -> "Resolved as: " ^ resid ^"\n");
	(resid,t) in
    let resolve_bcmd (bc : basic_command) = match bc with
      | Skip -> ()
      | VarAssign ({assign_lhs=x;assign_rhs=e} as c) -> 
	  let (rx,t) = res_lhs x in
	    (c.assign_lhs <- rx;
	     c.assign_tlhs <- (rx,t);
	     c.assign_rhs <- res_form e)
      | Alloc ({alloc_lhs=x;alloc_type=t} as c) -> 
	  (c.alloc_tlhs <- res_lhs x)
      | ArrayAlloc ({arr_alloc_lhs=lhs;arr_alloc_type=t;arr_alloc_dims=ds} as c) ->
	  (c.arr_alloc_tlhs <- res_lhs lhs;
	   c.arr_alloc_dims <- List.map res_form ds)
      | Assert ({annot_form=e;annot_msg=m} as c) -> 
	  (c.annot_form <- res_form e)
      | NoteThat ({annot_form=e;annot_msg=m} as c) -> 
	  (c.annot_form <- res_form e)
      | Assume ({annot_form=e;annot_msg=m} as c) ->
	  (c.annot_form <- res_form e)
      | Split ({annot_form=e;annot_msg=m} as c) -> 
	  (c.annot_form <- res_form e)
      | Havoc{havoc_regions=rs} ->
	  Util.warn ("Not resolving havoc's yet; in " ^ imn ^ "." ^ pn)
      | ProcCall pc -> resolve_call pc
      | Hint (TrackSpecvar sv) ->
	  (let (id,typ) = res_lhs sv.track_var in
	     sv.track_var <- id)
    in
    let rec resolve1 (c : command) = match c with
      | Basic{bcell_cmd = bc} -> resolve_bcmd bc
      | Seq cs -> List.iter resolve1 cs
      | Choice cs -> List.iter resolve1 cs
      | If ({if_condition=cond;if_then=thenc;if_else=elsec} as c) ->
	  (c.if_condition <- res_form cond;
	   resolve1 thenc;
	   resolve1 elsec)
      | Loop ({loop_inv=oinv;loop_prebody=s1;loop_test=cond;loop_postbody=s2} as c) ->
	  (c.loop_inv <- ores_form oinv;
	   (* Util.msg ("Resolved into " ^ pr_opt_form c.loop_inv); *)
	   resolve1 s1;
	   c.loop_test <- res_form cond;
	   resolve1 s2)
      | Return ({return_exp=fo} as c) -> (c.return_exp <- ores_form fo)
    in resolve1 proc.p_body
  in
  let resolve_proc_hdr
      (mname : string)
      (oim : impl_module option) (** None means it's a public method *)
      (ph : proc_header) : unit =
    let aspecvars = accessible_specvars p mname in
    let c = ph.p_contract in
    let params = mk_result_vd ph.p_restype :: ph.p_formals in
    let sm = must_find_sm mname p in
    let (vars,mod_vars) = match oim with
      | None ->
	  (params @ aspecvars,sm.sm_spec_vars)
      | Some im ->
	  (params @ aspecvars,sm.sm_spec_vars @ im.im_vars) in
    let resolve_pre (msg : string) (f : form) : form =
      (check_no_old msg f;
       resolve_form_and_this_tch mname vars mod_vars msg f) in
    let resolve_mod (msg : string) (f : form) : form =
      (check_no_old msg f;
       resolve_form_and_this_tch mname vars mod_vars msg f) in
    let resolve_post (msg : string) (f : form) : form =
      resolve_form_and_this_tch mname vars mod_vars msg f in
    let msg_pre = "in precondition of " ^ mname ^ "." ^ ph.p_name in
    let msg_mod = "in modifies clause of " ^ mname ^ "." ^ ph.p_name in      
    let msg_post = "in postcondition of "  ^ mname ^ "." ^ ph.p_name in
      if not c.co_resolved then begin
	c.co_pre <- resolve_pre msg_pre c.co_pre;
	c.co_mod <- 
	  (match c.co_mod with 
	     | None -> None
	     | Some fs -> Some (List.map (resolve_mod msg_mod) fs));
	c.co_post <- transform_old (resolve_post msg_post c.co_post);
	c.co_resolved <- true
      end else () in
  let resolve_proc_vardefs 
      (im : impl_module)
      (locals : var_decl list)
      (svs : specvar_def list) : specvar_def list =
    let imn = im.im_name in
    let sm = must_find_sm imn p in
    let aspecvars = accessible_specvars p imn in
    let lhs_vars = im.im_vars in
    let vars = aspecvars in
    let mod_vars = im.im_vars @ sm.sm_spec_vars in
    let resolve = resolve_vardef imn lhs_vars vars mod_vars locals
    in
      List.map resolve svs
  in
  let resolve_proc (im : impl_module) (proc : proc_def) =
    let imname = im.im_name in
    let ph = proc.p_header in 
    let pname = imname ^ "." ^ ph.p_name in
      begin
	resolve_proc_hdr imname (Some im) ph;
	(if disjoint_vds ph.p_formals proc.p_locals then ()
	 else Util.warn ("Local variable has same name as a parameter in "
			 ^ pname));
	check_var_status pname proc.p_locals proc.p_vardefs;
	proc.p_vardefs <- resolve_proc_vardefs im (proc.p_locals @ proc.p_header.p_formals) proc.p_vardefs;
	resolve_body im proc
      end
  in
  let resolve_type (t : typeDef) = () in

  let resolve_inv (im : impl_module) (mod_vars : var_decl list) (i : Specs.invariant_desc) : Specs.invariant_desc =
    let imn = im.im_name in
    let aspecvars = accessible_specvars p imn in
    let msg = "in private class invariant " ^ i.Specs.inv_name ^ " of " ^ imn in
      check_no_old msg i.Specs.inv_form ;
      {i with Specs.inv_form = add_forall_this imn (resolve_form_and_this_tch imn aspecvars 
			 mod_vars msg i.Specs.inv_form)}
	
  in
  let resolve_im_constdefs 
      (im : impl_module) 
      (svs : specvar_def list) : specvar_def list =
    let imn = im.im_name in
    let res_def ((v,f) : specvar_def) : specvar_def =
      let v1 = Util.qualify_if_needed imn v in
      let f1 = resolve_form_tch imn [] [] ("constdef " ^ v1 ^ " in class " ^ imn) f in 
	(v1,f1)
    in
      List.map res_def svs
  in
  let resolve_im_vardefs 
      (im : impl_module)
      (sm : spec_module)
      (svs : specvar_def list) : specvar_def list =
    let imn = im.im_name in
    let aspecvars = accessible_specvars p imn in
    let lhs_vars = im.im_vars in
    let vars = aspecvars in
    let mod_vars = im.im_vars @ sm.sm_spec_vars in
    let resolve = resolve_vardef imn lhs_vars vars mod_vars []
    in
      List.map resolve svs
  in
  let resolve_impl (im : impl_module) =
    im.im_constdefs <- resolve_im_constdefs im im.im_constdefs;
    List.iter (resolve_proc im) im.im_procs;
    let imn = im.im_name in
    let sm = must_find_sm imn p in
    let mod_vars = im.im_vars @ sm.sm_spec_vars in
      im.im_invs <- List.map (resolve_inv im mod_vars) im.im_invs;
      im.im_vardefs <- resolve_im_vardefs im sm im.im_vardefs
  in
  let resolve_sm_constdefs 
      (sm : spec_module)
      (svs : specvar_def list) : specvar_def list =
    let smn = sm.sm_name in
    let res_def ((v,f) : specvar_def) : specvar_def =
      let v1 = Util.qualify_if_needed smn v in
      let f1 = resolve_form_tch smn [] [] 
	("constdef " ^ v1 ^ " in class " ^ smn) f in 
	(v1,f1)
    in
      List.map res_def svs
  in
  let resolve_sm_vardefs 
      (sm : spec_module)
      (svs : specvar_def list) : specvar_def list =
    let smn = sm.sm_name in
    let aspecvars = accessible_specvars p smn in
    let lhs_vars = sm.sm_spec_vars in
    let vars = aspecvars in
    let mod_vars = sm.sm_spec_vars in
    let resolve = resolve_vardef smn lhs_vars vars mod_vars []
    in
      List.map resolve svs
  in
  let resolve_sm_inv (sm : spec_module) (i : Specs.invariant_desc) : Specs.invariant_desc =
    let smn = sm.sm_name in
    let aspecvars = accessible_specvars p smn in
    let msg = "in public invariant " ^ i.Specs.inv_name ^ " of " ^ smn in
      check_no_old msg i.Specs.inv_form ;
      {i with Specs.inv_form = add_forall_this smn (resolve_form_and_this_tch smn aspecvars 
			 sm.sm_spec_vars msg i.Specs.inv_form)}
       
  in
    (** separate the invariant between free invariant and cross-module invariants *)
  let classify_invariants (sm : spec_module) (invs : Specs.invariant_desc list) 
      : (Specs.invariant_desc list * Specs.invariant_desc list) =
    let smn = sm.sm_name in
    let get_name vd = vd.vd_name in
    let specvar_names = List.map get_name (specvars_except smn p) in
    let class_names = get_class_names p in
    let is_outside_mutable_var id = 
      List.mem id specvar_names & not (List.mem id class_names)
    in
    let is_outside_mutable_var_not_alloc id = 
      (id <> all_alloc_objs) & is_outside_mutable_var id in
    let is_free_inv_alloc (i : Specs.invariant_desc) : bool =
      not (List.exists is_outside_mutable_var_not_alloc (fv (i.Specs.inv_form))) in
    let is_free_inv (i : Specs.invariant_desc) : bool =
      not (List.exists is_outside_mutable_var (fv (i.Specs.inv_form))) in
    let rec classify invs free crossmod =
      match invs with
	| [] -> (List.rev free, List.rev crossmod)
	| f::invs1 when f.Specs.inv_ensured ->
	    if not (is_free_inv_alloc f) then 
	      Util.msg("Ensured invariant " ^ f.Specs.inv_name ^ 
			 " in module " ^ smn ^ 
			 " is unlikely to be ensurable because it connects variables from different modules.\n");
	    classify invs1 (f::free) crossmod
	| f::invs1 -> 
	    if (is_free_inv f) then
	      Util.msg("Public invariant " ^ f.Specs.inv_name ^ 
			 " in module " ^ smn ^ 
			 " not declared as ensured, but it could be because it involves only variables from this module.\n");
	    classify invs1 free (f::crossmod)
    in
      classify invs [] [] in
  let resolve_spec (sm : spec_module) =
    sm.sm_constdefs <- resolve_sm_constdefs sm sm.sm_constdefs;
    sm.sm_vardefs <- resolve_sm_vardefs sm sm.sm_vardefs;
    List.iter (resolve_proc_hdr sm.sm_name None) sm.sm_proc_specs;
    let res_invs = List.map (resolve_sm_inv sm) sm.sm_invs in
    let (free,crossmod) = classify_invariants sm res_invs in
      (sm.sm_free_invs <- free;
       sm.sm_invs <- crossmod)
  in
  let resolve_map (m : mapping) : unit = 
    let im = m.map_impl in
    let sm = m.map_spec in
    let imn = im.im_name in    
    let smn = sm.sm_name in (* should be smn=imn *)
    let aspecvars = accessible_specvars p imn in
    let _ = check_var_status (smn ^ " spec") sm.sm_spec_vars (sm.sm_vardefs @ m.map_abst) in
    let _ = check_var_status (imn ^ " impl") im.im_vars im.im_vardefs in
    let lhs_vars = sm.sm_spec_vars in
    let vars = aspecvars in
      (** we cannot do anything more precise than aspecvars
	  because variable can depend on any public field
	  of objects in the dynamically changing rep *)
    let mod_vars = im.im_vars @ sm.sm_spec_vars in
    let resolve = resolve_vardef imn lhs_vars vars mod_vars []
    in
      m.map_abst <- List.map resolve m.map_abst
  in
    (* check for definition cycles done on the fly *)
    check_class_claim p;
    List.iter resolve_type p.p_types;
    List.iter resolve_impl p.p_impls;
    Debug.msg "impl resolve completed.\n";
    List.iter resolve_spec p.p_specs;
    Debug.msg "spec resolve completed.\n";
    List.iter resolve_map p.p_maps;
    Debug.msg "Resolve completed.\n"
