(** Transform Ast to normal form by making all assertions
    explicit and desuraging loops and procedure calls *)

open Ast
open AstUtil
open Form
open FormUtil
open Background

let get_new_id_like : (ident -> ident) = 
  let (id_counter : int ref) = ref 0 in
  fun (x : ident) ->
    (id_counter := !id_counter + 1;
     x ^ "_" ^ (Printf.sprintf "%d" !id_counter))

(* ------------------------------------------------------------ *)
(** Modifies clause handling *)
(* ------------------------------------------------------------ *)

(** Compute a set of global variables that give *upper* approximation 
    of the modifies region given by the formula, e.g. 
    x..f is approximated by f *)
let rec mod_upper_bound (f : form) : ident list =
  match (strip_types f) with
    | Var id -> [id]
    | App(Const FieldRead, [Var field;obj]) -> [field]
    | App(Const ArrayRead, _) -> [arrayStateId]
    | TypedForm(f1,t) -> mod_upper_bound f1
    | _ -> (Util.warn ("Vcgen.mod_upper_bound: could not recognize mod item " ^ 
			 PrintForm.string_of_form f);
	    [])

(** Compute a set of global variables that give *lower* approximation 
    of the modifies region given by the formula, 
    e.g. the list [x..f; y] is approximated by y 
    because not all of f is allowed to be modified. *)
let mod_lower_bound (fs0 : form list) : ident list =
  let rec collect (fs : form list) (acc : ident list) : ident list =
    match fs with
      | [] -> acc
      | f::fs1 ->
	  (match f with
	     | Var id -> collect fs1 (id::acc)
	     | TypedForm(fmain,_) -> collect (fmain::fs1) acc
	     | _ -> 
		 debug_lmsg 0 (fun () ->"Threw away mod clause item " ^
			      PrintForm.string_of_form f ^ "\n");
		 collect fs1 acc)
  in
    collect fs0 []

(** split_mod separates modifies clause containing x..f into a list of modified variables f and
    frame condition for x..f 

If \q{f} is a field such that no item of the form \q{f} appears
in modifies clause, but an item of the form \q{e..f} appears
in the modifies clause, then let $\q{e}_1\q{..f}$,
\ldots, $\q{e}_n\q{..f}$ be all such expressions.  As just described,
then \q{f} is removed from the list of variables with full
frame conditions, but a partial frame condition is introduced of
the form:

ALL x::obj. x: old alloc.T & x ~= null &
               x ~= old e1 & ... & x ~= old en &
               old (x..owner) ~= C &
  -->  
    x..f = old (x..f)
*)
type field_mods = (ident * form list) list

let split_mod 
    (prog : program)
    (base_class : string) (** base class of procedure *)
    (fs0 : form list) (** formulas describing modifies clausees *)
    (callee : bool)  (** false = generates caller assumption. true = generates callee assertions *)
    : (ident list (** modified vars *) * form list (** frame condition conjuncts *) )  =

  let callee = callee && !CmdLine.checkHidden in

  let ins (id : ident) (ids : ident list) =
    if List.mem id ids then ids else id::ids in

  let rec mod_ins (field : ident) (obj : form) (fmods : field_mods) =
    match fmods with
      | [] -> [(field,[obj])]
      | (field1,objs1)::fmods1 ->
	  if field1=field then (field1,obj::objs1)::fmods1
	  else (field1,objs1)::mod_ins field obj fmods1 in

  let post_of_fmod (fmod : (ident * form list)) : form =
    let (f,es) = fmod in
    let fvar = mk_var f in
    let xid = "framedObj" in
    let xvar = mk_var xid in
    let xtypename = Util.unqualify_getting_module f in
    let hidden_set = mk_var (AstUtil.c_name base_class Jast.hidden_set_name) in
    let elem = smk_and (
      [mk_elem(xvar,mk_var (oldname all_alloc_objs)); mk_elem(xvar,mk_var (obj_var xtypename))] 
      @	if callee then [mk_not (mk_elem(xvar, hidden_set))] else []
    )     
    in
      
    let mk_diff (e : form) : form = mk_neq(xvar,make_old_and_transform e [xid]) in
    let diff = List.map mk_diff es in
    let notrep = 
      if !CmdLine.tokens then [mk_neq(mk_old_owner_of xvar, mk_class_token base_class)]
      else []
    in
    let lhs = smk_and (notrep @ [elem] @ diff) in
    let rhs = mk_eq(mk_fieldRead fvar xvar,
		    mk_fieldRead (mk_var (oldname f)) xvar) in
    let res = mk_forall(xid,mk_object_type, smk_impl(lhs,rhs)) in
    let _ = debug_lmsg 0 (fun () ->"Field mod post formula: " ^ PrintForm.string_of_form res) in
      res
  in

  let rec collect (fs : form list) (ids : ident list) (fmods : field_mods) =
    match fs with
      | [] -> (ids,fmods)
      | f::fs1 -> 
	  (match f with
	     | Var id -> 
		 collect fs1 (ins id ids) fmods
	     | App(Const FieldRead, [Var field;obj]) ->
		 (debug_lmsg 0 (fun () ->"Modifies reading " ^ field);
		 collect fs1 (ins field ids) (mod_ins field obj fmods))

	     | App(Const ObjLocs, [f]) ->
		 (Util.warn ("Objlocs not supported yet, item " ^ 
				  PrintForm.string_of_form f);
		  collect fs1 ids fmods)
	     | _ -> (Util.warn ("Unsupported modifies clause item " ^ 
				  PrintForm.string_of_form f);
		     collect fs1 ids fmods)) in

(* actuel split_mode body*)
  let (vars,fmods) = collect (List.map strip_types fs0) [] [] in
  let _ = debug_lmsg 0 (fun () ->"Fields in split_mod: " ^ 
			  String.concat ", " (List.map fst fmods)) in
    (vars, List.map post_of_fmod fmods)



(** Compute an upper bound on the set of variables
    modified by the execution of a command. *)
let modified_vars_of (c0 : command) : ident list =
  let ids = ref ([] : ident list) in
  let add_id (id : string) : unit =
    if List.mem id !ids then () 
    else ids := id::!ids in
  let form_collect (f : form) : unit =
    List.iter add_id (mod_upper_bound f) in
  let havoc_collect (fs : form list) : unit = 
    List.iter form_collect fs in
  let b_collect (b : basic_command) : unit = match b with
    | Skip -> ()
    | VarAssign {assign_lhs=id} -> add_id id 
    | Alloc {alloc_lhs=id} -> add_id id
    | ArrayAlloc _ -> () (** no 'add_id arrayStateId', 
			     array alloc does not change array content *)
    | Assert _ -> ()
    | NoteThat _ -> ()
    | Assume _ -> ()
    | Split _ -> ()
    | Havoc {havoc_regions=fs} -> havoc_collect fs
    | ProcCall {callee_hdr=Some {p_contract={co_mod=Some fs}}} -> 
	havoc_collect fs
    | ProcCall {callee_module=m;callee_name=p} ->
	debug_lmsg 0 (fun () ->"Could not find modifies clause for " ^ m ^ "." ^ p)
    | Hint _ -> ()
 in
  let rec collect (c : command) : unit = match c with
    | Basic {bcell_cmd=b} -> b_collect b
    | Seq cs -> List.iter collect cs
    | Choice cs -> List.iter collect cs
    | If {if_then=c1;if_else=c2} -> collect c1; collect c2
    | Loop {loop_prebody=c1;loop_postbody=c2} -> collect c1; collect c2
    | Return _ -> ()
  in
    collect c0;
    !ids

(* ------------------------------------------------------------ *)
(** END of modifies clauses *)
(* ------------------------------------------------------------ *)

(** Conjoin formula with public and private invariants,
    and concretize abstract variables. *)
let conjoin_concretize 
    (prog : program) 
    (im : impl_module)
    (is_public : bool)
    (f : form) = 
  let smname = im.im_name in
  let sm = must_find_sm smname prog in  
  let get_public_inv (sm1 : spec_module) = 
    ListLabels.map ~f:(Specs.good_looking_inv ~msg:("WhileIn_" ^ smname ^ "_OutsidePublicInvOf_" ^ sm1.sm_name)) sm1.sm_invs 
  in
  let private_invariants = 
    if is_public then 
      ListLabels.map ~f:(Specs.good_looking_inv ~msg:(smname ^ "_PrivateInv")) im.im_invs 
    else [] 
  in
  let our_free_invariants =
    ListLabels.map ~f:(Specs.good_looking_inv ~msg:(smname ^ "_FreeInv")) sm.sm_free_invs 
  in
  let relevant_invariants =
    private_invariants @
      our_free_invariants @
      List.concat (List.map get_public_inv prog.p_specs)
  in
    (mk_and (f :: relevant_invariants))

(** precondition of a procedure *)
let concretized_pre 
    (prog : program) 
    (im : impl_module)
    (ph : proc_header) = 
  conjoin_concretize prog im ph.p_public ph.p_contract.co_pre

(** postcondition of a procedure *)
let concretized_post
    (prog : program) 
    (im : impl_module)
    (p : proc_def)
    (ph : proc_header) = 

  (** preservation of values for variables that seem syntactically
      modified but are not declared such *)
  let mk_post_obligation 
      (prog : program) 
      (base_class : string)
      (f : ident) : form = 
    if f = arrayStateId then
      let fvar = mk_var f in
      let xid = "framedObj" in
      let xvar = mk_var xid in
      let iid = "i" in
      let ivar = mk_var iid in
      let xtypename = Util.unqualify_getting_module f in
      let hidden_set = mk_var (AstUtil.c_name base_class Jast.hidden_set_name) in
      let elem = smk_and (
	[mk_elem(xvar, mk_var (oldname all_alloc_objs));
	 mk_elem(xvar,mk_var (oldname (obj_var xtypename)))]
	@ if !CmdLine.checkHidden then [mk_not (mk_elem(xvar, hidden_set))] else []
      ) in
      let notrep = 
	if !CmdLine.tokens then [mk_neq(mk_old_owner_of xvar, mk_class_token base_class)]
	else [] 
      in
      let lhs = smk_and (elem :: notrep) in
      let rhs = mk_eq(mk_arrayRead fvar xvar ivar,
		      mk_arrayRead (mk_var (oldname f)) xvar ivar) in
      let res = mk_forall(xid,mk_object_type,
		  mk_forall(iid,mk_int_type,
			    smk_impl(lhs,rhs))) in
      let _ = debug_lmsg 0 (fun () ->"Field mod post formula: " ^ PrintForm.string_of_form res) in
	res      
    else if AstUtil.is_field f prog then
      let fvar = mk_var f in
      let xid = "framedObj" in
      let xvar = mk_var xid in
      let xtypename = Util.unqualify_getting_module f in
      let elem = mk_and[mk_elem(xvar, mk_var (oldname all_alloc_objs));
			mk_elem(xvar,mk_var (oldname (obj_var xtypename)))] in
      let notrep = 
	if !CmdLine.tokens then [mk_neq(mk_old_owner_of xvar, mk_class_token base_class)]
	else [] 
      in
      let lhs = smk_and (elem::notrep) in
      let rhs = mk_eq(mk_fieldRead fvar xvar,
		      mk_fieldRead (mk_var (oldname f)) xvar) in
      let res = mk_forall(xid,mk_object_type,
			  smk_impl(lhs,rhs)) in
      let _ = debug_lmsg 0 (fun () ->"Field mod post formula: " ^ PrintForm.string_of_form res) in
	res
    else
      mk_eq(mk_var f,mk_var (oldname f))
  in

  let smname = im.im_name in
  let get_name vd = vd.vd_name in
  let names_of_locals = List.map get_name p.p_locals in
  let procedure_mod = ph.p_contract.co_mod in
  let check_modifies () : form list =
    (** remove local variables from a list *)
    let non_locals_of (ids : ident list) : ident list =
      let not_local id = not (List.mem id names_of_locals) in
	List.filter not_local ids
    in
    let modified_vars = 
      non_locals_of (modified_vars_of p.p_body) in
    let _ = Debug.lmsg 4 (fun () ->"Modified variables in body of " ^ 
			smname ^ "." ^ ph.p_name ^ ":\n  " ^
			String.concat ", " modified_vars ^ "\n") in      
    let avars = accessible_specvars prog smname in
    let avar_names = List.map get_name avars in
      (* !! Change to use defined_affected_by? *)
    let deps = rtrancl_support_of_all prog smname avar_names in
    let _ = debug_lmsg 0 (fun () ->"Dependencies:\n" ^ string_of_defdeps deps ^"\n") in
    let ultimately_modified = affected_by_ids deps modified_vars in
    let _ = debug_lmsg 0 (fun () ->"Ultimately modified variables in body of " ^ 
			smname ^ "." ^ ph.p_name ^ ":\n  " ^
			String.concat ", " ultimately_modified ^ "\n") in
    let not_private (id : ident) : bool = not (is_rep_var id im prog) in
    let visible_modified = List.filter not_private ultimately_modified in
    let (declared1,field_post_mod) = match procedure_mod with
      | None -> ([],[])
      | Some fs -> split_mod prog smname fs true in
    let declared = all_alloc_objs :: declared1 in
    let _ = debug_lmsg 0 (fun () ->"Mod clause is: " ^
			String.concat ", " declared ^ "\n") in
    let is_undeclared id = not (List.mem id declared) in
    let undeclared_modified = List.filter is_undeclared visible_modified in
    let _ = debug_lmsg 0 (fun () ->"Undeclared in body of " ^ 
			smname ^ "." ^ ph.p_name ^ ":\n  " ^
			String.concat ", " undeclared_modified ^ "\n") in    
      field_post_mod @ List.map (mk_post_obligation prog smname) undeclared_modified
  in
  let post_mod = check_modifies() in
  conjoin_concretize prog im ph.p_public (smk_and (ph.p_contract.co_post :: post_mod))

let get_callee_hdr (pc : proc_call) : proc_header =
  match pc.callee_hdr with
    | None -> failwith ("vcgen: unresolved call to " ^ 
			  pc.callee_name)
    | Some h -> h 

(** diagnostic *)
let pr_map (m : (ident * form) list) : unit =
  let pr_sub (f1,f2) = 
    print_string (f1 ^ " --> " ^ 
		      PrintForm.string_of_form f2 ^ " ") in
  let _ = Debug.msg "Substitution:\n  " in
    List.iter pr_sub m; print_string "\n"

(** Desugaring procedure calls *)
let desugar_procedure_call
    (prog : program)
    (im : impl_module) (* caller module *)
    (pd : proc_def) (* caller *)
    (pc : proc_call) (* procedure call and callee info *) 
    : command list =
    (* !!! I think this, using split_mod, incorrectly assumes
       that even the fields of owned objects have not
       been modified - it's sound since it's done at both sides, but strange
    *)
  (* Procedure call (but see code for details):

     z := p(v)

     where p(u) has:
       requires pre(x,y,u)
       modifies x
       ensures post(old(x),x,y,u,result)

     becomes:
       assert pre(x,y,v);
       x0 := x;
       havoc x;
       havoc z;
       assume post(x0,x,y,v,z)
  *)
  let hdr = get_callee_hdr pc in
  let callee_sm = must_find_sm pc.callee_module prog in
  let full_callee_name = callee_sm.sm_name ^ "." ^ hdr.p_name in
  let spec = hdr.p_contract in

  let add_callee_invs f = smk_and (f:: (ListLabels.map ~f:Specs.good_looking_inv callee_sm.sm_invs)) in
  let c_pre = add_callee_invs spec.co_pre in
  let c_post1 = add_callee_invs spec.co_post in
  let modspec = match spec.co_mod with
    | None -> (** interpreting no modifies clause as an empty modifies clause *)
	[]
    | Some s -> s in
  let (mods0,field_post) = split_mod prog callee_sm.sm_name modspec false in
  let mods = all_alloc_objs :: mods0 in
    (*
  let _ = print_string "Mods: " in
  let _ = List.iter (fun x -> print_string (x ^ " ")) mods in
  let _ = print_string "\n" in
    *)

  let add_external f = 
    if pc.call_is_external then conjoin_concretize prog im hdr.p_public f
    else f in

  (* u -> v: 
     replacing formal parameters with actual arguments
     used both in pre and post *)

  let formals = List.map (fun x -> x.vd_name) hdr.p_formals in
  let m_u_v1 = 
    try List.combine formals pc.callee_args
    with Invalid_argument s ->
      failwith (s ^ ": Argument mismatch calling " ^ full_callee_name) in
  let old_formals = List.map (fun x -> oldname x.vd_name) hdr.p_formals in
  let m_u_v2 = 
    try List.combine old_formals pc.callee_args
    with Invalid_argument s ->
      failwith (s ^ ": Argument mismatch calling " ^ full_callee_name) in
  let map_u_v = m_u_v1 @ m_u_v2 in

  (* assert precondition *)

  let assert_pre = [mk_assert (add_external (subst map_u_v c_pre))
    (full_callee_name ^ "_Precondition")] in

  (* establish mapping (x0,x) of modified variables *)
    
  let mk_map_x_x0 x = (x, get_new_id_like x) in
  let map_x_x0 = List.map mk_map_x_x0 mods in

  (* x0 := x
     save values of modified variables *)

  let map_to_assign (x,x0) = mk_assign x0 (mk_var x) in
  let assigns_to_save_state = List.map map_to_assign map_x_x0 in
  
  (* havoc x *)

  let havoc_x = [mk_havoc (List.map mk_var mods)] in

  (* havoc z *)

  let havoc_z = 
    match pc.callee_res with
      | None -> []
      | Some z -> [mk_havoc [mk_var z]] in

    (* TODO: replace renamings with assignments? *)

  (* old x -> x0  renaming *)

  let mk_map_oldx_x0 x = 
    try (oldname x, mk_var (List.assoc x map_x_x0))
    with Not_found -> Util.fail "Internal error desugaring procedure call"
  in
  let m_oldx_x0 = List.map mk_map_oldx_x0 mods in
  (* let _ = pr_map m_oldx_x0 in *)

  (* result -> z: result parameter in the post *)

  let map_result_z = 
    match pc.callee_res with
      | None -> []
      | Some z -> [(result_var,mk_var z)] in

  (* assume postcondition *)
    
  let alloc_monotone = mk_subseteq(mk_var (oldname all_alloc_objs), 
				   mk_var all_alloc_objs) in
  let c_post = smk_and (c_post1::alloc_monotone::field_post) in
  let map_oldx_x0 = List.map (fun (x,x0) -> (oldname x, mk_var x0)) map_x_x0 in
  let assume_post = [mk_assume 
    (add_external (subst (map_u_v @ map_oldx_x0 @ map_result_z) c_post))
    (full_callee_name ^ "_Postcondition")] in

  (* final desugaring result for desugar_procedure_call: *)
    assert_pre 
    @ assigns_to_save_state
    @ havoc_x
    @ havoc_z
    @ assume_post

let desugar_proc_def 
    (prog : program)
    (im : impl_module)
    (pd : proc_def) : unit =

  let c_pre = concretized_pre prog im pd.p_header in
  let pre_assume = mk_assume c_pre "ProcedurePrecondition" in
  let c_post = concretized_post prog im pd pd.p_header in
  let post_assert = mk_assert c_post "ProcedureEndPostcondition" in

  let return_end = mk_assume mk_false "ProcedureReturn" in
  let loop_end = mk_assume mk_false "CodeUnreachableAfterLoop" in
  let desugar_return (oexp : form option) : command = 
    match oexp with
      | None -> Seq [post_assert; return_end]
      | Some exp -> Seq [mk_assign result_var exp;
			 post_assert; return_end] in

  let desugar_alloc (x : ident) (t : ident) : command list =
    (* x = new t
      --->
       havoc x;
       assume x ~= null & x ~: alloc_t & x : t & lonely x;
       alloc := alloc Un {x}
    *)
    let xf = mk_var x in
    let x_type = mk_elem(xf,mk_var (obj_var t)) in
    let x_nin_alloc = mk_notelem(xf,all_alloc_objsf) in
    let x_nonnull = mk_neq(xf,mk_null) in
    let alloc_assumption = 
      smk_and [x_nonnull; x_nin_alloc; x_type;
	       get_unalloc_lonely_xid prog t x]
    in
      [mk_havoc [mk_var x];
       mk_assume alloc_assumption "AllocatedObject";
       mk_assign all_alloc_objs 
	 (mk_cup(all_alloc_objsf, mk_singleton xf))]
  in
  let desugar_array_alloc 
      (x : ident) 
      (t : ident) 
      (ds : form list) : command list =
    (* x = new T[d1];
      --->
       havoc x;
       assume x ~= null & x ~: alloc_t & x : Array & x..length=d1 & lonely x;
       assume x .. array.length = s;
       alloc := alloc Un {x}
    *)
    match ds with
      | [] -> Util.warn "vcgen.wp_array_alloc: array with no dimensions"; []
      | d1::ds1 ->
	  let _ = (if ds1 <> [] then 
		     Util.warn "vcgen.wp_array_alloc: multidim array"
		   else ()) in
	  let xf = mk_var x in
	  let x_nonnull = mk_neq(xf,mk_null) in
	  let x_nin_alloc = mk_notelem(xf,all_alloc_objsf) in
	  let x_length = mk_eq(mk_arrayLength xf,d1) in
	  let x_has_array_type = mk_elem(xf,mk_var Jast.array_std_class_name) in
	  let alloc_assumption = 
	    smk_and [x_nonnull; x_nin_alloc; x_has_array_type; 
		     x_length;
		     get_unalloc_lonely_xid prog t x]
	  in
	    [mk_havoc [mk_var x];
	     mk_assume alloc_assumption "AllocatedArrayObject";
	     mk_assign all_alloc_objs 
	       (mk_cup(all_alloc_objsf, mk_singleton xf))]
  in
  let desugar_basic (bc : basic_command) : command list = 
    let same = [mkbasic bc] in
      match bc with
	| Skip -> []
	| VarAssign va -> same
	| Alloc{alloc_lhs=x;alloc_type=t} -> desugar_alloc x t
	| ArrayAlloc{arr_alloc_lhs=lhs;arr_alloc_type=t;arr_alloc_dims=ds} ->
	    desugar_array_alloc lhs t ds
	| Assert _ -> same
	| NoteThat{annot_form=e;annot_msg=m} -> [mk_assert e m; mk_assume e m]
	| Assume _ -> same
	| Split _ -> same
	| Havoc _ -> same
	| ProcCall pc -> desugar_procedure_call prog im pd pc
	| Hint _ -> same
  in
  let rec desugar_loop (lc : loop_command) : command =
    let c1 = desugar lc.loop_prebody in
    let cond = lc.loop_test in
    let c2 = desugar lc.loop_postbody in
    let assume_cond = mk_assume cond "LoopConditionHolds" in
    let assume_ncond = mk_assume (mk_not cond) "LoopConditionFalse" in
    let loop_inv_assert = 
      match lc.loop_inv with
	| None -> []
	| Some inv -> [mk_assert inv "LoopInvariantHoldsDuringUnrolling"] in
    let rec unroll (k : int) : command =
      if (k <= 0) then loop_end
      else smk_cmd_seq
	([c1] @
	 loop_inv_assert @
	 [Choice [assume_ncond;
		  smk_cmd_seq [assume_cond; c2; unroll (k-1)]]])
    in
      if !CmdLine.bounded_loop_unroll then 
	unroll !CmdLine.unroll_factor
      else 
	match lc.loop_inv with
	  | None -> Loop {loop_prebody = c1;
			  loop_inv = None;
			  loop_test = cond;
			  loop_postbody = c2} (* leaving loop in there *)
	  | Some inv -> (* ESC/Java desugaring *)
	      let mod_ids = Util.remove_dups 
		((modified_vars_of c1) @ (modified_vars_of c2)) 
	      in
		smk_cmd_seq
		  [mk_assert inv "LoopInvHoldsInitially";
		   mk_havoc (List.map mk_var mod_ids);
		   mk_assume inv "AssumingLoopInv";
		   c1;
		   Choice [smk_cmd_seq [assume_cond; 
					c2; 
					mk_assert inv "LoopInvPreserved";
					loop_end];
			   assume_ncond]]
  and desugar (c : command) : command =
    match c with
      | Basic{bcell_cmd = bc} -> smk_cmd_seq (desugar_basic bc)
      | Seq cs -> smk_cmd_seq (List.map desugar cs)
      | Choice cs -> Choice (List.map desugar cs)
      | If {if_condition=cond; if_then=c1; if_else=c2} ->
	  let c1d = desugar c1 and c2d = desugar c2 in
	    Choice [Seq [mk_assume cond "TrueBranch"; c1d];
		    Seq [mk_assume (mk_not cond) "FalseBranch"; c2d]]
      | Loop lc -> desugar_loop lc
      | Return ret -> desugar_return ret.return_exp
  in
  let desugared_body_core = desugar pd.p_body in
    (* This would generate too many useless assignments,
       instead we still remember to replace old with non-old versions in vcgen:
      let mk_old_assignment (id : ident) : command =
      mk_assign (oldname id) (mk_var id) in
      let old_equals_current = 
      List.map mk_old_assignment 
      (modified_vars_of desugared_body_core) in
    *)
  let desugared_body = 
    smk_cmd_seq [pre_assume;
		 desugared_body_core; 
		 post_assert]
  in
    pd.p_simple_body <- 
      Some {sb_body = desugared_body};
    pd.p_body <- desugared_body

let desugar_program (p : program) : unit =
  let desugar_impls (im : impl_module) : unit =
    List.iter (desugar_proc_def p im) im.im_procs
  in
    List.iter desugar_impls p.p_impls

let check_desugared_basic (bc : basic_command) : unit =
  match bc with
    | Skip -> ()
    | VarAssign va -> ()
    | Alloc _ -> Util.warn("Alloc not desugared.")
    | ArrayAlloc _ -> Util.warn ("Array alloc not desugared.")
    | Assert _ -> ()
    | NoteThat _ -> Util.warn ("noteThat not desugared.")
    | Assume _ -> ()
    | Split _ -> ()
    | Havoc _ -> ()
    | ProcCall pc -> Util.warn ("Procedure call not desugared.")
    | Hint _ -> ()

let rec check_desugared (c : command) : unit =
  match c with
    | Basic{bcell_cmd=bc} -> check_desugared_basic bc
    | Seq cs -> List.iter check_desugared cs
    | Choice cs -> List.iter check_desugared cs
    | Loop lc -> Debug.msg ("Note: loop was not desugared.")
    | If _ -> Util.warn ("If command not desugared")
    | Return _ -> Util.warn ("Return command not desugared")

let check_desugared_program (p : program) : unit =
  let check_proc (pd : proc_def) : unit =
    match pd.p_simple_body with
      | Some {sb_body=c} -> check_desugared c
      | None -> () in
  let check_impl (im : impl_module) : unit =
    List.iter check_proc im.im_procs
  in
    List.iter check_impl p.p_impls

let ast2sast (p : program) : program =
  desugar_program p;
  check_desugared_program p;
  Util.fail_if_warned("Desugaring of ast failed.");
  p
