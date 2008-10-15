(** Conversion from Jahob formulas to MONA formulas. *)

open Form
open FormUtil
open TypeReconstruct
open TermRewrite
open PrintForm
open MonaForm
open MonaUtil

(* debug messages *)
let debug_msg = Debug.debug_lmsg (Debug.register_debug_module "MonaConvert")


let null_pred = nullConstName
let eq1_pred = "$Eq1"
let eq2_pred = "$Eq2"
let sub_pred = "$Sub"
let union_pred = "$Union"
let inter_pred = "$Inter"
let diff_pred = "$Diff"
let elem_pred = "$Elem"
let nnull rname = rname ^ "_null" 
let nnode rname = rname ^ "_node"
let heap_type = "HEAP" 
let bb_type = "Bb"
let heap = "$Heap" 
let heap_var = mk_var2 heap 
let heap_bbtree = "BbTree" 
let heap_bbroot = "bbroot"
let heap_empty = "Empty" 
let heap_next = "$next" 
let graph_type = "GRAPHTYPE"
let gtype_root rname = rname ^ "_root"   
let univ = "$U" 

let raise_error p msg = Util.fail ("MonaConvert." ^ p ^ ": " ^ msg)

let type_error t = "type error in formula:\n" ^ string_of_form t 
let order_error ty = "found higher-order type:\n" ^ string_of_type ty
let var_order_error v ty = Printf.sprintf "failed to quantify %s which might have higher-order type:\n%s" v (string_of_type ty)
let desugar_error t = "formula should have been desugared:\n" ^ string_of_form t 
let some_error t = "error in formula:\n" ^ string_of_form t 

let convert_form_helper env f =
  (* let _ = print_debug 4 (fun () -> print_string (isabelle_formula f ^ "\n")) in *)
  let raise_error = raise_error "convert_form_helper" in
  let rec convert_term1 env t = 
    match t with
    | Var v -> mk_var1 v
    | Form.Const NullConst -> 
	mk_var1 null_pred 
    | TypedForm (t', _)
    | App (Form.Const Comment, [_; t']) ->
	convert_term1 env t'
    | App (Form.Const _, _) ->
	raise_error (desugar_error t)
    | _ -> raise_error (type_error t)
  in
  let rec convert_term2 env t = 
    match t with
    | TypedForm (t', _)
    | App (Form.Const Comment, [_; t']) ->
	convert_term2 env t'
    | Form.Const EmptysetConst 
    | App (Form.Const EmptysetConst, [])
    | App (TypedForm (Form.Const EmptysetConst, _), [])
    | App (Form.Const FiniteSetConst, [])
    | App (TypedForm (Form.Const FiniteSetConst, _), [])
      -> mk_emptyset
    | App (Form.Const c, ts) 
    | App (TypedForm (Form.Const c, _), ts) ->
	(match (c, ts) with
	| (FiniteSetConst, ts) ->	
	    let ts' = List.map (convert_term1 env) ts in
	    mk_set ts'
 	| _ -> raise_error (desugar_error t))
    | Var v -> mk_var2 v
    | _ -> raise_error (type_error t)
  in
  let rec mk_pred env v ts res_opt =
    let arg_tys, res_ty =
      match get_type v env with
      | TypeFun (arg_tys, res_ty) -> (arg_tys, res_ty)
      |	TypeApp (TypeArray, [arg_ty; res_ty]) -> ([arg_ty], res_ty)
      |	t -> ([], t)
    in 
    let ts, tys = match res_opt with
    | Some t -> 
	(t::List.rev ts, res_ty::List.rev arg_tys)
    | None when res_ty = FormUtil.mk_bool_type -> 
	(List.rev ts, List.rev arg_tys)
    | _ -> print_endline (string_of_type res_ty); raise_error (type_error (mk_var v))
    in
    let es = 
      try List.fold_left2 
	  (fun ts e arg_ty ->
	    (match FormUtil.order_of_type arg_ty with
	    | Some 0 -> let t = convert_form env e in
	      Form t :: ts
	    | Some 1 -> let t = convert_term1 env e in
              Term1 t :: ts
	    | Some 2 -> let t = convert_term2 env e in
	      Term2 t :: ts
	    | _ -> raise_error (order_error arg_ty)))
	  [] ts tys
      with Invalid_argument _ -> raise_error (type_error FormUtil.mk_true)
    in
    Pred (v, es)
  and convert_atom env a =
    match a with
    | Form.Const (BoolConst true) -> mk_true
    | Form.Const (BoolConst false) -> mk_false
    | Var v -> mk_pred env v [] None
    | App (Form.Const c, [t1; t2]) ->
	(match c with
	| Eq -> 
	    (match (unnotate_types 1 t1, 
		    unnotate_types 1 t2) with
	    | (App (Var fld, args), t) 
	    | (t, App (Var fld, args))
     	      -> mk_pred env fld args (Some t)
	    | _ ->
		let t1' = convert_term1 env t1
		and t2' = convert_term1 env t2 in
		mk_eq1 t1' t2')
	| Seteq -> 
	    (match (unnotate_types 1 t1, 
		    unnotate_types 1 t2) with
	    | (App (Form.Const c, [t11; t12]), t2)  
	    | (t2, App (Form.Const c, [t11; t12])) ->
		let pred_name = match c with
		| Cup -> union_pred
		| Cap -> inter_pred
		| Form.Diff -> diff_pred
		| _ -> raise_error (desugar_error f)
		in
		let t11' = convert_term2 env t11
		and t12' = convert_term2 env t12
		and t2' = convert_term2 env t2 in
		Pred (pred_name, [Term2 t11'; Term2 t12'; Term2 t2'])
	    | _ ->
		let t1' = convert_term2 env t1
		and t2' = convert_term2 env t2 in
		mk_eq2 t1' t2')
	| Form.Subseteq -> 
	    let t1' = convert_term2 env t1
	    and t2' = convert_term2 env t2 in
	    mk_sub t1' t2'
	| Form.Elem -> 
	    let t1' = convert_term1 env t1
	    and t2' = convert_term2 env t2 in
            mk_elem t1' t2'
	| Disjoint -> raise_error "disjoint unimplemented"
	| _ -> raise_error (desugar_error a))
    | _ -> raise_error (some_error a)
  and convert_form env f =
    let f = normalize 1 f in
    match f with
    (* Comments *)
    | App (Form.Const Comment, [_; f]) ->
	convert_form env f
    (* Boolean connectives *)
    | App (Form.Const c, fs) ->
	(match c with 
	| Form.Or -> 
	    let fs' = List.map (convert_form env) fs in
	    mk_or fs'
	| Form.And -> 
	    let fs' = List.map (convert_form env) fs in
	    mk_and fs'
	| Form.Not -> (match fs with
	  | [f] -> 
	      let f' = convert_form env f in
	      mk_not f'
	  | _ -> raise_error (type_error f))
	| Form.Impl -> (match fs with
	  | [f1; f2] -> 
	      let f1' = convert_form env f1
	      and f2' = convert_form env f2 in
	      mk_impl f1' f2'
	  | _ -> raise_error (type_error f))
	| Form.Iff -> (match fs with
	  | [f1; f2] -> 
	      let f1' = convert_form env f1
	      and f2' = convert_form env f2 in
	      mk_iff f1' f2'
	  | _ -> raise_error (type_error f))
	| MetaAnd | MetaImpl -> raise_error (desugar_error f)      
	| _ -> convert_atom env f)
    (* Predicates *) 
    | App (Var v, es) ->
	mk_pred env v es None
    (* Quantifiers *)
    | Binder (b, vs, f0) ->
	let env' = vs @ env in
	let f0' = convert_form env' f0 in
	let v0s, v1s, v2s = 
	  List.fold_left 
	    (fun (v0s, v1s, v2s) (v, ty) -> 
	      match FormUtil.order_of_type ty with
	      | Some 0 -> (v::v0s, v1s, v2s)
	      | Some 1 -> (v0s, v::v1s, v2s)
	      | Some 2 -> (v0s, v1s, v::v2s)
	      | _ -> raise_error (var_order_error v ty)) ([], [], []) vs in
	(match b with
	| Forall -> mk_all2 v2s (mk_all1 v1s (mk_all0 v0s f0'))
	| Exists -> mk_ex2 v2s (mk_ex1 v1s (mk_ex0 v0s f0'))
	| Lambda | Comprehension -> raise_error (desugar_error f))
    | TypedForm (f', _) -> convert_form env f'
    | _ -> convert_atom env f
  in
  convert_form env f

let desugar_rtrancl : rewriteRule =
  let mk_rtrancl_pt ty =
    let pred_name = "$p" in
    let pred_type = TypeFun ([ty;ty], FormUtil.mk_bool_type) in
    let rtc = "$S" in
    let rtcvar = FormUtil.mk_var rtc in
    let t1, t2 = (FormUtil.mk_var "$t1", FormUtil.mk_var "$t2") in
    let pred_app = App (FormUtil.mk_var pred_name, [FormUtil.mk_var "$v1"; FormUtil.mk_var "$v2"]) in
    let closed_t1 = 
      FormUtil.mk_and [FormUtil.mk_elem (t1, rtcvar); 
		       FormUtil.mk_foralls 
			 ([("$v1", ty); ("$v2", ty)], 
			  (FormUtil.mk_impl (FormUtil.mk_and [FormUtil.mk_elem (FormUtil.mk_var "$v1", rtcvar); pred_app],
					     FormUtil.mk_elem (FormUtil.mk_var "$v2", rtcvar))))]
    in
    let rtrancl_def = FormUtil.mk_foralls 
	([(rtc, FormUtil.mk_set_type ty)], 
	 FormUtil.mk_impl (closed_t1, FormUtil.mk_elem (t2, rtcvar))) in
    let rtrancl = Form.Binder 
	(Form.Lambda, [(pred_name, pred_type); 
		       ("$t1", ty); 
		       ("$t2", ty)], rtrancl_def)
    in rtrancl
  in
  let r _ _ _ genv env f =
  let arg_type t =
    match type_of_term (env @ genv) t with
    | TypeFun (arg_ty::_, _) -> arg_ty
    | _ -> TypeUniverse
  in
  match normalize 2 f with
  | App (Var v, (p::_ as args)) when v = str_rtrancl -> 
      unlambda (App (mk_rtrancl_pt (arg_type p), args)), []
  | App (App (Var v, (p::_ as args1)), args2) when v = str_rtrancl -> 
      unlambda (App (mk_rtrancl_pt (arg_type p), args1 @ args2)), []
  | _ -> f, []  
  in (r, RewriteAtoms)


let convert_form env0 derived f0 =
  let msg m = debug_msg 0 m in
  let f1 = disambiguate f0 in
  let rewrite_rules =
    [rewrite_comprehensions;
     rewrite_tree;
     desugar_rtrancl;
     rewrite_function_eq;
     rewrite_non_msol_atoms;
     rewrite_FieldRead_FieldWrite;
     rewrite_unnest;
     rewrite_derived_fields derived]
  in
  let _ = msg (fun () -> "MonaConvert: before rewriting:\n" ^ string_of_form (unnotate_all_types f1) ^ "\n") in
  (* eliminate comprehensions, and FieldRead, and FieldWrite, *)
  (* approximate derived fields, and flatten terms *)
  (* let f1, env0 = rewrite true [rewrite_non_msol_atoms;] env0 f1 in *)
  let f2, env1 = rewrite true rewrite_rules env0 (unlambda f1) in
  (* reconstruct types in resulting formula *)
  let f3, _ = reconstruct_types env1 ((* elim_quants *) f2) in
  let _ = msg (fun () -> "MonaConvert: after rewriting:\n" ^ string_of_form (unnotate_all_types f3) ^ "\n") in
  (* drop all non-digastible atoms *)
  let f = convert_form_helper env1 (disambiguate f3) in
  (f, env1)
    

(* finalize formulas: 
 * - restrict domain of quantifiers
 * - convert occurences of null, equality, ... 
 *)


let finalize mode env q1_guard q2_guard f =
  let q1_guard = List.rev_map q1_guard in
  let q2_guard = List.rev_map q2_guard in
  let mk_eq1 t1 t2 = mk_pred eq1_pred [Term1 t1; Term1 t2] in
  let mk_eq2 t1 t2 = mk_pred eq2_pred [Term2 t1; Term2 t2] in
  let mk_union t1 t2 t3 = mk_pred union_pred [Term2 t1; Term2 t2; Term2 t3] in
  let mk_inter t1 t2 t3 = mk_pred inter_pred [Term2 t1; Term2 t2; Term2 t3] in
  let mk_diff t1 t2 t3 = mk_pred diff_pred [Term2 t1; Term2 t2; Term2 t3] in
  let mk_sub t1 t2 = mk_pred sub_pred [Term2 t1; Term2 t2] in
  let rec ag env f =
    let ag_letdef env defs =
      List.rev_map (fun (v, f) -> (v, ag env f)) defs 
    in
    match f with
    | Not f -> Not (ag env f)
    | And fs -> And (List.rev_map (ag env) fs)
    | Or fs -> Or (List.rev_map (ag env) fs)
    | Impl (f1, f2) -> Impl (ag env f1, ag env f2)
    | Iff (f1, f2) -> Iff (ag env f1, ag env f2)
    | Restrict f -> Restrict (ag env f)
    | Prefix0 f -> Prefix0 (ag env f)
    | Pred (p, es) ->
	let fresh_var = FormUtil.fresh_var "$v" in
	let found_null, es' =
	  List.fold_right (fun t (found_null, acc) -> 
	    match t with
	    | Form f -> (found_null, Form (ag env f)::acc)
	    | Term1 (Var1 v) when v = null_pred ->
		(true, Term1 (Var1 fresh_var) :: acc)
	    | Term2 (Set ts) -> 
		let found_null, ts' = List.fold_right (fun t  (fn, ts') ->
		  match t with 
		  | Var1 v when v = null_pred -> (true, Var1 fresh_var :: ts')
		  | _ -> (fn, t :: ts')) ts (found_null, [])
		in (found_null, Term2 (Set ts') :: acc)
	    | _ -> (found_null, t::acc)) es (false, []) 
	in
	let f' = Pred (p, es') 
	in 
	(* convert null to predicate *)
	if found_null then 
	  Quant (Exists1, [], [fresh_var], 
		 And [f'; mk_pred null_pred [Term1 (Var1 fresh_var)]])
	else f' 
    | Export (fname, f) -> mk_export fname (ag env f)
    | Quant (q, us, vs, f') ->
	let env' =  List.map (fun v -> (v, Form.TypeUniverse)) vs @ env in
	(match q with
	| Exists1 -> Quant (q, us, vs, mk_and (ag env' f'::q1_guard vs))
	| Exists2 -> Quant (q, us, vs, mk_and (ag env' f'::q2_guard vs))
	| Forall1 -> Quant (q, us, vs, mk_impl (mk_and (q1_guard vs)) (ag env' f'))
	| Forall2 -> Quant (q, us, vs, mk_impl (mk_and (q2_guard vs)) (ag env' f'))
	| _ -> Quant (q, us, vs, ag env' f'))
    | Let0 (defs, f') -> 
	let env' = List.map (fun (v, _) -> (v, Form.TypeUniverse)) defs @ env in
	Let0 (ag_letdef env defs, ag env' f')
    | Let1 (defs, f') ->
	let env' = List.map (fun (v, _) -> (v, Form.TypeUniverse)) defs @ env in
	Let1 (ag_letdef env defs, ag env' f')
    | Let2 (defs, f') -> 
	let env' = List.map (fun (v, _) -> (v, Form.TypeUniverse)) defs @ env in
	Let2 (ag_letdef env defs, ag env' f')
    | Atom (Eq1 (Var1 v, t)) when v = null_pred -> mk_pred null_pred [Term1 t]
    | Atom (Eq1 (t, Var1 v)) when v = null_pred -> mk_pred null_pred [Term1 t]
    | Atom (Eq1 (t1, t2)) -> mk_eq1 t1 t2
    | Atom (Eq2 (Union (t1, t2), t3)) 
    | Atom (Eq2 (t3, Union (t1, t2))) -> mk_union t1 t2 t3
    | Atom (Eq2 (Inter (t1, t2), t3))
    | Atom (Eq2 (t3, Inter (t1, t2))) -> mk_inter t1 t2 t3
    | Atom (Eq2 (Diff (t1, t2), t3))
    | Atom (Eq2 (t3, Diff (t1, t2))) -> mk_diff t1 t2 t3
    | Atom (Eq2 (t1, t2)) -> mk_eq2 t1 t2
    | Atom (Neq1 (Var1 v, t)) when v = null_pred -> Not (mk_pred null_pred [Term1 t])
    | Atom (Neq1 (t, Var1 v)) when v = null_pred -> Not (mk_pred null_pred [Term1 t])
    | Atom (Neq1 (t1, t2)) -> Not (mk_eq1 t1 t2)
    | Atom (Neq2 (t3, Union (t1, t2))) -> mk_not (mk_union t1 t2 t3)
    | Atom (Neq2 (Inter (t1, t2), t3))
    | Atom (Neq2 (t3, Inter (t1, t2))) -> mk_not (mk_inter t1 t2 t3)
    | Atom (Neq2 (Diff (t1, t2), t3))
    | Atom (Neq2 (t3, Diff (t1, t2))) -> mk_not (mk_diff t1 t2 t3)
    | Atom (Neq2 (t1, t2)) -> Not (mk_eq2 t1 t2)
    | Atom (Sub (t1, t2)) -> mk_sub t1 t2
    | Atom (Elem (Var1 v, t)) when v = null_pred -> 
       mk_ex1 ["$v"] (mk_and [mk_pred null_pred [Term1 (Var1 "$v")]; mk_elem (Var1 "$v") t])
    | Atom (Elem (t1, t2)) -> mk_pred elem_pred [Term1 t1; Term2 t2]
    | Atom (Nelem (Var1 v, t)) when v = null_pred -> 
	mk_all1 ["$v"] (mk_impl (mk_pred null_pred [Term1 (Var1 "$v")]) (mk_nelem (Var1 "$v") t))
    | Atom (Nelem (t1, t2)) -> Not (mk_pred elem_pred [Term1 t1; Term2 t2])
    
    | _ -> f
  in
  ag env f

(** Convert environment to MONA declarations *)

let convert_env mk_sometype q1_guard q2_guard mode env derived vars =
  let us = match mode with | Ws2s -> [univ] | _ -> [] in
  let used_vars = Hashtbl.create 0 in
  let add_used_vars f = 
    List.iter (fun x -> Hashtbl.replace used_vars x ()) (FormUtil.fv f)
  in  
  let _ = List.iter (fun x -> Hashtbl.replace used_vars x ()) vars in
  let is_used_var = Hashtbl.mem used_vars in
  let mk_null v = mk_pred null_pred [Term1 v] in
  let convert env f = 
    let mf, env' = convert_form env [] f in
    finalize mode env' q1_guard q2_guard mf
  in
  let process_env_decl decls ((x, t), f_opt) =
    if is_used_var x then
      let var1_def rname = 
	match mode with
	| Ws2s -> 
	    let x_type = 
	      if rname = "" then mk_sometype (mk_var1 x) 
	      else mk_type (mk_var1 x) rname 
	    in
	    mk_and [mk_elem (mk_var1 x) heap_var; x_type]
	| _ -> mk_true
      in
      let var2_def rname = 
	match mode with 
	| Ws2s ->
	    let x_type = 
	      if rname = "" then
		mk_all1 ["$v"] (mk_impl (mk_elem (mk_var1 "$v") (mk_var2 x)) (mk_sometype (mk_var1 "$v")))
	      else mk_all1 ["$v"] (mk_impl (mk_elem (mk_var1 "$v") (mk_var2 x)) (mk_type (mk_var1 "$v") rname))
	    in
	    mk_and [mk_sub (mk_var2 x) heap_var; x_type]
	| _ -> mk_true
      in
      match normalize_type t with
      (* set of objects *)
      | TypeApp (TypeSet, [TypeApp (TypeObject, [])]) ->
	  let f_opt' = match f_opt with
	  |  Some f -> 
	      let _ = add_used_vars f in
	      Some (mk_and [var2_def ""; convert env f])
	  | _ -> Some (var2_def "") in
	  VarDecl2 (us, [(x, f_opt')])::decls
      (* reference *)
      | TypeApp (TypeObject, []) ->
	  let f_opt' = match f_opt with
	  |  Some f -> 
	      let _ = add_used_vars f in
	      Some (mk_and [var1_def ""; convert env f])
	  | _ -> Some (var1_def "") in
	  VarDecl1 (us, [(x, f_opt')])::decls
      (* Boolean variable *)
      | TypeApp (TypeBool, []) ->
	  VarDecl0 [x]::decls
      (* pointer-valued field *) 
      |	TypeFun ([(TypeApp (TypeObject, []))], (TypeApp (TypeObject, []))) 
      | TypeApp (TypeArray, [TypeApp (TypeObject, []); TypeApp (TypeObject, [])])
	->
	  (match f_opt with
	  (* non-derived field *)
	  | None ->
	      let v1 = "v1"
	      and v2 = "v2" in
	      let decl = match mode with
	      |	Ws2s ->
		  mk_or [mk_and [mk_null (mk_var1 v1); mk_null (mk_var1 v2)];
			 mk_and [mk_sometype (mk_var1 v1); mk_sometype (mk_var1 v2);
				 mk_elem (mk_var1 v1) heap_var; mk_elem (mk_var1 v2) heap_var;
				 mk_pred eq1_pred [Term1 (mk_var1 v2); 
						   Term1 (mk_succ (mk_var1 v1) bb_type (nnode bb_type) x)]]]
	      |	_ ->
		  finalize mode env q1_guard q2_guard (
		  mk_or [mk_and [mk_null (mk_var1 v1); mk_null (mk_var1 v2)];
			 mk_and [mk_not (mk_null (mk_var1 v1)); mk_eq1 (mk_plus (mk_var1 v1) 1) (mk_var1 v2)]])
	      in PredDecl (x, [VarPar1 [(v1, None);(v2, None)]], decl)::decls
	  (* derived field *)
	  | Some (Binder (Forall, [(v1, _); (v2, _)], App (Form.Const Form.Impl, [_; fdef])) as f) ->
	      let decl = 
		mk_and [mk_impl (mk_null (mk_var1 v1)) (mk_null (mk_var1 v2));
			convert ((v1, FormUtil.mk_object_type)::(v2, FormUtil.mk_object_type)::env) fdef] 
	      in
	      let _ = add_used_vars f in
	      PredDecl (x, [VarPar1 [(v1, None); (v2, None)]], decl)::decls
	  | Some f -> raise_error "convert_env" ("MonaConvert: unsupported field constraint for field " ^ x ^ ":\n" ^ string_of_form f))
      (* Boolean field *) 
      |	TypeFun ([TypeApp (TypeObject, [])], TypeApp (TypeBool, []))
      |	TypeApp (TypeArray, [TypeApp (TypeObject, []); TypeApp (TypeBool, [])]) ->
	  let v1 = "v1"
	  and xset = "$$" ^ x in
	  (match mode with 
	  | Ws2s ->
	      VarDecl2 (us, [(xset, Some (mk_sub (mk_var2 xset) heap_var))])::
	      PredDecl (x, [VarPar1 [(v1, None)]], 
			mk_and [mk_sometype (mk_var1 v1); mk_not (mk_null (mk_var1 v1)); 
				mk_elem (mk_var1 v1) (mk_var2 xset)])::decls
	  | _ -> VarDecl2 (us, [(xset, None)])::
	      PredDecl (x, [VarPar1 [(v1, None)]], 
			mk_elem (mk_var1 v1) (mk_var2 xset))::decls)
      | _ -> decls 
    else decls
  in
  let mona_env = List.map (fun vt ->
    try (vt, List.assoc vt derived) with Not_found -> (vt, None)) env in
  let res = (List.fold_left process_env_decl [] mona_env) in
  res


(** Convert Jahob formula to MONA formula and generate all auxiliary declarations *)

let convert env0 derived fields f =
  let derived_names = List.map (fun ((fld, _), _) -> fld) derived in
  let mk_null v = mk_pred null_pred [Term1 (mk_var1 v)] in
  let mona_form0, env = convert_form (List.map fst derived @ env0) derived_names f in
  let convert_ws2s rname fields =
    let mk_sometype v = mk_type v rname in
    let q1_guard v = mk_and [mk_sometype (mk_var1 v); mk_elem (mk_var1 v) heap_var] in
    let q2_guard v = mk_sub (mk_var2 v) heap_var in
    let mk_type_decl rname fields =
      let fields' = List.map (fun f -> (f, bb_type)) fields in
      TypeDecl (rname, [(nnull rname, []); (nnode rname, fields')])
    in
    let process_record (rname, fields) 
	(gtroots, nulls, type_decls) =
      let type_decl = mk_type_decl rname fields in
      ((String.uppercase (gtype_root rname), [(gtype_root rname, rname)])::gtroots,
       mk_variant (mk_var1 "v") heap rname (nnull rname)::nulls,
       type_decl::type_decls)
    in
    let types, null_def, type_decls = 
      process_record (rname, fields) ([], [], []) in
    let bb_decls = match types with
    | [(_, [(_, ty)])] -> 
	[TypeDecl (heap_type, [(heap_empty, []);
			       (heap_bbtree, [(heap_bbroot, ty); (heap_next, heap_type)])])]
    | _ -> [TypeDecl (graph_type, types);
	    TypeDecl (heap_type, [(heap_empty, []);
				  (heap_bbtree, [(heap_bbroot, graph_type); (heap_next, heap_type)])])] 
    in
    let univs_decl = Universe [(univ, Some (UnivTree heap_type))] in
    let tree_decl = TreeDecl ([univ], [(heap, Some (mk_eq1 (mk_treeroot heap_var) (mk_root1 (Some univ))))]) in
    let null_decl = PredDecl (null_pred, [VarPar1 [("v", None)]], mk_and [mk_elem (mk_var1 "v") heap_var; mk_or null_def]) in
    (Ws2s, type_decls @ bb_decls @ [univs_decl; tree_decl; null_decl], mk_sometype, q1_guard, q2_guard)
  in
  let convert_ws1s rname fld =
    let mk_sometype v = mk_true in
    let q1_guard v = mk_true in
    let q2_guard v = mk_true in 
    let null_set = "$NullSet" in
    let null_set_decl = 
      VarDecl2 ([], 
		[(null_set, Some (mk_ex1 ["v"] (mk_and [mk_elem (mk_var1 "v") (mk_var2 null_set);
							mk_all1 ["v'"] (mk_not (mk_eq1 (mk_var1 "v'") (mk_plus (mk_var1 "v") 1)))])))]) in
    let null_decl =  PredDecl (null_pred, [VarPar1 [("v", None)]], mk_elem (mk_var1 "v") (mk_var2 null_set)) in
    (M2l_str, [null_set_decl; null_decl], mk_sometype, q1_guard, q2_guard)
  in
  let mode, decls, mk_sometype, q1_guard, q2_guard = 
    match fields with
    | [field] -> convert_ws1s bb_type field 
    | _ -> convert_ws2s bb_type fields
  in
  let mona_form = finalize mode env q1_guard q2_guard mona_form0 in 
  let v1 = "v1"
  and v2 = "v2"
  and s1 = "S1"
  and s2 = "S2"
  and s3 = "S3" in
  let vv1 = mk_var1 v1 
  and vv2 = mk_var1 v2 in
  let vs1 = mk_var2 s1 
  and vs2 = mk_var2 s2 
  and vs3 = mk_var2 s3 in
  let eq1_decl = 
    PredDecl (eq1_pred, [VarPar1 [(v1, None);(v2, None)]], 
	      mk_or [mk_eq1 vv1 vv2; 
		     mk_and [mk_null v1; mk_null v2]])
  and elem_decl = PredDecl (elem_pred, [VarPar1 [(v1, None)]; VarPar2 [("S", None)]],
			    mk_ex1 [v2] (mk_and [mk_elem vv2 (mk_var2 "S");
						 mk_pred eq1_pred [Term1 vv1; Term1 vv2]]))   
  and sub_decl = 
    PredDecl (sub_pred, [VarPar2 [(s1, None); (s2, None)]],
	      mk_all1 [v1] (mk_impl (mk_pred elem_pred [Term1 vv1; Term2 vs1])
			   (mk_pred elem_pred [Term1 vv1; Term2 vs2])))
  and eq2_decl = 
    PredDecl (eq2_pred, [VarPar2 [(s1, None);(s2, None)]], 
	      mk_and [mk_pred sub_pred [Term2 vs1; Term2 vs2];
		      mk_pred sub_pred [Term2 vs2; Term2 vs1]])
  and union_decl =
    PredDecl (union_pred, [VarPar2 [(s1, None); (s2, None); (s3, None)]],
	      mk_all1 [v1] (mk_iff (mk_or [mk_pred elem_pred [Term1 vv1; Term2 vs1];
					   mk_pred elem_pred [Term1 vv1; Term2 vs2]])
			      (mk_pred elem_pred [Term1 vv1; Term2 vs3])))
  and inter_decl =
    PredDecl (inter_pred, [VarPar2 [(s1, None); (s2, None); (s3, None)]],
	      mk_all1 [v1] (mk_iff (mk_and [mk_pred elem_pred [Term1 vv1; Term2 vs1];
					    mk_pred elem_pred [Term1 vv1; Term2 vs2]])
			      (mk_pred elem_pred [Term1 vv1; Term2 vs3])))
  and diff_decl =
    PredDecl (diff_pred, [VarPar2 [(s1, None); (s2, None); (s3, None)]],
	      mk_all1 [v1] (mk_iff (mk_and [mk_not (mk_pred elem_pred [Term1 vv1; Term2 vs2]);
					    mk_pred elem_pred [Term1 vv1; Term2 vs1]])
			      (mk_pred elem_pred [Term1 vv1; Term2 vs3])))
  and env_decls = convert_env mk_sometype q1_guard q2_guard mode env derived (fv mona_form0) in
  (mode, decls @ eq1_decl :: elem_decl :: sub_decl :: eq2_decl :: union_decl :: inter_decl :: diff_decl
		 ::  env_decls, mona_form)


