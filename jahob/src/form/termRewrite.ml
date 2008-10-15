open Util
open Form
open FormUtil
open PrintForm
open TypeReconstruct

(** Variable declaration with optional defining formulas *)
type decl = typedIdent * form option



(** Replace map for common subterm replacements *)
type replaceMap = typedIdent FormHashtbl.t

(** Extended variable declaration for auxiliary variables. 
   The second component is applied to the replace map and the
   result conjoined with the defining formula 
   (used for field constraint analysis) *)
type extDecl = decl * (replaceMap -> form)

(** Scope of auxiliary quantified variables that are introduced during rewriting *)
type binderScope = 
  | Outermost (** bind auxiliary variable in the outermost scope wrt. to its defining formula *)
  | Innermost (** bind auxiliary variable innermost in the scope where the rewrite rule is applied *)

(** Auxiliary quantified variables introduced during rewriting *)
type auxDecl = form * bool * binderKind * binderScope * extDecl

(** Rewrite functions *)
type rewriteFun = 
    (bool -> typeEnv -> form -> form * auxDecl list) ->
    replaceMap -> bool -> typeEnv -> typeEnv -> form -> form * auxDecl list

(** Kinds of rewrite rules *)
type rewriteKind =
  | RewriteTerms (** rewrite terms within atomic formulas *)
  | RewriteAtoms (** rewrite atomic formulas *) 

(** Rewrite rules *)
type rewriteRule = rewriteFun * rewriteKind

let some_error f = "failure in rewriting of formula:\n" ^ string_of_form f
let msome_error msg f = "TermRewrite." ^ msg ^ ": failure in rewriting of formula:\n" ^ string_of_form f
let merror proc msg f = "TermRewrite." ^ proc ^ ": " ^ msg ^ ":\n" ^ string_of_form f

let get_type x env =
  try Util.find_map (fun (x', ty) -> if x = x' then Some ty else None) env
  with Not_found -> TypeUniverse


let type_of_term env t = 
  let ty = match t with
  | TypedForm(_, ty) -> ty
  | Var v -> get_type v env
  | _ -> TypeReconstruct.get_type env t
  in normalize_type ty

(** Constructs an extended variable declaration with a defining formula 
   that does not depend on the state of the replace map *)
let mk_const_decl (v : typedIdent) (decl_opt : form option) : extDecl =
  ((v, decl_opt), fun _ -> mk_true)

(** Constructors for auxiliary variables *)

let mk_inner_exists pol t edecl = 
  (t, pol, Exists, Innermost, edecl)
let mk_inner_forall pol t edecl = 
  (t, pol, Forall, Innermost, edecl)
let mk_outer_exists pol t edecl = 
  (t, pol, (if pol then Exists else Forall), Outermost, edecl)
let mk_outer_forall pol t edecl = 
  (t, pol, (if pol then Forall else Exists), Outermost, edecl)

(** [rewrite pol rewrite_rules genv f] successively applies a list of rewrite rules to formula [f]. 

   Parameters:
   [pol] polarity of the formula. The polarity determines the quantification of auxiliary variables.
   [rewrite_rules] the list of applied rewrite rules.
   [genv] the global environment which must contain  all free variables occuring in [f].
   [f] the formula to be rewritten

   Return value:
   The return value is the rewrittin formula and its new global environment. The new global environment is the 
   original environment extended with outermost bound auxiliary variables. 
   If [pol] is true these auxiliary variables are implicitly universally quantified, otherwise existentially.
 *)
let rewrite (pol : bool) (rewrite_rules : rewriteRule list) (genv : typeEnv) (f0 : form) :
    form * typeEnv =
  let replace_map = FormHashtbl.create 0 in
  let is_bound v env = List.exists (fun (v', _) -> v = v') env in 
  let bind pol (aux_vars : auxDecl list) f env =
    let f' =
      List.fold_left (fun f' (t, pol', b, bs, ((vt, decl_opt), decl_constr)) ->
	let mk_binder, mk_decl = match b, pol, pol'  with
	| Exists, true, true | Exists, false, false | Forall, true, false | Forall, false, true ->
	    smk_exists, fun (f1, f2) -> 
	      (match f1 with 
	      |	App (Const Or, f1s) -> 
		  smk_or (List.rev_map (fun f -> smk_and [f2; f]) f1s)
	      |	_ -> smk_and [f1; f2])
	| Forall, true, true | Forall, false, false | Exists, true, false | Exists, false, true  ->
	    smk_foralls, smk_impl
	| Lambda, _, _ -> (fun (vs, f) ->
	    match f with
	    | Binder (Lambda, vs', f') -> Binder (Lambda, vs @ vs', f')
	    | _ -> Binder (Lambda, vs, f)), 
	    (fun (f1, f2) -> smk_and [f1; f2])
	| b, _, _ -> (fun (vs, f) -> Binder (b, vs, f)), (fun (f1, f2) -> smk_and [f1; f2])
	in
    	let _ = 
	  try if FormHashtbl.find replace_map t = vt then 
	    FormHashtbl.remove replace_map t 
	  with Not_found -> ()
	in
	mk_binder ([vt], mk_decl (smk_and ([safe_unsome mk_true decl_opt;decl_constr replace_map]), f'))) f aux_vars
    in
    let env' = List.filter (fun tv -> not (List.exists (fun (_, _, _, _, ((tv',_), _)) -> tv = tv') aux_vars)) env in
    (f', env')
  in
  let extend_genv (aux_vars : auxDecl list) =
    let genv', defs, aux_vars' = List.fold_left 
	(fun (genv', defs, aux_vars') 
	    ((t, pol', b, k, ((vt, decl_opt), decl_constr)) as aux_var)  ->
	      match (b, pol, pol') with
	      | (Exists, false, false) | (Forall, true, true) 
	      |	(Forall, false, true) | (Exists, true, false) -> 
   		  FormHashtbl.remove replace_map t;
		  let def = smk_and [safe_unsome mk_true decl_opt; decl_constr replace_map] in
		  (vt::genv', def::defs, aux_vars')
	      | _ -> (genv', defs, aux_var::aux_vars')) 
	([], [], []) aux_vars
    in (List.rev_append genv' genv, defs, aux_vars')
  in
  let rec rewrite rewrite_rules pol env f =
  match rewrite_rules with
  | [] -> (f, [])
  | (r_cb, k)::rewrite_rules' ->
      let apply_to_terms = match k with RewriteTerms -> true | _ -> false in
      let r = r_cb (rewrite rewrite_rules) replace_map in
      let rewrite' = rewrite rewrite_rules' in 
      let bind_inner pol (aux_vars : auxDecl list list) f env =
	let outer_aux, inner_aux = 
	  List.partition (function (_, _, _, Outermost, _) -> true | _ -> false)
	    (List.concat aux_vars) 
	in
	let f', env' = bind pol inner_aux f env in
	let f'', aux_vars = rewrite' pol env' f' in
	(f'', aux_vars @ outer_aux)
      in
      let bind_outer pol b bvs (aux_vars : auxDecl list) f env =
	let contains t vs = List.exists (fun (x, _) -> 
	  List.mem x (fv t) && not (is_bound x genv)) vs
	in
	let _, new_bound, aux_vars' = 
	  List.fold_right (fun ((_, _, _, _, ((v, decl_opt), _)) as auxv) (vs, new_bound, aux_vars') ->
	    if contains (safe_unsome mk_true decl_opt) (vs @ bvs) then
	      (v::vs, auxv::new_bound, aux_vars')
	    else
	      (vs, new_bound, auxv::aux_vars')) aux_vars ([], [], [])
	in
	let bvs' = List.map (fun vt -> (mk_true, pol, b, Innermost, (mk_const_decl vt None))) bvs in
	let f', _ = bind pol (new_bound @ bvs') f env in
	(f', aux_vars')
      in
      let extend_env env acc =
	List.rev_map (fun (_, _, _, _, ((vt, _), _)) -> vt) acc @ env 
      in
      let rec rewrite_atom pol env a =
	match a with
	(* Composed atoms *)
	| App (Const c, [t1; t2]) ->
	    (match c with
	    | Eq | Seteq | Subseteq | Subset | Elem
	    | Lt | Gt | LtEq | GtEq | Disjoint ->
 		let t1', acc1 = r pol genv env t1 in
		let env' = extend_env env acc1 in
		let t2', acc2 = r pol genv env' t2 in
		bind_inner pol [acc1; acc2] (App (Const c, [t1'; t2'])) (extend_env env' acc2)
	    | _ -> fail (msome_error "rewrite_atom" f))
	| _ -> (a, [])
      in
      let rec rewrite_form pol env f =
	match f with 
	(* Comments *)
	| App (Const Comment as c, [str; f]) ->
	    let f', aux_vars = rewrite_form pol env f in
	    (App (c, [str; f']), aux_vars)
        (* Boolean connectives *)
	| App (Const c, fs) ->
	    (match (c, fs) with 
	    | (Or, _) | (And, _) | (MetaAnd, _) -> 
		let fs', aux_vars = List.fold_right (fun f (fs', aux_vars) -> 
		  let f', aux_vars' = rewrite_form pol env f in (f'::fs', aux_vars' @ aux_vars)) fs ([], [])
		in (App (Const c, fs'), aux_vars)
	    | (Not, [f]) ->
		 let f', aux_vars = rewrite_form (not pol) env f in
		 (App (Const c, [f']), aux_vars)
	    | (Impl, [f1; f2]) | (MetaImpl, [f1; f2]) ->
		let f1', aux_vars1 = rewrite_form (not pol) env f1 in
		let f2', aux_vars2 = rewrite_form pol env f2 in
		(App (Const c, [f1'; f2']), aux_vars2 @ aux_vars1)
	    | (Iff, [f1; f2]) 
	    | (Eq, [TypedForm (_, TypeApp (TypeBool, [])) as f1; f2]) ->
		let f11, aux_vars11 = rewrite_form (not pol) env f1 in
		let f21, aux_vars21 = rewrite_form (not pol) env f2 in
		let f12, aux_vars12 = rewrite_form pol env f1 in
		let f22, aux_vars22 = rewrite_form pol env f2 in 
		if equal f11 f12 && equal f21 f22 then
		  (App (Const c, [f11; f21]), aux_vars21 @ aux_vars11)
                else
		  (smk_and [smk_impl (f11, f22);
			    smk_impl (f21, f12)], aux_vars12 @ aux_vars21) 
	    | _ when not (apply_to_terms) -> 
		let f', acc = r pol genv env f in
		bind_inner pol [acc] f' env
	    | _ -> rewrite_atom pol env f)
	(* Binders *)
	| Binder (Exists as b, vs, f)
	| Binder (Forall as b, vs, f) ->
	    (* make names of bound variables unique *)
	    let vs', sigma = List.fold_right (fun (v, ty) (vs', sigma) ->
	      if is_bound v (env @ genv) then
		let v' = get_fresh_tv "v" in
		((v', ty)::vs', (v, mk_var v')::sigma)
	      else ((v, ty)::vs', sigma)) vs ([], [])
	    in 
	    let f' = match sigma with [] -> f | _ -> subst sigma f in
	    let env' = vs' @ env in
	    let f', aux_vars = rewrite_form pol env' f' in
	    let f', aux_vars' = bind_outer pol b vs' aux_vars f' env' in
	    (f', aux_vars')
	(* Predicates *) 
	| App (Var v as pred, es) 
	| App (TypedForm (Var v, _) as pred, es) when apply_to_terms ->
	    let arg_tys = match normalize_type (get_type v (env @ genv)) with
	    | TypeFun (arg_tys, _) -> arg_tys
	    | TypeApp (TypeArray, [arg_ty; _]) -> [arg_ty]
	    | TypeUniverse -> List.map (fun _ -> TypeUniverse) es
	    | _ -> fail (merror "rewrite" "type error (1)" f)
	    in
	    let es', accs, env', _ = List.fold_right (fun e (es', accs, env', tys) -> 
	      match tys with
	      |	ty::tys' ->
		  (match (normalize_type ty, e) with 
		  | (TypeApp (TypeBool, []), _) -> 
		      let e', acc = rewrite_form pol env' e in
		      (e'::es', acc::accs, extend_env env' acc, tys')
		  | (TypeFun (_, TypeApp (TypeBool, [])), Binder (Lambda, vs, f)) ->
		      let env'' = vs @ env' in
		      let f', acc = rewrite_form pol env'' f in
		      let e', acc = bind_outer pol Lambda (List.rev vs) acc f' env'' in
		      (e'::es', acc::accs, extend_env env' acc, tys')
		  | _ ->
		      let e', acc = r pol genv env' e in 
		      (e'::es', acc::accs, extend_env env' acc, tys'))
	      | _ -> fail (merror "rewrite" "type error (2)" e)) 
		es ([], [], env, List.rev arg_tys)
	    in bind_inner pol accs (App (pred, es')) env'
	| TypedForm (f, ty) -> 
	    let f', aux_vars = rewrite_form pol env f in
	    (TypedForm (f', ty), aux_vars)
	| _ when not apply_to_terms -> 
	    let f', acc = r pol genv env f in
	    bind_inner pol [acc] f' env
	| _ -> rewrite_atom pol env f
      in rewrite_form pol env f
  in 
  let f, aux_vars = rewrite rewrite_rules pol [] f0 in
  let genv', defs, aux_vars1 = extend_genv aux_vars in
  let f1, _ = bind pol aux_vars1 f [] in
  let f' = if pol then smk_impl (smk_and defs, f1) else smk_and (f1::defs) in
  (f', genv')

(** A rewrite rule is a tuple [(r,k)] where [r] is the actual rewrite
   function and [k] determines wether [r] is applied to atomic
   formulae or to non-boolean subterms of atomic formulae.

   Rewrite functions:
   A rewrite [r call_back replace_map pol genv env f] is as follows:
   [call_back] allows [r] to recursively call back [TermRewrite.rewrite] 
   [replace_map] a mapping from terms to typed identifiers which is used 
     for common subexpression elimination.
   [pol] the polarity of the context in which [f] occurs.
   [genv] the global environment of the context of [f]
   [env] the local environment of variables bound in the context of [f]
   [f] the formula to be rewritten

   Return value of rewrite functions: 
   The return value of a rewrite function is a pair [(f', aux_decls)]
   where [f'] is the rewritten formula and [aux_decls] is a list of
   declarations for auxilliary variables that are introduced during
   rewriting.  Rewrite rules can choose whether auxiliary variables
   are bound immediately in the calling context of the rewrite rule or
   whether they are bound in the outermost possible scope wrt. bound
   variables in defining formulas of aux. variables. Defining formulas
   of auxiliary variables are not further rewritten in
   [!Termrewrite.rewrite]. This can be accomplished by applying function
   [call_back] on defining formulae.

*)

(** Term rewrite rule for elimination of set comprehensions *)
let rewrite_comprehensions : rewriteRule =
  let r = fun call_back replace_map pol genv env t ->
    let mk_quant = if pol then mk_inner_exists else mk_inner_exists in
    let rec rewrite t =
      match t with
      | Var v -> (t, [])
      | Const _ -> (t, [])
      | App (Const Comment as c, [str; t]) -> 
	let t', new_vars = rewrite t in
	(App (c, [str; t']), new_vars)
      | App (fun_t, ts) ->
	  let ts', new_vars = List.fold_right 
	      (fun t (ts', new_vars) ->
		let t', new_vars' = rewrite t in
		(t'::ts', new_vars' @ new_vars))
	      ts ([], [])
	  in
	  let fun_t', new_vars' = rewrite fun_t in 
	  (App (fun_t', ts'), new_vars' @ new_vars)	
      | Binder (Comprehension, vs, f) ->
	  let f', new_vars = call_back pol (vs @ env) f in
	  let t' =  Binder (Comprehension, vs, f') in
      	  let elem, elem_ty = match vs with
	  | [(v, ty)] -> (mk_var v, ty)
	  | _ -> let vars, tys = List.split vs in
	    (mk_tuple (List.map mk_var vars), mk_product_type tys)
	  in
	  (try (mk_var (fst (FormHashtbl.find replace_map t')), new_vars)
	  with Not_found ->
	    let set_var = get_fresh_tv "S" in
	    let t_rep = mk_var set_var in
	    let set_ty = mk_set_type elem_ty in
	    let decl = 
	      Some (smk_foralls (vs, mk_iff (mk_elem (elem, t_rep), f')))
	    in
	    let _ = FormHashtbl.add replace_map t' (set_var, set_ty) in
	    (t_rep, mk_quant pol t' (mk_const_decl (set_var, set_ty) decl) :: new_vars))
      | Binder (Lambda, vs, f) -> 
	  let f', new_vars = rewrite f in
	  let t' =  Binder (Lambda, vs, f') in
      	  (t', new_vars)
      | TypedForm (t, ty) -> 
	  let t', new_vars = rewrite t in
	  (TypedForm (t', ty), new_vars)
      | _ -> (t, [])
    in 
    match t with
    | Var _ | TypedForm (Var _, _) -> (t, [])
    | _ -> rewrite t
  in (r, RewriteTerms)

(** Rewrite rule for eliminating non-atomic set expressions, set comprehensions and set equality *)
let rewrite_sets : rewriteRule = 
  let r call_back _ pol genv env f =
    let generate_elem 
	(ty : typeForm) 
	(elem_opt : form option) : form * typedIdent list = match ty with
    | TypeApp (TypeSet, [TypeVar _ as elemty])
    | TypeApp (TypeSet, [TypeApp (_, []) as elemty]) ->
	let v = get_fresh_tv "v" in
	(safe_unsome (mk_var v) elem_opt, [(v, elemty)])
    | TypeApp (TypeSet, [(TypeProd tys)]) -> (* Set of tuples *)
	let vts = List.map (fun ty -> (get_fresh_tv "v", ty)) tys in
	(safe_unsome (mk_tuple (List.map (fun (v, _) -> mk_var v) vts)) elem_opt, vts)
    | _ -> failwith ("\nrewrite_sets encountered unexpected type: " ^ (string_of_type ty) ^ "\n")
    in
    let mk_compr vts ts' f =
      let m = List.fold_right2 (fun (v1, _) t acc ->
	(v1, t)::acc) vts ts' []
      in subst m f
    in
    let rewrite_setexp (elem : form) (tts : form list) (t : form) =
      let rec rewrite t =
	match normalize 1 t with
	| Const EmptysetConst -> (mk_false, [])
	| App (Const FiniteSetConst, ts) ->
	    (smk_or (List.map (fun t -> mk_eq (t, elem)) ts), [])
	| App (Const Cap, ts) ->
	    let ts', aux = List.fold_right (fun t (ts', aux) ->
	      let t', aux' = rewrite t in (t'::ts', aux' @ aux)) ts ([], [])
	    in
	    (smk_and ts', aux) 
	| App (Const Cup, ts) -> 
	    let ts', aux = List.fold_right (fun t (ts', aux) ->
	      let t', aux' = rewrite t in (t'::ts', aux' @ aux)) ts ([], [])
	    in
	    (smk_or ts', aux)
	| App (Const Diff, [t1; t2]) -> 
	    let t1', aux1 = rewrite t1 in
	    let t2', aux2 = rewrite t2 in
	    (smk_and [t1'; smk_not t2'], aux2 @ aux1)
	| Binder (Comprehension, vts', f) ->
	    let f', aux = 
	      call_back pol (vts' @ env) f 
	    in (mk_compr vts' tts f', aux)
	| f -> (mk_elem (elem, t), [])
	     (* failwith ("unsupported set expression" ^ PrintForm.string_of_form f) *)
      in rewrite t
    in 
    let rec is_set_expr (f : form) : bool =
      match f with
	| Const EmptysetConst
	| App(Const FiniteSetConst, _)
	| App(Const Cap, _)
	| App(Const Cup, _)
	| App(Const Diff, _)
	| Binder(Comprehension, _, _) -> true
	| App(Const Comment, [_; f'])
	| TypedForm(f', _) -> is_set_expr f'
	| _ -> false
    in
    match f with
    | App (Const (Seteq as c), [TypedForm (t1, ty); TypedForm (t2, _)])
    | App (Const (Subseteq as c), [TypedForm (t1, ty); TypedForm (t2, _)])  ->
	let elem, vts = generate_elem ty None in
	let t1', aux1 = rewrite_setexp elem (List.map (fun (v, _) -> mk_var v) vts) t1 in
	let t2', aux2 = rewrite_setexp elem (List.map (fun (v, _) -> mk_var v) vts) t2 in
	let mk_form = match c with
	| Subseteq -> smk_impl
	| _ -> mk_iff
	in
	let f' = mk_foralls (vts, mk_form (t1', t2')) in
	(f', aux2 @ aux1)
    | App (Const Subset, [TypedForm (t1, ty); TypedForm (t2, _)])  ->
	let elem, vts = generate_elem ty None in
	let t1', aux1 = rewrite_setexp elem (List.map (fun (v, _) -> mk_var v) vts) t1 in
	let t2', aux2 = rewrite_setexp elem (List.map (fun (v, _) -> mk_var v) vts) t2 in
	let f' = mk_and [smk_foralls (vts, smk_impl (t1', t2')); 
			 smk_exists (vts, smk_and [t2'; smk_not t1'])] 
	in
	(f', aux2 @ aux1)
    | App (Const Elem, [t; TypedForm (Binder (Comprehension, vts', bf), _)])
    | App (Const Elem, [t; Binder (Comprehension, vts', bf)]) ->
	let bf', aux = call_back pol (vts' @ env) bf in
	let ts = match normalize 1 t with
	| App (Const Tuple, ts) -> ts 
	| _ -> [t]
	in
	(try 
	  let sigma = List.fold_right2 
	      (fun (v, _) t acc -> (v, t)::acc)
	      vts' ts [] 
	  in (subst sigma bf', aux)
	with Invalid_argument _ ->
	  (App (Const Elem, [t; Binder (Comprehension, vts', bf')])), aux)
    | App (Const Elem, [elem; TypedForm (t, ty)]) ->
	let elem, vts = generate_elem ty (Some elem) in
	(match ([elem], vts) with
	| (_ as ts, [_]) 
	| ([App (Const Tuple, ts)], _) -> rewrite_setexp elem ts t
	| _ ->
	    let ts = List.map (fun (v, _) -> mk_var v) vts in
	    let t', aux = rewrite_setexp elem ts t in
          (smk_exists (vts, smk_and [mk_eq (elem, mk_tuple ts); t']), aux)) 
    | App(Const op, _) when (op = Seteq || op = Subseteq || op = Subset || op = Elem) ->
	failwith ("Didn't handle " ^ (string_of_form f) ^ "\n")
    | App (Const _, [t1; t2]) when ((is_set_expr t1) || (is_set_expr t2)) ->
	failwith ("Didn't handle " ^ (string_of_form f) ^ "\n")
    | _ -> (f, [])
  in (r, RewriteAtoms)

(** Term rewrite rule for elimination of FieldRead and FieldWrite *)
let rewrite_FieldRead_FieldWrite : rewriteRule =
  let r call_back replace_map pol genv env t =
    let rec remove t upd_args = 
      match t with
      (* Comments *)
      | App (Const Comment as c, [str; t]) ->
	  let t', acc_t = remove t upd_args in
	  App (c, [str; t']), acc_t
      (* FieldRead *)
      | App (Const FieldRead, t :: ts) 
	-> remove (App (t, ts)) upd_args
      (* field write followed by field read on the same index *)  
      | App (App (Const FieldWrite, [_; ind; upd]), [arg]) 
      | App (TypedForm (App (Const FieldWrite, [_; ind; upd]), _), [arg]) when equal ind arg ->
	  let upd', acc_upd = remove upd None in
	  upd', acc_upd
      (* start of FieldWrite sequence *)
      | App (App (Const FieldWrite, _) as fld, [arg]) 
      | App (TypedForm (App (Const FieldWrite, _), _) as fld, [arg]) ->
	  let arg', acc_arg = remove arg None in
	  let ty = match type_of_term (env @ genv) fld with
	  | TypeFun (_, res_ty)
	  | TypeApp (TypeArray, [_; res_ty]) -> res_ty
	  | _ -> TypeUniverse in
	  let rhs = get_fresh_tv "v" in
	  let fld', acc_fld = remove fld (Some (arg', rhs, [], [], mk_true, ty)) in
	  mk_var rhs, List.concat [acc_fld; acc_arg]
      (* FieldWrite *)
      | App (Const FieldWrite, [fd; ind; upd]) ->
	  (match upd_args with
	  | Some (arg, rhs, inds, updates, guard, ty) ->
	      let ind', acc_ind = remove ind None 
	      and upd', acc_upd = remove upd None in
	      let g = mk_neq (ind', arg) in
	      let guard' = smk_and [g;guard] in
	      let eq_fun = match ty with
		| TypeApp(TypeSet, _) -> mk_seteq
		| _ -> mk_eq in
	      let update = 
		if List.mem ind' inds then mk_false else
		  let typed_upd = TypedForm(upd', ty) in
		  let typed_rhs = TypedForm(mk_var rhs, ty) in
		    mk_and [guard; mk_eq (ind', arg); eq_fun (typed_upd, typed_rhs)]
	      in
	      let fd', acc_fd = remove fd (Some (arg, rhs, ind'::inds, update::updates, guard', ty)) in
	      fd', List.concat [acc_fd; acc_ind; acc_upd]
	  | _ -> fail (msome_error "rewrite_FieldRead_FieldWrite.remove.upd_args" t))
      | App (fld, args) -> 
	  let args', acc_args = 
	    List.fold_right (fun arg (args', acc_args) ->
	      let arg', acc_arg = remove arg None in
	      (arg' :: args', acc_arg :: acc_args)) args ([], [])
	  and fld', acc_fld = remove fld None in
	  App (fld', args'), List.concat acc_args
      | Var _ | Const _ ->
	  (match upd_args with
	  (* end of FieldWrite sequence *)
	  | Some (arg, rhs, _, updates, guard, ty) -> 
	      let upd_form = 
		mk_or
		  (smk_and [guard; mk_eq (App (t, [arg]), mk_var rhs)]
		   :: updates)
	      in 
	      let decl = Some upd_form in
	      t, [mk_inner_exists pol t (mk_const_decl (rhs, ty) decl)]
	  | _ -> t, [])
      | TypedForm (t, ty) -> 
	  let t', acc_t = remove t upd_args in
	  TypedForm (t', ty), acc_t
      | Binder (Comprehension, vs, f) -> 
	  let f', acc_f = call_back pol (vs @ env) f in
	  Binder (Comprehension, vs, f'), acc_f
      |	_ -> t, []
    in
    remove t None 
  in r, RewriteTerms

(** Term rewrite rule for unnesting of field applications *)
let rewrite_unnest : rewriteRule = 
  let r call_back replace_map pol genv env t =
    let rec flatten_term t new_vs =
      match t with
      | Var _ | Const _ -> (t, new_vs)
      | App (Const Comment as c, [str; t]) ->
	  let t', new_vs' = flatten_term t new_vs in
	  (App (c, [str; t']), new_vs')
      | App (fun_t, ts) ->
	  let res_ty = match type_of_term (env @ genv) fun_t with
	  | TypeFun (_, res_ty)
	  | TypeApp (TypeArray, [_; res_ty]) -> res_ty
	  | _ -> TypeUniverse
	  in
	  let fresh_v = get_fresh_tv "v" in
	  let v = Var fresh_v in
	  let ts', new_vs' = 
	    List.fold_right
	      (fun t (ts, new_vs) ->
		let t', new_vs' = flatten_term t new_vs in
		(t'::ts, new_vs'))  ts ([], new_vs)
	  in
	  let fun_t', new_vs' = 
	    flatten_term fun_t new_vs' in
	  let t' = App (fun_t', ts') in
	  let decl = Some (mk_eq (t', v)) in
	  (v, mk_inner_exists pol t' (mk_const_decl (fresh_v, res_ty) decl)::new_vs')
      | TypedForm (t, ty) -> 
	  let t', new_vs' = flatten_term t new_vs in
	  (TypedForm (t', ty), new_vs')
      |	Binder (Comprehension, vs, f) ->
	  let f', new_vs' = call_back pol (vs @ env) f in
	  (Binder (Comprehension, vs, f'), new_vs' @ new_vs)
      | _ -> (t, [])	  
    in match t with
    | Var _ -> (t, [])
    | _ -> flatten_term t []
  in (r, RewriteTerms)

(** Term rewrite rule for field constraint analysis Preconditions:                                            
   - all fields are atomic, i.e. in particular no FieldRead/FieldWrite                                    
   - field constraints are of the form (ALL v1 v2. f v1 = v2 --> F(v1,v2)) *)
let rewrite_derived_fields derived : rewriteRule =
  let r _ replace_map pol genv env t =
    let is_derived_field fld = List.mem fld derived in
    let mk_eq_constraint fld x c replace_map =
      let fs = FormHashtbl.fold (fun t (c', _) acc ->
	match t with 
	| App (fld', [x']) when equal fld fld' ->
	    mk_impl (mk_eq (x, x'), mk_eq (c, mk_var c'))::acc
	| _ -> acc) replace_map []
      in mk_and fs
    in
    let rec rewrite_ground_derived_fields t =
      match t with
      | Var v -> (t, [])
      | Const _ -> (t, [])
      | App (Const Comment as c, [str; t]) ->
	  let t', new_vars = rewrite_ground_derived_fields t in
	  (App (c, [str; t']), new_vars)
      | App (fun_t, ts) ->
	  let ts', new_vars = List.fold_right 
	      (fun t (ts', new_vars) ->
		let t', new_vars' = rewrite_ground_derived_fields t in
		(t'::ts', new_vars' @ new_vars))  
	      ts ([], [])
	  in
	  let t' = App (fun_t, ts') in
	  (match (fun_t, ts') with 
	  | (TypedForm (Var fld, _), [arg])
	  | (Var fld, [arg]) when is_derived_field fld  ->
	      let ty1, ty2 = (mk_object_type, mk_object_type) in
	      let const, new_vars' =
		try (mk_var (fst (FormHashtbl.find replace_map t')), new_vars)
		with Not_found ->
		  let fresh_c = get_fresh_tv "c_" in
		  let c = mk_var fresh_c in
		  let fdecl = Some (mk_eq (t', c))
		  in
		  let decl = ((fresh_c, ty2), fdecl) in
		  let new_var = mk_outer_forall pol t' (decl, mk_eq_constraint fun_t arg c)
		  in
		  let _ = FormHashtbl.add replace_map t' (fresh_c, ty2) in
		  (c, new_var::new_vars)
	      in
	      (const, new_vars')
	  | _ -> (t', new_vars))
      | TypedForm (t, ty) -> 
	  let t', new_vars = rewrite_ground_derived_fields t in
	  (TypedForm (t', ty), new_vars)
      | _ -> fail (msome_error "rewrite_derived_fields" t)
    in 
    match t with
    | Var _ -> (t, [])
    | _ -> rewrite_ground_derived_fields t
  in (r, RewriteTerms)

(** Rewrite rule for elimination of atoms which MONA cannot deal with.
   Precondition: annotated types, all terms flattend *)
let rewrite_non_msol_atoms : rewriteRule = 
  let r call_back replace_map pol genv env a =
    let rec is_mso_type ty = 
      let is_mso_typesimple ty = 
	match ty with
	| TypeBool | TypeObject | TypeSet | TypeArray -> true
	| _ -> false
      in
      match normalize_type ty with
      | TypeApp (sty, tys) -> 
	  is_mso_typesimple sty && List.for_all is_mso_type tys
      | TypeFun (tys, res_ty) ->
	  is_mso_type res_ty &&  List.for_all is_mso_type tys
      | _ -> false
    in
    let drop () =
      try (mk_var (fst (FormHashtbl.find replace_map a)), [])
      with Not_found ->  
	let fresh_c = get_fresh_tv "b_" in
	let c = mk_var fresh_c in
	let _ = FormHashtbl.add replace_map a (fresh_c, mk_bool_type) in
	Debug.lmsg 4 (fun () -> "dropping atom from formula:\n" ^ string_of_form a ^ "\n");
	(c, [mk_outer_forall pol a (mk_const_decl (fresh_c, mk_bool_type) None)])
      (* if pol then (mk_false, []) else (mk_true, []) *)
    in
    let check_type ty =
      is_mso_type ty && 
      safe_unsome 3 (order_of_type ty) <= 2     
    in
    let rec check a =
      match a with
      | Const (BoolConst _) | App (Const BoolConst _, []) -> true
      | Const _ -> true
      | Var v -> check_type (get_type v (env @ genv))
      | App (Var v, ts) -> check_type (get_type v (env @ genv)) && List.for_all check ts
      | App (Const Eq, [TypedForm (t1, ty); t2])
      | App (Const Seteq, [TypedForm (t1, ty); t2]) 
      | App (Const Subseteq, [TypedForm (t1, ty); t2]) 
      | App (Const Subset, [TypedForm (t1, ty); t2]) 
      | App (Const Elem, [t1; TypedForm (t2, ty)]) 
	-> check_type ty && check t1 && check t2
      | App (Const Comment, [_; f]) -> check f
      | App (fn, ts) -> List.for_all check (fn :: ts)
      | TypedForm (t, ty) -> check_type ty && check t
      | _ -> false
    in 
    if check a then (a, []) else drop () 
  in (r, RewriteAtoms)

(** Rewrite rule for elimination of predicate "tree" using "rtrancl_pt" *)
let rewrite_tree : rewriteRule =
  let xs, ys, zs = 
    (FormUtil.fresh_var "v", 
     FormUtil.fresh_var "v", 
     FormUtil.fresh_var "v")
  in
  let x, y, z = 
    (FormUtil.mk_var xs, 
     FormUtil.mk_var ys, 
     FormUtil.mk_var zs)     
  in 
  let r _ _ pol genv env f =
    let mk_tree fields =
      let r x y = 
	FormUtil.smk_or 
	  (List.rev_map (fun fld -> mk_eq (App (fld, [x]), y)) fields) 
      in
      let r_pred = Binder (Lambda, [(xs, mk_object_type); (ys, mk_object_type)], r x y) in 
      let rtrancl_r x y = App (mk_var str_rtrancl, [r_pred; x; y]) in
      let acyclic =
	match fields with
	| [_] ->
	 (* use a simpler way to express acyclicity if backbone is a list *)
	    FormUtil.mk_foralls ([(xs, mk_object_type)], rtrancl_r x (mk_null))
	| _ ->
	    FormUtil.mk_foralls
	      ([(xs, mk_object_type); (ys, mk_object_type); (zs, mk_object_type)],
               FormUtil.smk_impl (FormUtil.smk_and
				    [FormUtil.mk_neq (FormUtil.mk_null, x);
				     r x y; rtrancl_r y z], FormUtil.mk_neq (x, z)))
      in
      let no_sharing =
	mk_foralls
	  ([(xs, mk_object_type); (ys, mk_object_type); (zs, mk_object_type)],
           mk_impl (smk_and [mk_neq (y, z); r y x; mk_neq (mk_null, x)],
                    smk_not (r z x)))
      in
      FormUtil.smk_and [mk_comment "acyclicity" acyclic; 
			mk_comment "no sharing" no_sharing]
    in
    let mk_res f = (f, []) in
    match f with
    | App (Var str_tree, [App (Form.Const ListLiteral, fields)])
    | App (TypedForm (Var str_tree, _), [App (Form.Const ListLiteral, fields)]) ->
	mk_res (mk_tree fields)
    | _ -> mk_res f
  in (r, RewriteAtoms)

(** Expand pointsto relations *)
let rewrite_pointsto : rewriteRule =
  let mk_res f = (f, []) in
  let r _ _ pol genv env f =
    match f with
    | App (Var pointsto, [s1; f; s2]) 
    | App (TypedForm (Var pointsto, _), [s1; f; s2])
      when pointsto = points_to_name ->
	mk_res (mk_points_to_expansion s1 f s2)
    | _ -> mk_res f
  in (r, RewriteAtoms)


(** Rewrite rule for elimination of equality on functions *)
let rewrite_function_eq : rewriteRule =
  let r call_back replace_map pol genv env f =
    let mk_res f = (f, []) in
    let res = match f with
    | App (Const Eq, [TypedForm (t1, TypeFun (arg_tys, res_ty)); TypedForm (t2, _)])
    | App (Const Eq, [TypedForm (t1, TypeFun (arg_tys, res_ty)); t2])
    | App (Const Eq, [t2; TypedForm (t1, TypeFun (arg_tys, res_ty))]) ->
	let xts = List.map (fun ty -> (fresh_var "v", ty)) arg_tys in
	let xs = List.map (fun (x, _) -> mk_var x) xts in
	let t1' = TypedForm (App (t1, xs), res_ty)
	and t2' = TypedForm (App (t2, xs), res_ty) in
	let f' = App (Const Eq, [t1'; t2']) in
	smk_foralls (xts, f')
    | App (Const Eq, [TypedForm (t1, TypeApp (TypeArray,[arg_ty; res_ty])); TypedForm (t2, _)])
    | App (Const Eq, [TypedForm (t1, TypeApp (TypeArray, [arg_ty; res_ty])); t2])
    | App (Const Eq, [t2; TypedForm (t1, TypeApp (TypeArray, [arg_ty; res_ty]))]) ->
	let arg_tys, res_ty0 =
	  match res_ty with
	    | TypeApp (TypeArray, [arg_ty0; res_ty1]) ->
		[arg_ty; arg_ty0], res_ty1
	    | _ -> [arg_ty], res_ty in
	let xts = List.map (fun ty -> (fresh_var "varg", ty)) arg_tys in
	let xs = List.map (fun (x, _) -> mk_var x) xts in
	let t1' = TypedForm (App (t1, xs), res_ty0)
	and t2' = TypedForm (App (t2, xs), res_ty0) in
	let f' = App (Const Eq, [t1'; t2']) in
	  smk_foralls (xts, f')
    | _ -> f in
    mk_res res
  in (r, RewriteAtoms)

(* Rewrites sets into predicates by rewriting elem's into function
   application. *)
let rewrite_elems (f : form) (env : typeEnv) : form * typeEnv =
  let rec rewrite_set_type (ty : typeForm) : typeForm =
    match ty with
      | TypeApp(TypeSet, tys) ->
	  let tys0 = List.map rewrite_set_type tys in
	    TypeFun(tys0, TypeApp(TypeBool, []))
      | TypeApp(st, tys) ->
	  TypeApp(st, (List.map rewrite_set_type tys))
      | TypeFun(tys, ty0) ->
	  let tys0 = List.map rewrite_set_type tys in
	  let ty1 = rewrite_set_type ty0 in
	    TypeFun(tys0, ty1)
      | TypeProd(tys) ->
	  TypeProd(List.map rewrite_set_type tys)
      | _ -> ty in
  let rewrite_env (env : typeEnv) : typeEnv =
    List.map (fun (id, ty) -> (id, (rewrite_set_type ty))) env in
  let rec rewrite_elems_rec (f : form) : form =
    match f with
      | App(Const Elem, [_; (Const EmptysetConst)])
      | App(Const Elem, [_; TypedForm(Const EmptysetConst, _)]) ->
	  Const (BoolConst false)
      | App(Const Elem, [f0; f1]) ->
	  App(rewrite_elems_rec f1, [rewrite_elems_rec f0])
      | App(Const FiniteSetConst, _)
      | App(Const Cap, _)
      | App(Const Cup, _)
      | App(Const Diff, _)
      | Binder(Comprehension, _, _) ->
	  failwith ("rewrite_elems did not expect: " ^ (string_of_form f) ^ "\n")
      | App(f0, fs) ->
	  App(rewrite_elems_rec f0, List.map rewrite_elems_rec fs)
      | Binder(b, til, f0) ->
	  let ids, tys = List.split til in
	  let tys0 = List.map rewrite_set_type tys in
	  let til0 = List.combine ids tys0 in
	    Binder(b, til0, (rewrite_elems_rec f0))
      | TypedForm(f0, ty) ->
	  TypedForm((rewrite_elems_rec f0), (rewrite_set_type ty))
      | _ -> f in
    ((rewrite_elems_rec f), (rewrite_env env))
      
type tupleMap = (ident, form list) Hashtbl.t

(* Rewrites tuples into individual elements. A named tuple T is
   rewritten as t0, t1, ... etc. In order for this pass to work
   properly, it's important that sets have already been translated
   into predicates. *)
let rewrite_tuples (m : tupleMap) (f : form) (env : typeEnv) : form * typeEnv =
  let make_elems (id : ident) lst : form list =
    try Hashtbl.find m id
    with Not_found ->
      let elms = 
	List.map (fun f -> Var (FormUtil.fresh_var (id ^ "_tup_"))) lst in
	Hashtbl.add m id elms; elms in
  let extract_id (f : form) : ident =
    match f with 
      | TypedForm(Var id, _) -> id 
      | _ -> failwith ("unexpected form: "^ (string_of_form f) ^ "\n") in
  let rec rewrite_tuple_ty (ty : typeForm) : typeForm =
    match ty with
      | TypeApp(st, tys) ->
	  TypeApp(st, rewrite_tuple_tys tys)
      | TypeFun(tys, ty) ->
	  TypeFun((rewrite_tuple_tys tys), (rewrite_tuple_ty ty))
      | _ -> ty
  and rewrite_tuple_tys (tys : typeForm list) : typeForm list =
    match tys with
      | [] -> []
      | ty :: tys_rest ->
	  let ty' = rewrite_tuple_ty ty in
	  let tys_rest' = rewrite_tuple_tys tys_rest in
	    match ty' with
	      | TypeProd tys_tup ->
		  tys_tup @ tys_rest'
	      | _ -> ty' :: tys_rest' in
  let rec rewrite_env (env : typeEnv) : typeEnv =
    match env with
      | [] -> []
      | (id, ty) :: ti_rest ->
	  let ty' = rewrite_tuple_ty ty in
	  let ti_rest' = rewrite_env ti_rest in
	    match ty' with
	      | TypeProd tys ->
		  let fs = make_elems id tys in
		  let ids = List.map extract_id fs in
		    (List.combine ids tys) @ ti_rest'
	      | _ -> (id, ty') :: ti_rest' in
  let rec rewrite_tuples_rec (f : form) : form = 
    match f with
    | App(Const Eq, [App(Const Tuple, fs0); App(Const Tuple, fs1)])
    | App(Const Eq, [TypedForm(App(Const Tuple, fs0), _); App(Const Tuple, fs1)])
    | App(Const Eq, [App(Const Tuple, fs0); TypedForm(App(Const Tuple, fs1), _)])
    | App(Const Eq, [TypedForm(App(Const Tuple, fs0), _); TypedForm(App(Const Tuple, fs1), _)]) ->
	let fs0' = List.map rewrite_tuples_rec fs0 in
	let fs1' = List.map rewrite_tuples_rec fs1 in
	  smk_and (List.map2 smk_eq fs0' fs1')
    | App(Const Eq, [App(Const Tuple, fs0); Var v])
    | App(Const Eq, [TypedForm(App(Const Tuple, fs0), _); Var v])
    | App(Const Eq, [App(Const Tuple, fs0); TypedForm(Var v, _)])
    | App(Const Eq, [TypedForm(App(Const Tuple, fs0), _); TypedForm(Var v, _)])
    | App(Const Eq, [Var v; App(Const Tuple, fs0)])
    | App(Const Eq, [TypedForm(Var v, _); App(Const Tuple, fs0)])
    | App(Const Eq, [Var v; TypedForm(App(Const Tuple, fs0), _)])
    | App(Const Eq, [TypedForm(Var v, _); TypedForm(App(Const Tuple, fs0), _)]) ->
	let fs0' = List.map rewrite_tuples_rec fs0 in
	let fs1 = make_elems v fs0 in
	  smk_and (List.map2 smk_eq fs0' fs1)
    | App(Const Elem, _) ->
	failwith ("rewrite_tuples_rec did not expect: " ^ (string_of_form f) ^ "\n")
    | App(f0, fs) ->
	App(rewrite_tuples_rec f0, rewrite_tuple_args fs)
    | Binder(b, til, f0) ->
	  Binder(b, (rewrite_env til), (rewrite_tuples_rec f0))
    | TypedForm(f0, ty) ->
	TypedForm(rewrite_tuples_rec f0, rewrite_tuple_ty ty)
    | _ -> f
  and rewrite_tuple_args (fs : form list) : form list =
    match fs with
      | [] -> fs
      | f0 :: f_rest ->
	  let f0' = rewrite_tuples_rec f0 in
	  let f_rest' = rewrite_tuple_args f_rest in
	    match f0' with
	      | TypedForm(App(Const Tuple, fs0), TypeProd tys) ->
		  let fs0' = List.map2 (fun f ty -> TypedForm(f, ty)) fs0 tys in
		    fs0' @ f_rest'
	      | App(Const Tuple, fs0) 
	      | TypedForm(App(Const Tuple, fs0), _) ->
		  fs0 @ f_rest'
	      | _ -> f0' :: f_rest' in
    ((rewrite_tuples_rec f), (rewrite_env env))
