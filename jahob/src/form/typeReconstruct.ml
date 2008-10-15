(** Type reconstruction a la Hindley/Milner. *)

open Util
open PrintForm
open Form
open FormUtil
open TypeVars

let debug_msg = Debug.debug_lmsg (Debug.register_debug_module "typeReconstruct")

let raise_error p msg f = 
  Debug.msg ("typeReconstruct.raise_error form ast: " ^ MlPrintForm.string_of_form f);
  fail ("TypeReconstruct." ^ p ^ ": " ^ msg ^ ":\n" ^ PrintForm.string_of_form f)

let fresh_type_var () = TypeVar (get_fresh_tv "a")

let fresh_type_vars t0 =
  let (subst : (ident * ident) list ref) = ref [] in
  let process_tvar (tvar : ident) =
    try List.assoc tvar !subst 
    with Not_found ->
      (let fresh = get_fresh_tv "a" in
	 subst := (tvar, fresh) :: !subst;
	 fresh)
  in
  let rec walk t = match t with
      | TypeUniverse -> TypeVar (process_tvar (get_fresh_tv "a"))
      | TypeVar tv -> TypeVar (process_tvar tv)
      | TypeApp (t1, ts) -> TypeApp(t1, List.map walk ts)
      | TypeFun (ts, t1) -> TypeFun(List.map walk ts, walk t1)
      | TypeProd ts -> TypeProd (List.map walk ts)
  in 
  walk t0

let type_of_const =
  (* TODO: add types of missing constants *)
  let alpha = TypeVar "a" in
  let beta = TypeVar "b" in
  let ht = Hashtbl.create 10 in
  let _ = List.iter (uncurry (Hashtbl.add ht))
      [(MetaImpl, mk_fun_type [mk_bool_type; mk_bool_type] mk_bool_type);
       (Impl, mk_fun_type [mk_bool_type; mk_bool_type] mk_bool_type);
       (Iff, mk_fun_type [mk_bool_type; mk_bool_type] mk_bool_type);
       (Not, mk_fun_type [mk_bool_type] mk_bool_type);
       (MetaEq, mk_fun_type [alpha; alpha] mk_bool_type);
       (Eq, mk_fun_type [alpha; alpha] mk_bool_type);
       (Ite, mk_fun_type [mk_bool_type; alpha; alpha] alpha);
       (Minus, mk_fun_type [alpha; alpha] alpha);
       (LtEq, mk_fun_type [alpha; alpha] mk_bool_type);
       (* integers *)
       (Lt, mk_fun_type [mk_int_type; mk_int_type] mk_bool_type);
       (Gt, mk_fun_type [mk_int_type; mk_int_type] mk_bool_type);
       (GtEq, mk_fun_type [mk_int_type; mk_int_type] mk_bool_type);
       (Plus, mk_fun_type [mk_int_type; mk_int_type] mk_int_type);
       (UMinus, mk_fun_type [mk_int_type] mk_int_type);
       (Mult, mk_fun_type [mk_int_type; mk_int_type] mk_int_type);
       (Div, mk_fun_type [mk_int_type; mk_int_type] mk_int_type);
       (Mod, mk_fun_type [mk_int_type; mk_int_type] mk_int_type);
       (* arrays *)
       (ArrayRead, mk_fun_type 
	  [mk_state_array alpha; mk_object_type; mk_int_type] alpha);
       (ArrayWrite, mk_fun_type 
	  [mk_state_array alpha; mk_object_type; mk_int_type; alpha]
	  (mk_state_array alpha));
       (* fields, objects *)
       (NullConst, mk_object_type);
       (FieldRead, mk_fun_type [mk_field_type alpha; mk_object_type] alpha);
       (FieldWrite, mk_fun_type [mk_field_type alpha; mk_object_type; alpha]
  			         (mk_field_type alpha));
       (* sets *)
       (Card, mk_fun_type [mk_set_type alpha] mk_int_type);
       (Cardeq, mk_fun_type [mk_set_type alpha; mk_int_type] mk_bool_type);
       (Cardleq, mk_fun_type [mk_set_type alpha; mk_int_type] mk_bool_type);
       (Cardgeq, mk_fun_type [mk_set_type alpha; mk_int_type] mk_bool_type);
       (EmptysetConst, mk_set_type alpha);
       (Elem, mk_fun_type [alpha; mk_set_type alpha] mk_bool_type);
       (Subseteq, mk_fun_type [mk_set_type alpha; mk_set_type alpha] mk_bool_type);
       (Subset, mk_fun_type [mk_set_type alpha; mk_set_type alpha] mk_bool_type);
       (Seteq, mk_fun_type [mk_set_type alpha; mk_set_type alpha] mk_bool_type);
       (Diff, mk_fun_type [mk_set_type alpha; mk_set_type alpha] 
                       (mk_set_type alpha));
       (Rtrancl, mk_fun_type [mk_set_type (mk_product_type [alpha; alpha])] 
	  (mk_set_type (mk_product_type [alpha; alpha])));
       (Rimage, mk_fun_type [mk_set_type (mk_product_type [alpha; beta]); mk_set_type alpha] (mk_set_type beta));
       (* others *)
       (Unit, mk_unit_type);
       (Comment, mk_fun_type [mk_string_type; alpha] alpha);
       (Old, mk_fun_type [alpha] alpha)
     ]
  in fun c n -> 
    match c with
    | BoolConst _ -> mk_bool_type
    | IntConst _ -> mk_int_type
    | StringConst _ -> mk_string_type
    | MetaAnd | And | Or -> 
	mk_fun_type (generate_list (fun _ -> mk_bool_type) n) mk_bool_type
    | Cup | Cap -> 
	let ty = mk_fun_type (generate_list (fun _ -> mk_set_type alpha) n) (mk_set_type alpha) in
	fresh_type_vars ty
    | FiniteSetConst ->
	let ty = mk_fun_type (generate_list (fun _ -> alpha) n) (mk_set_type alpha) in
	fresh_type_vars ty
    | Tuple ->
	let tys = generate_list (fun _ -> fresh_type_var ()) n in
	mk_fun_type tys (mk_product_type tys)
    | ListLiteral ->
	let arg_tys = generate_list (fun _ -> alpha) n in
	let ty = mk_fun_type arg_tys (mk_list_type alpha) in
	fresh_type_vars ty
    | _ -> 
	try fresh_type_vars (Hashtbl.find ht c) 
	with Not_found -> raise_error "get_type_of_const" "type of constant unknown" (Const c)

let type_of_var =
  let alpha = TypeVar "a" in
  let ht = Hashtbl.create 2 in
  let _ = List.iter (uncurry (Hashtbl.add ht)) 
      [(str_rtrancl, fun _ -> mk_fun_type [mk_fun_type [alpha; alpha] mk_bool_type; alpha; alpha] mk_bool_type);
       (str_tree, fun _ -> mk_fun_type [mk_list_type (mk_field_type mk_object_type)] mk_bool_type)]
  in fun env v n ->
  let get_type v = 
    let ty = Hashtbl.find env v in 
    match ty with
    | TypeUniverse ->
	let res_ty = fresh_type_var ()
	in Hashtbl.replace env v res_ty; res_ty 
    | _ -> ty
  in 
  try get_type v with
  | Not_found ->
      let ty = 
	try fresh_type_vars (Hashtbl.find ht v n) 
	with Not_found -> fresh_type_var ()
      in Hashtbl.replace env v ty; ty

let subst_type subst_map ty =
  let rec st ty = match ty with
  | TypeUniverse -> ty
  | TypeFun (arg_tys, res_ty) -> 
      let arg_tys' = List.map st arg_tys in
      TypeFun (arg_tys', st res_ty)
  | TypeApp (sty, tys) ->
      let tys' = List.map st tys in
      TypeApp (sty, tys')
  | TypeProd tys ->
      let tys' = List.map st tys in
      TypeProd tys'
  | TypeVar v -> 
      try Hashtbl.find subst_map v
      with Not_found -> ty
  in st ty
     
let subst_types_in_form subst_map f =
  let rec st f = match f with
  | Var _ | Const _ -> f
  | App (fn, fs) -> App (st fn, List.map st fs)
  | Binder (b, vts, f') -> 
      let vts' = List.rev_map (fun (v, ty) -> (v, subst_type subst_map ty)) vts in
      Binder (b, vts', st f')
  | TypedForm (TypedForm (f, _), ty)
  | TypedForm (f, ty) -> TypedForm (st f, subst_type subst_map ty)
  in st f

let print_subst subst_map = 
  Hashtbl.iter (fun v ty -> Printf.printf "%s -> %s\n" v (PrintForm.string_of_type ty)) subst_map
  

let solve_constraints cs =
  let mgu = Hashtbl.create 0 in
  let type_error (ty1, ty2) f = raise_error "solve_constraints" 
      (Printf.sprintf "type error\ntried to match type\n\t%s\nwith type\n\t%s\nin formula" 
	 (PrintForm.string_of_type ty1) (PrintForm.string_of_type ty2)) (subst_types_in_form mgu f) 
  in
  let occur_error f = raise_error "solve_constraints" "occurs check failed" (subst_types_in_form mgu f) in
  let add_subst v ty cs f =
    if List.mem v (ftv ty) then occur_error f 
    else begin
      Hashtbl.replace mgu v ty;
      Hashtbl.iter (fun v' ty' -> Hashtbl.replace mgu v' (subst_type mgu ty')) mgu; 
      cs
    end
  in
  (* let type_error tys f = print_subst mgu; type_error tys f in *)
  let rec solve cs =
    match cs with
    | (tys, f)::cs' -> 
	(match tys with
	| (TypeApp (TypeArray, [arg_ty1; res_ty1]),
	   TypeFun (arg_ty2::arg_tys2, res_ty2))
	| (TypeFun (arg_ty2::arg_tys2, res_ty2),
	   TypeApp (TypeArray, [arg_ty1; res_ty1])) ->
	     solve (((arg_ty1, arg_ty2), f) :: 
		    ((res_ty1, TypeFun (arg_tys2, res_ty2)), f) :: cs')
	| (TypeApp (st1, tys1), TypeApp (st2, tys2)) when st1 = st2 ->
	    let new_cs = try
	      List.fold_left2 (fun cs ty1 ty2 -> ((ty1, ty2), f)::cs) cs' tys1 tys2 
	    with Invalid_argument _ -> type_error tys f
	    in solve new_cs
	| (TypeProd tys1, TypeProd tys2) ->
	    let new_cs = try
	      List.fold_left2 (fun cs ty1 ty2 -> ((ty1, ty2), f)::cs) cs' tys1 tys2 
	    with Invalid_argument _ -> type_error tys f
	    in solve new_cs
	| (TypeFun ([], ty1), ty2)
	| (ty1, TypeFun ([], ty2)) -> solve (((ty1, ty2), f) :: cs')
	| (TypeFun (arg_ty1::arg_tys1, res_ty1), 
	   TypeFun (arg_ty2::arg_tys2, res_ty2)) ->
	  solve (((arg_ty1, arg_ty2), f) :: ((TypeFun (arg_tys1, res_ty1), TypeFun (arg_tys2, res_ty2)), f) :: cs')
	| ((TypeVar v as ty1), ty2)
	| (ty2, (TypeVar v as ty1)) ->
	    if not (ty1 = ty2) then 
	      let ty1' = subst_type mgu ty1 in
		 if ty1 = ty1' then
		   let ty2' = subst_type mgu ty2 in
		     if ty1' = ty2' then solve cs'
		     else solve (add_subst v ty2' cs' f)
		 else solve (((ty1', subst_type mgu ty2), f) :: cs')
	    else solve cs'
	| _ -> type_error tys f
	)
    | _ -> mgu
  in solve cs


let infer_types global_env f =
  let _ = debug_msg 2 (fun () -> PrintForm.string_of_form f) in 
  let type_constraints = ref [] in
  let env = Hashtbl.create 0 in
  let add_var (v, ty) =
    let ty' = fresh_type_vars ty in
    Hashtbl.add env v ty'; (v, ty')
  in
  let annotate_type f ty = match f with
  | TypedForm (f0, _) -> TypedForm (f0, ty)
  | _ -> TypedForm (f, ty)
  in
  let _ = List.map add_var global_env in
  let add_constraint ty1 ty2 f =
    if not (normalize_type ty1 = normalize_type ty2) then 
      (* let _ = 
	Printf.printf "  %s = %s in %s\n" 
	  (PrintForm.string_of_type ty1) 
	  (PrintForm.string_of_type ty2) 
	  (string_of_form f)
      in *)
      if List.for_all (fun ((ty1', ty2'), _) -> not (ty1 = ty1' && ty2 = ty2')) !type_constraints
      then type_constraints := ((ty1, ty2), f) :: !type_constraints
  in
  let rec res_type fn_ty arg_tys f =
    let rec match_types arg_tys1 arg_tys2 res_ty =
      match (arg_tys1, arg_tys2) with
      | (ty1::arg_tys1, ty2::arg_tys2) -> 
	  add_constraint ty1 ty2 f; match_types arg_tys1 arg_tys2 res_ty
      |	(ty1::_, []) -> TypeFun (arg_tys1, res_ty)
      |	([], []) -> res_ty
      |	([], _) -> res_type res_ty arg_tys2 f
    in match fn_ty with
    | TypeFun (arg_tys1, res_ty) -> 
	match_types arg_tys1 arg_tys res_ty
    | TypeApp (TypeArray, [arg_ty; res_ty]) -> 
	match_types [arg_ty] arg_tys res_ty 
    | _ -> let res_ty = fresh_type_var () in 
      add_constraint fn_ty (TypeFun (arg_tys, res_ty)) f; res_ty
  in
  let rec gen f =
    match f with 
    | Var v -> (f, type_of_var env v 0)
    | Const c -> (f, type_of_const c 0)
    | App (fn, args) ->
	let fn', fn_ty = 
	  match fn with
	  | Const c -> (fn, type_of_const c (List.length args))
	  | Var v -> (fn, type_of_var env v (List.length args))
	  | _ -> gen fn 
	in
	let args', arg_tys = List.fold_left (fun (args', arg_tys) (t, ty) ->
	  (t::args', ty::arg_tys)) ([], []) (List.rev_map gen args) in
	let res_ty = res_type fn_ty arg_tys f in
	(* add type annotations to polymorphic operators *)
	let f' = match fn with 
	| Const Eq | Const LtEq | Const Minus | Const Elem 
	| Const Subseteq | Const Subset -> 
	    let args' = List.map2 (fun f ty -> annotate_type f ty) args' arg_tys 
	    in App (fn', args')
	| _ -> App (fn', args')
	in (f', res_ty)
    | TypedForm (f, ty) ->
	let f', ty' = match f with
	| Var v when not (Hashtbl.mem env v) ->
	    let v, ty' = add_var (v, ty) in
	    (f, ty')
	| _ ->	
	    let f', ty' = gen f in
	    let ty = 
	      if ty = TypeUniverse then fresh_type_var () 
	      else ty 
	    in 
	    add_constraint ty ty' f; (f', ty')
	in (annotate_type f' ty', ty')
    | Binder (b, vts, bf) ->
	let vts', tys' = List.fold_left (fun (vts', tys') vt -> 
	  let vt' = add_var vt in (vt'::vts' , snd vt'::tys')) ([], []) vts in
	let bf', ty_bf = gen bf in
	let _ = List.iter (fun (v, _) -> Hashtbl.remove env v) vts in
	let binder_ty = match b with
	| Exists | Forall ->
	    add_constraint mk_bool_type ty_bf f;
	    mk_bool_type
	| Comprehension ->
	    add_constraint mk_bool_type ty_bf f;
	    (match tys' with
	    | [ty] -> mk_set_type ty 
	    | _ -> mk_set_type (mk_product_type tys'))
	| Lambda -> TypeFun (tys', ty_bf)
	in
	(Binder (b, vts', bf'), binder_ty)
  in
  let f', f_ty = gen f in
  let global_env' = Hashtbl.fold
      (fun v ty env' -> (v, ty)::env') env []
  in
  (f', global_env', f_ty, !type_constraints)


(** [get_env f] compute the global environment for formula [f] *)
let get_env f =
   let _, env, _, type_constraints = infer_types [] f in
   let mgu = solve_constraints type_constraints in
   List.map (fun (v, ty) -> (v, subst_type mgu ty)) env


(** [well_typed env f] check whether formula [f] is well-typed in environment [env] *)
let well_typed env f =
  try
    let f', _, _, type_constraints = infer_types env f in
    ignore (solve_constraints type_constraints); true
  with Failure msg -> Util.warn msg; false

(** [get_type env f] get the type of [f] for environment [env] *)
let get_type env f =
  let f', _, f_ty, type_constraints = infer_types env f in
  let mgu = solve_constraints type_constraints in
  subst_type mgu f_ty

(** [reconstruct_types env f] reconstruct types in formula [f] and environment [env] *) 
let reconstruct_types env f =
  let _ = debug_msg 0 (fun () -> "Reconstructing types...\n") in
  let f', env', _, type_constraints = infer_types env f in
  let mgu = solve_constraints type_constraints in
  (* let _ = print_subst mgu in *)
  let f'' = subst_types_in_form mgu f' in 
  let env'' = List.map (fun (v, ty) -> (v, subst_type mgu ty)) env' in 
  let _ = debug_msg 0 (fun () -> "\nType reconstruction done.\n") in
  (f'', env'')

(** [disambiguate f] resolve ad-hoc polymorphism in [f] as much as possible *)
let disambiguate f =
  let rec da f = match f with
  | Var _ 
  | Const _ -> f
  | App (Const c, [TypedForm (t1, t1_ty) as tt1; tt2]) ->
      let tt1' = da tt1
      and tt2' = da tt2 in
      let c' = match (c, t1_ty) with
      |	(MetaEq, TypeApp (TypeBool, []))
      |	(Eq, TypeApp (TypeBool, [])) -> Iff
      | (MetaEq, TypeApp (TypeSet, _))
      | (Eq, TypeApp (TypeSet, _)) -> Seteq
(*    |	(Sub, TypeApp (TypeSet, _)) -> Subseteq *)
(*    |	(Sub, TypeApp (TypeInt, _)) -> LtEq *)
      |	(LtEq, TypeApp (TypeSet, _)) -> Subseteq
      |	(Minus, TypeApp (TypeSet, _)) -> Diff
      |	_ -> c
      in App (Const c', [tt1'; tt2']) 
  | TypedForm (f, ty) -> TypedForm (da f, ty)
  | App (fn, args) -> App (da fn, List.map da args)
  | Binder (b, vts, f) -> Binder (b, vts, da f)
  in da f


