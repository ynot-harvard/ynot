(**  Utility functions for manipulating {!Form} formulas. *)

open Form
open TypeVars

(* Debug messages *)
let debug_id = Debug.register_debug_module "FormUtil"
let debug_lmsg = Debug.debug_lmsg debug_id
let debug_msg = Debug.debug_msg debug_id

let arrayName = "Array"
let shortArrayStateId = "arrayState"
let arrayStateId = arrayName ^ "." ^ shortArrayStateId
let arrayStateVar = Var arrayStateId

let shortArrayLengthId = "length"
let arrayLengthId = arrayName ^ "." ^ shortArrayLengthId
let arrayLengthVar = Var arrayLengthId

(** Smart formula makers. *)

let mk_true = Const (BoolConst true)
let mk_false = Const (BoolConst false)
let mk_bool b = if b then mk_true else mk_false
let mk_int k = Const (IntConst k)
let mk_not f = App (Const Not, [f])
let mk_and cs = match cs with
| [] -> mk_true
| [f] -> f
| _ -> App (Const And, cs)
let mk_metaand cs = match cs with
| [] -> mk_true
| [f] -> f
| _ -> App (Const MetaAnd, cs)
let mk_or ds = App (Const Or, ds)
let mk_eq (lhs, rhs) = App (Const Eq, [lhs; rhs])
let mk_neq (lhs, rhs) = mk_not (mk_eq(lhs,rhs))
let mk_seteq (lhs, rhs) = App (Const Seteq, [lhs; rhs])
let mk_subset (lhs, rhs) = App (Const Subset, [lhs; rhs])
let mk_subseteq (lhs, rhs) = App (Const Subseteq, [lhs; rhs])
let mk_lt (lhs, rhs) = App (Const Lt, [lhs; rhs])
let mk_gt (lhs, rhs) = App (Const Gt, [lhs; rhs])
let mk_lteq (lhs, rhs) = App (Const LtEq, [lhs; rhs])
let mk_gteq (lhs, rhs) = App (Const GtEq, [lhs; rhs])
let mk_impl (lhs, rhs) = App (Const Impl, [lhs; rhs])
let mk_metaimpl (lhs, rhs) = App (Const MetaImpl, [lhs; rhs])
let mk_iff (lhs, rhs) = App (Const Iff, [lhs; rhs])
let mk_forall(v,t,f) = Binder(Forall,[(v,t)],f)
let mk_foralls(vts,f) = Binder(Forall,vts,f)
let mk_exists(v,t,f) = Binder(Exists,[(v,t)],f)
let mk_existses(vts,f) = Binder(Exists,vts,f)
let mk_var v = Var v
let mk_string s = Const (StringConst s)


(** Make expression:
    let (v::t) = e in f *)
let mk_let e (v,t) f = App(Const Let,[e;Binder(Lambda,[(v,t)],f)])

let mk_def (v,f) = mk_eq(mk_var v,f)

let mk_fieldRead f x = App(Const FieldRead, [f;x])
let mk_fieldWrite f x y = App(Const FieldWrite,[f;x;y])

let mk_arrayLength arrObj = mk_fieldRead arrayLengthVar arrObj
let mk_arrayRead arr arrObj index = 
  App(Const ArrayRead,[arr;arrObj;index])
let mk_arrayRead1 arrObj index = mk_arrayRead arrayStateVar arrObj index
let mk_arrayWrite arr arrObj index v =
  App(Const ArrayWrite,[arr;arrObj;index;v])

let mk_arrayWrite1 arrObj index v =
  App(Const ArrayWrite,[arrayStateVar;arrObj;index;v])

let mk_null = Const NullConst

let mk_plus (lhs, rhs) = App (Const Plus, [lhs; rhs])
let mk_uminus x = App(Const UMinus, [x])
let mk_minus (lhs, rhs) = App (Const Minus, [lhs; rhs])
let mk_mult (lhs, rhs) = App (Const Mult, [lhs; rhs])
let mk_div (lhs, rhs) = App (Const Div, [lhs; rhs])
let mk_mod (lhs, rhs) = App (Const Mod, [lhs; rhs])

let mk_elem(lhs,rhs) = App(Const Elem, [lhs;rhs])
let mk_notelem(lhs,rhs) = mk_not(mk_elem(lhs,rhs))
let mk_setdiff(lhs,rhs) = App(Const Diff, [lhs;rhs])
let mk_cup(lhs,rhs) = App(Const Cup, [lhs;rhs])
let mk_cap(lhs,rhs) = App(Const Cap, [lhs;rhs])
let mk_finite_set fs = App(Const FiniteSetConst, fs)
let mk_emptyset = Const EmptysetConst
let mk_singleton x = mk_finite_set [x]

let mk_tuple fs = App(Const Tuple, fs)

let mk_singleton_relation (id1 : ident) (id2 : ident) : form =
  mk_singleton (mk_tuple [mk_var id1; mk_var id2])

let mk_list fs = App(Const ListLiteral, fs)

let mk_old f = App(Const Old, [f])

let mk_objlocs f = App(Const ObjLocs, [f])

let mk_typedform(f,t) = TypedForm(f,t)
let mk_typevar id = TypeVar (String.sub id 1 (String.length id - 1))
let mk_ite (f1, f2, f3) = App(Const Ite, [f1;f2;f3])

let mk_unit = Const Unit

(** Attempt to insert comments into formulas. *)
let mk_comment s f = 
  if s="" then f 
  else App(Const Comment,[Const (StringConst s);f])

(** Strip types from formula. *)

let dummify_tv (v,t) = (v,TypeUniverse)
let rec strip_types (f : form) : form = match f with
  | App(f1,fs) -> App(strip_types f1, List.map strip_types fs)
  | Binder(b,tvs,f1) -> 
      Binder(b,List.map dummify_tv tvs, strip_types f1)
  | Var _ -> f
  | Const _ -> f
  | TypedForm(f1,t) -> strip_types f1

let strip_sq_types (fs,f) = 
  (List.map strip_types fs, strip_types f)

(** Smart type makers. *)

let mk_unit_type = TypeApp(TypeUnit,[])
let mk_int_type = TypeApp(TypeInt,[])
let mk_string_type = TypeApp(TypeString, [])
let mk_bool_type = TypeApp(TypeBool,[])
let mk_object_type = TypeApp (TypeObject,[])

let mk_fun_type arg_tys res_ty =
  match res_ty with
  | TypeFun (arg_tys', res_ty') -> TypeFun (arg_tys @ arg_tys', res_ty')
  |  _ -> TypeFun (arg_tys, res_ty)

let mk_class_type (name : string) : typeForm =
(* TypeApp(TypeDefined name,[]) *)
  mk_object_type

let mk_set_type (t : typeForm) : typeForm =
  TypeApp(TypeSet,[t])

let mk_list_type (t : typeForm) : typeForm =
  TypeApp (TypeList, [t])

let mk_map (it : typeForm) (et : typeForm) : typeForm =
  TypeApp(TypeArray,[it;et])

let mk_array (et : typeForm) : typeForm =
  mk_map mk_int_type et

let mk_field_type (t : typeForm) : typeForm =
  mk_map mk_object_type t

let mk_state_array (et : typeForm) : typeForm =
  mk_field_type (mk_array et)

let mk_product_type (ts : typeForm list) : typeForm =
  TypeProd ts

let mk_type_from_ident (t : string) : typeForm =
  if t = "objset" then 
    mk_set_type mk_object_type
  else 
    TypeApp(TypeDefined t,[])

(** Make set comprehension defining a relation *)
let mk_relation_comprehension (v1,t1) (v2,t2) f = 
  let tids = [(v1,t1); (v2,t2)] in
  let ts = "p" in
  let mk_coord (v,t) = Var v in
  let tuple = mk_tuple (List.map mk_coord tids) in
    Binder(Comprehension,[(ts,mk_product_type [t1;t2])],
	   Binder(Exists,tids,
		  mk_and [mk_eq(Var ts,tuple);f]))


(** Free variables of a formula (this ignores types). *)

let fv (f:form) = 
  let add v bv acc = 
    if (List.mem v bv) || (List.mem v acc) 
    then acc
    else v::acc in
  let rec fv1 f bv acc = match f with
  | App(f1,fs) -> fv1 f1 bv (fv_list fs bv acc)
  | Binder(_,tvs,f1) -> fv1 f1 (List.rev_append (List.map fst tvs) bv) acc
  | Var v -> add v bv acc
  | Const _ -> acc
  | TypedForm(f1,t) -> fv1 f1 bv acc
  and fv_list fs bv acc = match fs with
  | [] -> acc
  | f::fs1 -> fv_list fs1 bv (fv1 f bv acc)
in fv1 f [] []

(** Free variables of a formula and a given type *)
let fv_by_type env tys f =
  List.filter (fun x -> 
    try List.mem (List.assoc x env) tys
    with Not_found -> Util.warn ("missing type for variable " ^ x); true) (fv f)

(** Substitution (ignores types). *)

type substMap = (ident * form) list

(** Naive substitution: ignores var capture. *)
let rec nsubst (m:substMap) (f:form) : form = 
  if m=[] then f else match f with
  | App(f1,fs) -> App(nsubst m f1, List.map (nsubst m) fs)
  | Binder(k,tvs,f1) -> 
      let not_bound (id,f) = not (List.mem_assoc id tvs) in
      let m1 = List.filter not_bound m in
      Binder(k,tvs,nsubst m1 f1)
  | Var v -> (try List.assoc v m with Not_found -> f)
  | Const _ -> f
  | TypedForm(f1,t) -> TypedForm(nsubst m f1,t)

(** Free variables of a substitution. *)
let fv_of_subst (m:substMap) =
  List.concat (List.map fv (List.map snd m))

(** Generating fresh variables. *)
let fresh_var_count = (ref 0 : int ref)
let fresh_var s = begin
  fresh_var_count := !fresh_var_count + 1; 
  s ^ (Printf.sprintf "__%d" !fresh_var_count)
end

(** Auxiliary for {!subst}.
    Computes 'renaming' for the variables that cause
    variable capture, and a new set
    of bound variables. *)
let rec capture_avoid 
    (vars : ident list)
    (tvs : typedIdent list)
    (subst_acc : substMap)
    (tvs_acc : typedIdent list) : (typedIdent list * substMap) =
  match tvs with
    | [] -> (List.rev tvs_acc, subst_acc)
    | (v,t)::tvs1 when (List.mem v vars) ->
	let fresh_v = fresh_var v in
	  capture_avoid vars tvs1 
            ((v,Var fresh_v)::subst_acc)
            ((fresh_v,t)::tvs_acc)
    | (v,t)::tvs1 ->
	capture_avoid vars tvs1 
          subst_acc
          ((v,t)::tvs_acc)

(** Capture-avoiding substitution. *)
let rec subst (m:substMap) (f:form) : form = 
  if m=[] then f 
  else match f with
    | App(f1,fs) -> App(subst m f1, List.map (subst m) fs)
    | Binder(k,tvs,f1) -> 
	let not_bound (id,f) = not (List.mem_assoc id tvs) in
	let m1 = List.filter not_bound m in
	  (** m1 is projection of substitution to 
	      variables that are not bound *)
	  if m1=[] then f
	  else 
            let (tvs1, renaming) = 
              capture_avoid (fv_of_subst m1) tvs [] [] in
            let f2 = if renaming=[] then f1 else nsubst renaming f1 in
              if tvs1=[] then f2 else
		Binder(k,tvs1,subst m1 f2)
    | Var v -> 
	(try List.assoc v m
	 with Not_found -> f)
    | Const _ -> f
    | TypedForm(f1,t) -> TypedForm(subst m f1,t)

(** Substituting subformulas. *)

type gsubstMap = (form * form) list

(** Naive substitution, ignores var capture.
    Substitution are tried on larger formulas first,
    and for a given formula substitutions earlier in map are tried first. *)
let rec ngsubst (m:gsubstMap) (f:form) : form = 
  if m=[] then f else
    try List.assoc f m with Not_found ->
      match f with
	| App(f1,fs) -> App(ngsubst m f1, List.map (ngsubst m) fs)
	| Binder(k,tvs,f1) ->
	    let vs = List.map fst tvs in
	    let not_bound (f_r,_) = 	      
	      List.for_all (fun x -> not (List.mem x (fv f_r))) vs in
	    let m1 = List.filter not_bound m in
	      Binder(k,tvs,ngsubst m1 f1)
	| Var _ -> f
	| Const _ -> f
	| TypedForm(f1,t) -> TypedForm(ngsubst m f1,t)

(** Check if formula contains the 'old' construct. *)
let rec contains_old (f : form) : bool = 
  match f with
    | App(Const Old, _) -> true
    | App(f1,fs) -> 
	List.exists contains_old (f1::fs)
    | Binder(k,tvs,f1) -> contains_old f1
    | Var _ -> false
    | Const _ -> false
    | TypedForm(f1,_) -> contains_old f1

(** Replace 'old' construct by pushing 
    it and renaming variables. *)

let oldname (s : string) = "old_" ^ s

let is_oldname (s : string) =
  (String.length s > 4) &&
    (String.sub s 0 4 = "old_")

let unoldname (s : string) =
  if is_oldname s then String.sub s 4 (String.length s - 4)
  else Util.fail ("unoldname of " ^ s)

let rec oldify
    (mkold : bool)
    (fvs : ident list) 
    (f0 : form) : form = 
  match f0 with
    | App(Const Old, [f1]) -> oldify true fvs f1
    | App(f1,fs) -> App(oldify mkold fvs f1, 
			List.map (oldify mkold fvs) fs)
    | Binder(k,tvs,f1) ->
	let not_bound v = not (List.mem_assoc v tvs) in
	let fvs1 = List.filter not_bound fvs in
	  Binder(k,tvs,oldify mkold fvs1 f1)
    | Var v -> 
	if mkold && (List.mem v fvs) then (Var (oldname v)) 
	else f0
    | Const _ -> f0
    | TypedForm(f1,t) -> TypedForm(oldify mkold fvs f1,t)

let transform_old (f : form) : form = oldify false (fv f) f

(* this somehow looks wrong... What is bound?  Why add fv f to it?! *)
let make_old_and_transform (f : form) (bound : ident list) : form = 
  oldify true (bound @ (fv f)) f

(** Add types to integer constants in a formula. *)
let type_int_consts (f0 : form) : form =
  let rec add (f : form) : form = match f with
    | TypedForm(Const (IntConst _),_) -> f
    | TypedForm(f1,t) -> TypedForm(add f1,t)
    | Const (IntConst _) -> TypedForm(f, mk_int_type)
    | Const _ -> f
    | Binder(k,vts,f1) -> Binder(k,vts,add f1)
    | App(f1,fs) -> App(add f1, List.map add fs)
    | Var _ -> f
  in 
  let res = add f0 in
    res

(** Smart constructors: construct a formula out of components and
    perhaps do some local simplifications. *)

let smk_not f =
  match f with
  | Const (BoolConst b) -> Const (BoolConst (not b))
  | App (Const Not, [f']) -> f'
  | _ -> mk_not f

let smk_forall (x,t,f) = 
  if List.mem x (fv f) then mk_forall(x,t,f)
  else f

let smk_foralls (xts,f) = 
  let fvs = fv f in
  let isfree (x,t) = List.mem x fvs in
  let useful = List.filter isfree xts in
    if useful=[] then f else 
    match f with
    | Binder (Forall, xts', f') -> mk_foralls(useful @ xts', f')
    | _ -> mk_foralls(useful, f)

let smk_exists (x,t,f) = 
  if List.mem x (fv f) then mk_exists(x,t,f)
  else f

let smk_exists (xts,f) = 
  let fvs = fv f in
  let isfree (x,t) = List.mem x fvs in
  let useful = List.filter isfree xts in
    if useful=[] then f else 
    match f with
    | Binder (Exists, xts', f') -> mk_existses(useful @ xts', f')
    | _ -> mk_existses(useful, f)

let smk_or fs = 
  let set_insert x xs = if List.mem x xs then xs else x::xs in
  let rec mkor1 fs acc = match fs with
  | [] -> 
      (match acc with
      | [] -> Const (BoolConst false)
      | [f] -> f
      | _ -> mk_or (List.rev acc))
  | App(Const Or,fs0) :: fs1 -> mkor1 (List.rev_append fs0 fs1) acc
  | Const (BoolConst false)::fs1 -> mkor1 fs1 acc
  | Const (BoolConst true)::fs1 -> Const (BoolConst true)
  | fs::fs1 -> mkor1 fs1 (set_insert fs acc)
  in mkor1 fs []

let smk_and fs = 
  let set_insert x xs = if List.mem x xs then xs else x::xs in
  let rec mkand1 fs acc = match fs with
    | [] -> (match acc with
	       | [] -> Const (BoolConst true)
	       | [f] -> f
	       | _ -> mk_and (List.rev acc))
    | App(Const And,fs0) :: fs1 -> mkand1 (fs0 @ fs1) acc
    | Const (BoolConst true)::fs1 -> mkand1 fs1 acc
    | Const (BoolConst false)::fs1 -> Const (BoolConst false)
    | fs::fs1 -> mkand1 fs1 (set_insert fs acc)
  in mkand1 fs []

let smk_metaand fs = 
  let set_insert x xs = if List.mem x xs then xs else x::xs in
  let rec mkand1 fs acc = match fs with
    | [] -> (match acc with
	       | [] -> Const (BoolConst true)
	       | [f] -> f
	       | _ -> mk_metaand (List.rev acc))
    | (App(Const And,fs0) :: fs1 
      | App(Const MetaAnd,fs0) :: fs1) -> mkand1 (List.rev_append fs0 fs1) acc
    | (App (Const Comment, [_; Const (BoolConst true)]) :: fs1
      | Const (BoolConst true)::fs1) -> mkand1 fs1 acc
    | (App (Const Comment, [_; Const (BoolConst false)]) :: fs1
      | Const (BoolConst false)::fs1) -> Const (BoolConst false)
    | fs::fs1 -> mkand1 fs1 (set_insert fs acc)
  in mkand1 fs []

let smk_eq (f0 : form) (f1 : form) : form =
  if (f0 = f1) then
    Const (BoolConst true)
  else
    mk_eq(f0, f1)

let smk_impl(f1,f2) = 
  match f1 with
    | Const (BoolConst false) -> Const (BoolConst true)
    | Const (BoolConst true) -> f2
    | App (Const And, fs) when List.mem f2 fs -> mk_true
    | _ -> (match f2 with
	      | App(Const Impl,[f2a;f2b]) -> mk_impl(smk_and [f1;f2a], f2b)
	      |	App(Const MetaImpl, [f2a; f2b]) -> mk_metaimpl (smk_metaand [f1;f2a], f2b)
(*	      | Const (BoolConst false) -> mk_not f1 - this is sound, but confusing *)
	      | Const (BoolConst true) -> f2
	      | _ -> mk_impl(f1,f2))

(** Normalize type formula *)
let rec normalize_type ty =
  match ty with
  | TypeApp (TypeArray, [ty1;ty2]) ->
      normalize_type (TypeFun ([ty1], ty2))
  | TypeApp (sty, tys) ->
      TypeApp (sty, List.map normalize_type tys)
  | TypeFun (tys, res_ty) ->
      let tys' = List.map normalize_type tys in
      let res_ty' = normalize_type res_ty in
      (match (tys', res_ty') with
      |	(_, TypeFun (tys'', res_ty'')) ->
	  normalize_type (TypeFun (tys' @ tys'', res_ty''))
      |	(_, TypeApp (TypeArray, [ty'';res_ty''])) ->
	  normalize_type (TypeFun (tys' @ [ty''], res_ty''))
      |	([], _) -> res_ty'
      |	_  -> TypeFun (tys', res_ty'))
  | TypeProd tys ->
      TypeProd (List.map normalize_type tys)
  | _ -> ty

(** Normalize formula for pattern matching up to depth [n]. *)
let normalize n f =
  let rec drop n f = match f with
  | Var _ | Const _ -> f
  | App (Const Comment, [_; f]) -> 
      drop n f 
  | App (t, ts) -> 
      if n = 0 then f
      else App (drop (n - 1) t, List.map (drop (n - 1)) ts)
  | Binder (b, vts, f') -> 
      if n = 0 then f 
      else Binder (b, vts, drop (n - 1) f')
  | TypedForm (f, _) -> drop n f
  in drop n f

(** Sequent is just a conjunction of formulas 
    that implies the conclusion. *)

type sequent = form list * form

let string_of_oblig (ob : obligation) = 
  Common.string_of_pos ob.ob_pos  ^ " : " ^ ob.ob_purpose ^ " := \n" ^
  PrintForm.wr_form ob.ob_form

let name_of_oblig (ob : obligation) = 
  Common.string_of_pos ob.ob_pos  ^ " : " ^ ob.ob_purpose

let form_of_sequent (fs,f) = 
  if fs=[] then f else mk_metaimpl(smk_metaand fs,f)

let sequent_of_form f =
  let rec add (hyps : (form * string list) list) (asms : form list) = match hyps with
  | [] -> asms
  | (App(Const And, fs), cs)::hyps1 
  | (App(Const MetaAnd, fs), cs)::hyps1 -> add ((List.map (fun f -> (f,cs)) fs) @ hyps1) asms
  | (App(Const Not, [App (Const Or, fs)]), cs)::hyps1 ->
      add (List.map (fun f -> (smk_not f, cs)) fs @ hyps1) asms
  | (App(Const Not, [App (Const Impl, [f1;f2])]), cs)::hyps1 ->
      add ((f1,cs)::(smk_not f2,cs)::hyps1) asms
  | (App(Const Not, [App (Const Not, [f])]),cs)::hyps1 ->
      add ((f,cs)::hyps1) asms
  | (App(Const Comment,[Const (StringConst c);f]),cs)::hyps1 -> 
      add ((f,c::cs)::hyps1) asms
  | (f,cs)::hyps1 -> 
      let hyp = mk_comment (String.concat "_" (List.rev cs)) f in
      add hyps1 (hyp::asms)
  in
  let rec gen asms f cs = match f with
  | App(Const Comment, [Const StringConst c; f1]) -> gen asms f1 (c::cs)
  | TypedForm (f1, _) -> gen asms f1 cs
  | App(Const Impl, [f1; f2])
  | App(Const MetaImpl,[f1;f2]) -> gen (add [(f1, [])] asms) f2 cs
  (* | Binder(Forall,vts,f1) -> gen (vts @ env) asms f1 *)
  | _ -> (List.rev asms, mk_comment (String.concat "_" (List.rev cs)) f)
  in gen [] f []

let string_of_sequent (sq:sequent) : string = 
(*  string_of_form (strip_types (form_of_sequent sq)) *)
  PrintForm.string_of_form (form_of_sequent sq)

(** Some simple formula simplification. *)

let rec simplify (f:form) = 
let res = (match f with
| App(f1,[]) -> simplify f1
| App(Const And,fs) -> smk_and (List.map simplify fs)
| App(Const Impl,[f1;f2]) -> smk_impl(simplify f1, simplify f2)
| Binder(Forall,vts,f1) -> smk_foralls(vts,f1)
| Var v -> f
| Const c -> f
| Binder(k,vts,f1) -> Binder(k,vts,simplify f1)
| App(f1,fs) -> App(simplify f1, List.map simplify fs)
| TypedForm(f1,t) -> TypedForm(simplify f1,t)) in
  (* print_string ("Original formula:\n" ^ isabelle_formula f ^ "\n simplified formula:\n" ^ isabelle_formula res ^ "\n"); *)
res

(** Hai's code for type inference in BAPA. *)

(*--------------------------------------------------
  some utility functions
  --------------------------------------------------*)

let is_set_type (t : typeForm) = match t with
  | TypeApp (TypeSet, _) -> true
  | _ -> false

let is_bool_type (t : typeForm) = match t with
  | TypeApp (TypeBool, _) -> true
  | _ -> false

let is_int_type (t : typeForm) = match t with
  | TypeApp (TypeInt, _) -> true
  | TypeApp (TypeDefined "int", _) -> true
  | _ -> false

let is_object_type (t : typeForm) = match t with
  | TypeApp (TypeDefined "Object", _) -> true
  | _ -> false

let get_defined_type_name (t : typeForm) = match t with
  | TypeApp (TypeDefined name, _) -> Some name
  | _ -> None

let is_same_type (t1 : typeForm) (t2 : typeForm) : bool =
  if (is_int_type t1 && is_int_type t2)
    || (is_set_type t1 && is_set_type t2)
    || (is_bool_type t1 && is_bool_type t2) 
    || (is_object_type t1 && is_object_type t2)
    || ((get_defined_type_name t1) = (get_defined_type_name t2))
  then
    true
  else
    false

let is_set_form (f : form) = match f with
  | TypedForm (_, t) -> is_set_type t
  | _ -> false

let is_bool_form (f : form) = match f with
  | TypedForm (_, t) -> is_bool_type t
  | _ -> false

let is_int_form (f : form) = match f with
  | TypedForm (_, t) -> is_int_type t
  | _ -> false

let is_object_form (f : form) = match f with
  | TypedForm (_, t) -> is_object_type t
  | _ -> false

let get_type (f : form) = match f with
  | TypedForm (_, t) -> t
  | _ -> failwith ("form:get_type: not TypedForm")

let get_form (f0 : form) = match f0 with
  | TypedForm (f, _) -> f
  | _ -> failwith ("form:get_form: not TypedForm")



let is_empty_set (f : form) = match f with
  | Const EmptysetConst -> true
  | _ -> false

exception FormulaTypeError of string

(** Extracting annotated types from formulas. *)

let merge_typing 
    (t1 : typedIdent list) 
    (t2 : typedIdent list) : typedIdent list =
  let add (v,t) vts =
    try (let t1 = List.assoc v vts in
	   (if normalize_type t1 <> normalize_type t && (ftv t1 = []) then 
	      Util.warn 
		("FormUtil.merge_typing: conflicting types for variable \"" ^ v ^
		   "\", types \"" ^ 
		   PrintForm.wr_type t1 ^ "\" and \"" ^
		   PrintForm.wr_type t ^ "\".")
	    else ()); vts)
    with Not_found -> (v,t)::vts 
  in
    List.fold_right add t1 t2

let merge_typings (ts : typedIdent list list) : typedIdent list = 
  List.fold_right merge_typing ts []

(** Extract the types of annoated free variables in a formula. *)
let get_annotated_types (f : form) : typedIdent list =
  let rec get_types (bound:ident list) (f:form) : typedIdent list = 
  match f with
  | App(f1,fs) -> 
      merge_typings (List.map (get_types bound) (f1::fs))
  | Binder(k,tvs,f1) ->
      let add_bound (v,t) vs = v::vs in
	get_types (List.fold_right add_bound tvs bound) f1
  | Var v -> []
  | Const _ -> []
  | TypedForm(Var v,t) -> if List.mem v bound then [] else [(v,t)]
  | TypedForm(f1,t) -> get_types bound f1
  in get_types [] f

(** Universally quantify typed free variables of a formula. *)
let forall_annotated_types (f : form) : form =
  smk_foralls(get_annotated_types f,f)

(** Compute order of a type *)
let order_of_type ty =
  let order_simple_type ty =
    match ty with
    | TypeUnit | TypeBool -> 0
    | TypeInt | TypeString
    | TypeObject | TypeSet -> 1
    | TypeList | TypeArray -> 1
    | TypeDefined _ -> raise (Invalid_argument "")
  in
  let rec order ty =
    match ty with
    | TypeApp (ty, tys) -> List.fold_left (fun m ty -> 
	max (order ty) m) 0 tys + order_simple_type ty
    | TypeFun (tys, ty) -> List.fold_left (fun m ty -> 
	max (order ty + 1) m) (order ty) tys
    | TypeProd tys -> List.fold_left (fun m ty -> 
	max (order ty) m) 0 tys
    | TypeUniverse | TypeVar _ -> raise (Invalid_argument "")
  in try Some (order ty) with Invalid_argument _ -> None

(** Remove type annotations in a formula up to depth [n] of syntax tree 
   (not counting TypedForm). Simplifies pattern matching of formulas *)
let unnotate_types n f =
  let rec drop n f = match f with
  | Var _ | Const _ -> f
  | App (t, ts) -> 
      if n = 0 then f
      else App (drop (n - 1) t, List.map (drop (n - 1)) ts)
  | Binder (b, vts, f') -> 
      if n = 0 then f 
      else Binder (b, vts, drop (n - 1) f')
  | TypedForm (f, _) -> drop n f
  in drop n f

(** Remove all type annotations in a formula *)
let unnotate_all_types = unnotate_types (-1)

(***************************************************)
(** Smart implications. Used to help e.g. BAPA. But there is a bug. *)
(***************************************************)

let extract_definitions1
    (cands : ident list)
    (f : form) : 
    (form list * substMap) =
  (* FIX: check that replaced variable is not on RHS anywhere
     else *)
  let rec extract 
      (cs : form list) (cs0 : form list) (m : substMap) =
    match cs with
      | [] -> (cs0, m)
      | (App(Const Eq,[lhs;rhs]) as c)::cs1 -> 
	  (let rec handle lhs rhs = match (lhs,rhs) with
	     | (Var v,rhs) ->
		 if List.mem v cands &&
		   not (List.mem v (fv rhs)) &&
		   not (List.mem_assoc v m)
		 then extract cs1 cs0 ((v,rhs)::m)
		 else extract cs1 (cs0 @ [c]) m
	     | (TypedForm(lhs1,_),_) -> handle lhs1 rhs
	     | (_,TypedForm(rhs1,_)) -> handle lhs rhs1
	     | (_, Var v) -> handle rhs lhs 
	     | (_,_) -> extract cs1 (cs0 @ [c]) m in
	     handle lhs rhs)
      | c::cs1 -> extract cs1 (cs0 @ [c]) m in
  let rec handle1 lhs rhs = match (lhs,rhs) with
    | (Var v,rhs) -> 
	if List.mem v cands  &&
	  not (List.mem v (fv rhs))
	then ([],[(v,rhs)])
	else ([f],[])
    | (TypedForm(lhs1,_),_) -> handle1 lhs1 rhs
    | (_,TypedForm(rhs1,_)) -> handle1 lhs rhs1
    | (_, Var v) -> handle1 rhs lhs 
    | (_,_) -> ([f],[])
  in match f with
    | App(Const Eq,[lhs;rhs]) -> handle1 lhs rhs
    | App(Const And, cs) ->
	extract cs [] []
    | _ -> ([f],[])

let extract_definitions (candidates : ident list) (f : form) :
    (form * substMap) =
  let (conjs,defs) = extract_definitions1 candidates f in
    (* ideally we would order defs in topological order if possible,
       but for now we just check that rhs do not contain any lhs in
       defs *)
  let vars = List.map (fun (v,f) -> v) defs in
  let rec check (ds : substMap) (ds0 : substMap) (cs0 : form list) =
    match ds with
      | [] -> (subst ds0 (smk_and cs0), ds0)
      | (v,f)::ds1 -> 
	  if Util.disjoint (fv f) vars then check ds1 ((v,f)::ds0) cs0
	  else check ds1 ds0 (mk_def (v,f)::cs0)
  in check defs [] conjs

let smk_fixand_eq 
    (candidates : ident list)
    (f : form) : form =
  let (f1p,defs) = extract_definitions candidates f in
    smk_and ([subst defs f1p])

let smk_impl_eq 
    (candidates : ident list) 
    ((f1,f2) : form * form) : form =
  let (f1p,defs) = extract_definitions candidates f1 in
    smk_impl(f1p,subst defs f2)

let smk_impl_eq2
    (candidates : ident list) 
    (excands : ident list)
    ((f1,f2) : form * form) : form =
  let (f1p,defs) = extract_definitions candidates f1 in
    smk_impl(f1p,subst defs (smk_fixand_eq excands f2))

let rec no_binder (f : form) : bool = 
  match f with
    | Binder(_,_,_) -> false
    | App(f1,fs) -> 
	no_binder f1 && nos_binder fs    
    | Var _ -> true
    | Const _ -> true
    | TypedForm(f1,t) -> no_binder f1
and nos_binder (fs : form list) : bool =
  match fs with
    | [] -> true
    | f::fs1 -> no_binder f && nos_binder fs1

let rec lambda_or_no_binder (f : form) : bool =
  match f with 
    | Binder(Lambda,_,_) -> true
    | App(Const Comment,[Const (StringConst c);f1]) -> lambda_or_no_binder f1
    | _ -> no_binder f


(** Create formula representing (fdef --> f0).
    fdef is assumed to have the form of list of equalities v=rhs.
    When substitute_formula rhs is true, then equality is substituted,
    otherwise it is conjoined.
*)

let smk_impl_def_eq
    (substitute_formula : form -> bool)
    ((fdefs, f0) : form * form) : form =
  let rec dapply fs f =
    match fs with
      | [] -> f
      | fdef::fs1 ->
	  (match fdef with
	     | App(Const Eq,[Var v;rhs]) 
	     | App(Const Eq, [TypedForm (Var v, _); rhs]) ->
		 if substitute_formula rhs then
		   if not (List.mem v (fv (mk_and (f::fs1)))) then
		     (debug_lmsg 4 (fun () -> "Dropped definition of variable " ^ v ^ " because it does not appear anywhere.");
		     dapply fs1 f)
		   else 
		     (let sub = subst [(v,rhs)] in		     
			dapply (List.map sub fs1) (sub f))
		 else dapply fs1 (smk_impl(fdef,f))
	     | _ -> 
		 (Util.warn 
		    ("formUtil.smk_impl_def_eq: Found a non-equality " ^ PrintForm.string_of_form fdef ^"\nrepresented as:" ^
		       MlPrintForm.string_of_form fdef);
		  dapply fs1 (smk_impl(fdef,f))))
  in
  let _ = debug_lmsg 4 (fun () -> "\nsmk_impl_def_eq fdefs = " ^ MlPrintForm.string_of_form fdefs ^ "\n") in
    match fdefs with
      | Const (BoolConst true) -> f0
      | App(Const And,fs) -> dapply fs f0
      | _ -> dapply [fdefs] f0

let fresh_tv_counter = ref 0
let get_fresh_tv id =
  (fresh_tv_counter := !fresh_tv_counter + 1;
   Printf.sprintf "%s_%d" id !fresh_tv_counter)

(** Replace type variables in a formula with fresh type variables. *)
let fresh_type_vars t0 =
  let (subst : (ident * ident) list ref) = ref [] in
  let process_tvar (tvar : ident) =
    try List.assoc tvar !subst 
    with Not_found ->
      (let fresh = get_fresh_tv tvar in
	 subst := (tvar,fresh) :: !subst;
	 fresh)
  in
  let rec walk t = match t with
      | TypeUniverse -> t
      | TypeVar tv -> TypeVar (process_tvar tv)
      | TypeApp(t1,ts) -> TypeApp(t1,List.map walk ts)
      | TypeFun(ts,t1) -> TypeFun(List.map walk ts,walk t1)
      | TypeProd ts -> TypeProd (List.map walk ts)
  in 
    walk t0

(** Extract as string all first arguments of Comment constant. *)
let extract_comments (f : form) : string =
  let rec extract (f : form) (acc : string list) =
    match f with
      | App(Const Comment,[Const (StringConst s);farg]) ->
	  extract farg (s::acc)
      | Var _ -> acc
      | Const _ -> acc
      | App(f1,fs) -> 
	  List.fold_right extract (f1::fs) acc
      | Binder(k,tvs,f1) -> extract f1 acc	  
      | TypedForm(f1,t) -> extract f1 acc
  in
    String.concat "; " (extract f [])

let form_to_oblig (f : form) : obligation = { 
  ob_pos = Common.unknown_pos;
  ob_purpose = "";
  ob_form = f
}

let form_to_sqob (f : form) : sq_obligation = { 
  sqob_pos = Common.unknown_pos;
  sqob_purpose = "";
  sqob_sq = ([],f)
}

(** Remove lambda abstractions (currently only beta reduction) *)
let rec unlambda (f : form) =
  let box_result new_ty f res =
    match f with
    | TypedForm (_, old_ty) -> TypedForm (res, new_ty old_ty)
    | _ -> res
  in
  match f with
  | App (Const Elem, [t; Binder (Comprehension, vs, bf)]) 
  | App (Const Elem, [t; TypedForm (Binder (Comprehension, vs, bf), _)]) ->
      let t' = unlambda t in
      let ts = match normalize 1 t' with
      |	App (Const Tuple, ts) -> ts 
      |	_ -> [t']
      in
      (try 
	let sigma = List.fold_right2 
	    (fun (v, _) t acc -> (v, t)::acc)
	    vs ts [] 
	in unlambda (subst sigma bf)
      with Invalid_argument _ ->
	let bf' = unlambda bf in
	App (Const Elem, [t'; Binder (Comprehension, vs, bf')]))
  | App (Const FieldRead, [fld]) -> unlambda fld
  | App (Const FieldRead, fld::fs) -> unlambda (App (fld, fs))
  | App (Binder (Lambda, vs, t) as head, args) |
    App (TypedForm (Binder (Lambda, vs, t), _) as head, args) ->
      let vs', sigma, args' = 
	List.fold_left (function 
	  | ((v, _)::vs', sigma, _) -> fun t -> (vs', (v, t)::sigma, [])
	  | ([], sigma', args') -> fun t -> ([], sigma', t::args')) (vs, [], []) args
      in
      let t' = unlambda (subst (List.rev sigma) t) in
      let new_ty ty = 
	let res_ty = match ty with
	| TypeApp (TypeArray, [_; res_ty]) -> res_ty
	| TypeFun (_, res_ty) -> res_ty
	| _ -> ty
	in
	normalize_type (TypeFun (List.map snd vs', res_ty))
      in
      if vs' = [] then if args' = [] then t'
      else unlambda (App (box_result new_ty head t', List.rev args'))
      else box_result new_ty head (Binder (Lambda, vs', t'))
  | App (t, ts) -> 
      let t' = unlambda t in
      (match t' with
      |	Binder _ | TypedForm (Binder _, _) -> unlambda (App (t', ts))
      |	_ -> App (t', List.map unlambda ts))
  | Binder (b, vs, t) -> Binder (b, vs, unlambda t)
  | TypedForm (f', ty) -> TypedForm (unlambda f', ty)
  | _ -> f
     
(** reduce formulas such that (ALL f g. reduce f = reduce g <-> equal f g).
   This means that equal/reduce can be used for hashing of formulas *)
let reduce (f : form) : form =
  let c = ref 0 in
  let fv_f = fv f in
  let rec fresh_var replace_map x = 
    let new_x = Printf.sprintf "x%d" !c in
    c := !c + 1;
    if List.mem new_x fv_f then fresh_var replace_map x 
    else ((x, new_x)::replace_map, new_x)
  in
  let get_name replace_map x =
    try List.assoc x replace_map
    with Not_found -> x
  in
  let rec reduce replace_map f =
    match f with
    | App (Const UMinus, [Const (IntConst i)]) 
    | App (Const UMinus, [TypedForm (Const (IntConst i), _)]) ->
	Const (IntConst (-1 * i))
    | Const _ -> f
    | Var x -> mk_var (get_name replace_map x)
    | App (Const FieldRead, [f; t]) -> App (reduce replace_map f, [reduce replace_map t])
    | App (Const Comment, [_; f1]) -> reduce replace_map f1 
    | App (Const And, [f1]) | App (Const Or, [f1]) -> reduce replace_map f1
    | App (f, fs) -> App (reduce replace_map f, List.map (reduce replace_map) fs)
    | TypedForm (f, ty) -> reduce replace_map f
    | Binder (b, xs, f) ->
	let replace_map', xs' = List.fold_right 
	    (fun (x, ty) (replace_map, xs') -> 
	      let replace_map', x' = fresh_var replace_map x in
	      (replace_map', (x', normalize_type ty)::xs')) 
	    xs (replace_map, [])
	in
	let f' = reduce replace_map' f in
	Binder (b, xs', f')
  in reduce [] f


(** Check syntactic equality of formulas up to alpha renaming 
   of bound variables, type annotations, and some other symmetries 
   which can be checked in linear time. *)
let equal (f1 : form) (f2 : form) : bool =
  let rec eq sigma f1 f2 =
    match (f1, f2) with
    | (App (Const UMinus, [Const (IntConst i1)]), (Const (IntConst i2))) 
    | (Const (IntConst i2), App (Const UMinus, [Const (IntConst i1)])) ->
	(-1 * i1) = i2
    | (Const c1, Const c2) -> c1 = c2
    | (Var x1, Var x2) ->
	let x1' = 
	  try List.assoc x1 sigma 
	  with Not_found -> x1
	in x1' = x2
    | (App (Const FieldRead, [f; x]), _) -> eq sigma (App (f, [x])) f2
    | (_, App (Const FieldRead, [f; x])) -> eq sigma f1 (App (f, [x]))
    | (App (Const Comment, [f1']), _) -> eq sigma f1' f2
    | (_, App (Const Comment, [f2'])) -> eq sigma f1 f2'
    | (App (Const And, [f1']), _)
    | (App (Const Or, [f1']), _) -> eq sigma f1' f2
    | (_, App (Const And, [f2']))
    | (_, App (Const Or, [f2'])) -> eq sigma f1 f2'  
    | (App (g1, gs1), App (g2, gs2)) ->
	(try 
	  List.for_all2 (eq sigma) (g1::gs1) (g2::gs2)
	with Invalid_argument _ -> false)
    | (Binder (b1, bvs1, g1), Binder (b2, bvs2, g2)) ->
	(try
	  let sigma', same_types = 
	    List.fold_left2 (fun (sigma', same_types) (x1, ty1) (x2, ty2) ->
	      if normalize_type ty1 = normalize_type ty2 then
		((x1, x2)::sigma', same_types)
	      else (sigma', false)) (sigma, true) bvs1 bvs2
	  in
	  b1 = b2 && same_types && eq sigma' g1 g2
	with Invalid_argument _ -> false)
    | (TypedForm (f1', _), _) -> eq sigma f1' f2
    | (_, TypedForm (f2', _)) -> eq sigma f1 f2'
    | _ -> false
  in 
  eq [] f1 f2



(** A hash table module using formulas as hash keys *)
module FormHashtbl = 
  Hashtbl.Make(struct 
    type t = form
    let equal = equal
    let hash f = Hashtbl.hash (reduce f)
  end)

(** Compute negation normal form of a formula *)
let rec negation_normal_form (f : form) : form =
  match f with
    | App(Const Not, [Const (BoolConst true)]) -> Const (BoolConst false)
    | App(Const Not, [Const (BoolConst false)]) -> Const (BoolConst true)
    | App(Const Not, [App(Const Not, [f1])]) -> negation_normal_form f1
    | App(Const Not, [Binder(Forall, til, f1)]) -> 
	Binder(Exists, til, negation_normal_form(App(Const Not, [f1])))
    | App(Const Not, [Binder(Exists, til, f1)]) ->
	Binder(Forall, til, negation_normal_form(App(Const Not, [f1])))
    | App(Const Not, [App(Const And, fs)]) ->
        let fs1 = List.map (fun (x) -> negation_normal_form (App(Const Not, [x]))) fs in
	smk_or fs1
    | App(Const Not, [App(Const Or, fs)]) ->
	let fs1 = List.map (fun (x) -> negation_normal_form (App(Const Not, [x]))) fs in
	smk_and fs1
    | App(Const Not, [App(Const Impl, [f1; f2])]) ->
	let f3 = negation_normal_form f1 in
	let f4 = negation_normal_form (mk_not f2) in
	smk_and [f3; f4]
    | App(Const Not, [App(Const Iff, [f1; f2])]) ->
	let f3 = App(Const Impl, [f1; f2]) in
	let f4 = App(Const Impl, [f2; f1]) in
	  negation_normal_form (App(Const Not, [App(Const And, [f3; f4])]))
    | App(Const Not, [App(Const Eq, [Const (BoolConst true); f0])])
    | App(Const Not, [App(Const Eq, [f0; Const (BoolConst true)])])
    | App(Const Eq, [Const (BoolConst false); f0])
    | App(Const Eq, [f0; Const (BoolConst false)]) ->
	negation_normal_form (App(Const Not, [f0]))
    | App(Const Not, [App(Const Eq, [Const (BoolConst false); f0])])
    | App(Const Not, [App(Const Eq, [f0; Const (BoolConst false)])])
    | App(Const Eq, [Const (BoolConst true); f0])
    | App(Const Eq, [f0; Const (BoolConst true)]) ->
	negation_normal_form f0
    | App(Const Not, [App(Const Lt, [f0; f1])]) ->
	App(Const GtEq, [f0; f1])
    | App(Const Not, [App(Const Gt, [f0; f1])]) ->
	App(Const LtEq, [f0; f1])
    | App(Const Not, [App(Const LtEq, [f0; f1])]) ->
	App(Const Gt, [f0; f1])
    | App(Const Not, [App(Const GtEq, [f0; f1])]) ->
	App(Const Lt, [f0; f1])
    | App(Const Impl, [f1; f2]) ->
	let f3 = negation_normal_form(App(Const Not, [f1])) in
	let f4 = negation_normal_form f2 in
	App(Const Or, [f3; f4])
    | App(Const Iff, [f1; f2]) ->
	let f3 = App(Const Impl, [f1; f2]) in
	let f4 = App(Const Impl, [f2; f1]) in
	  negation_normal_form (App(Const And, [f3; f4]))
    (* | App(Const Ite, _) ->
	failwith ("negation_normal_form: Can't handle " ^ (PrintForm.string_of_form f)) *)
    | App(f1, fs) -> 
	App((negation_normal_form f1), (List.map negation_normal_form fs))
    | Binder(b, til, f) -> Binder(b, til, (negation_normal_form f))
    | TypedForm(f, ty) -> TypedForm (negation_normal_form f, ty) 
    | _ -> f

(** Apply substitutions to a formula in appropriate order,
    assuming they are acyclic.  Used to apply shorthands and variable definitions. *)

let apply_defs 
    (defs : (ident * form) list)
    (f : form) : form =
  let app_to_form (id_def,f_def) f =
    subst [(id_def,f_def)] f in
  let app_to_def (id_def,f_def) (id,f) =
    (id, app_to_form (id_def,f_def) f) in
  let good_def (id,fid) = not (List.mem id (fv fid)) in
  let rec appdef defs f =
    match defs with
      | [] -> f
      | (id,fid)::defs1 ->
	  if List.mem id (fv f) then
	    if good_def (id,fid) then
	      (debug_msg ("*** FormUtil.apply_defs: expanding " ^ id ^ "\n");
	       appdef 		  
		 (List.map (app_to_def (id,fid)) defs1)
		 (app_to_form (id,fid) f))
            else
	      (Util.warn ("Cycle in definitions:\n  " ^ id ^ " == " ^
			    PrintForm.string_of_form fid);
	       f)
	  else (debug_msg ("apply_defs: no ocurrences of " ^ id ^ ".\n");
		appdef defs1 f)
  in
  let _ = debug_msg ("Before apply_defs: " ^ PrintForm.string_of_form f ^ "\n DEFS:") in
  let _ = List.iter (fun (id,f) -> debug_msg (id ^ " ")) defs in
  let _ = debug_msg "\n"; flush_all() in
  let f1 = appdef defs f in
  let _ = debug_msg ("After apply_defs: " ^ PrintForm.string_of_form f1 ^ "\n") in
    appdef defs f

(*
let apply_defs_possibly_old
    (defs : (ident * form) list)
    (f : form) : form =
  let make_old ((id,f1):(ident * form)) : (ident * form) =
    (oldname id, oldify true (fv f1) f1) in
  let defs1 = List.map make_old defs in
    apply_defs (defs1 @ defs) f
*)

(* Conjoin definitions of variables on which formula depends.
let conjoin_defs
    (defs : (ident * form) list)
    (f : form) : form =
  let app_to_form (id_def,f_def) f =
    subst [(id_def,f_def)] f in
  let app_to_def (id_def,f_def) (id,f) =
    (id, app_to_form (id_def,f_def) f) in
  let good_def (id,fid) = not (List.mem id (fv fid)) in
  let def_to_eq (id,fid) = mk_eq(mk_var id,fid) in
  let rec get_fresh_sub
      (defs : (ident * form) list)
      (sub : (ident * form) list) : (ident * form) list =
    match defs with
      | [] -> sub
      | ((id,f)::defs1) ->
	  (let id_f = fresh_var id in
	     get_fresh_sub defs1 ((id,mk_var id_f)::sub))
  in
  let rec condef defs to_reconsider fvs fdefs =
    match defs with
      | [] -> 
	  (let sub = get_fresh_sub fdefs [] in
	   let f1 = smk_impl(smk_and (List.map def_to_eq fdefs),f) in
	     subst sub f1
	  )
      | (id,fid)::defs1 ->
	  if List.mem id fvs then
	    (debug_msg ("*** FormUtil.apply_defs: expanding " ^ id ^ "\n");
	     condef
	       (defs1 @ to_reconsider)
	       []
	       ((fv fid) @ (Util.difference fvs [id]))
	       ((id,fid)::fdefs))
	  else (debug_msg ("apply_defs: no ocurrences of " ^ id ^ ".\n");
		condef defs1 to_reconsider fvs fdefs)
  in
  let _ = debug_lmsg 0 (fun () -> "Before conjoin_defs: " ^ PrintForm.string_of_form f ^ "\n DEFS:") in
  let _ = List.iter (fun (id,f) -> debug_msg (id ^ " ")) defs in
  let _ = debug_msg "\n"; flush_all() in
  let f1 = condef defs [] (fv f) [] in
  let _ = debug_lmsg 0 (fun () -> "After conjoin_defs: " ^ PrintForm.string_of_form f1 ^ "\n") in
   f1

let conjoin_defs_possibly_old
    (defs : (ident * form) list)
    (f : form) : form =
  let make_old ((id,f1):(ident * form)) : (ident * form) =
    (oldname id, oldify true (fv f1) f1) in
  let defs1 = List.map make_old defs in
    conjoin_defs (defs1 @ defs) f
*)

let points_to_name = "pointsto"
let points_to_name_f = mk_var points_to_name

let mk_points_to (a : form) (f : form) (b : form) : form =
  App(points_to_name_f, [a; f; b])

let mk_points_to_expansion : form -> form -> form -> form =
  let xid = fresh_var "x" in
  let xvar = mk_var xid in
  fun (a : form) (f : form) (b : form) ->
    mk_forall(xid,mk_object_type,
	      mk_impl(mk_elem(xvar,a),
		      mk_elem(mk_fieldRead f xvar, b)))

(** Eliminate quantifiers and minimize scopes *)
let elim_quants f =
  let rec split_conjuncts f =
    match f with
    | App (Const And, fs) | App (Const MetaAnd, fs) -> 
	List.concat (List.rev_map split_conjuncts fs)
    | _ -> [f]
  in
  let elim_vars candidates fs =
    let rec elim fs fs' sigma =
      let substitute (v, t as sb) fs fs' sigma =
	let sub = subst [sb] in
	elim (List.map sub fs) (List.map sub fs') (sb :: List.map (fun (v, t) -> (v, sub t)) sigma)
      in
      match fs with
      | [] -> fs', sigma
      | f::fs ->
	  match normalize 2 f with
	  | App (Const Eq, [Var v1; Var v2]) 
	  | App (Const Seteq, [Var v1; Var v2]) ->
	      if List.mem v2 candidates then
		substitute (v2, Var v1) fs fs' sigma
	      else if List.mem v1 candidates then
		substitute (v1, Var v2) fs fs' sigma
	      else elim fs (f::fs') sigma
	  | App (Const Eq, [Const (BoolConst true); rhs])
	  | App (Const Eq, [rhs; Const (BoolConst true)]) ->
	      elim (rhs::fs) fs' sigma
	  | App (Const Eq, [Var v; rhs])
	  | App (Const Eq, [rhs; Var v])
	  | App (Const Seteq, [rhs; Var v])
	  | App (Const Seteq, [Var v; rhs])
	  | App (Const Iff, [Var v; rhs])
	  | App (Const Iff, [rhs; Var v])
	    when List.mem v candidates && not (List.mem v (fv rhs)) ->
	      substitute (v, rhs) fs fs' sigma
	  | Var v when List.mem v candidates ->
	      substitute (v, mk_true) fs fs' sigma
	  | App (Const Not, [Var v]) when List.mem v candidates ->
	      substitute (v, mk_false) fs fs' sigma
	  | _ -> elim fs (f::fs') sigma
    in elim fs [] []
  in
  let rec minimize f =
    match f with
    | Const _ | Var _ -> f 
    | App (f0, args) -> 
	App (minimize f0, List.map minimize args)
    | Binder (Comprehension as b, vs, f0)
    | Binder (Lambda as b, vs, f0) -> 
	Binder (b, vs, minimize f0)
    | Binder (Forall, vs, f0) ->
	(match f0 with 
	| App (Const Impl, [f;g])
	| App (Const MetaImpl, [f;g]) ->
	    let fs', sigma = elim_vars (List.rev_map fst vs) (split_conjuncts f) in
	    smk_foralls (vs, minimize (smk_impl (smk_and fs', subst sigma g)))
	| App (Const And, fs) ->
	    smk_and (List.rev_map (fun f -> minimize (mk_foralls (vs, f))) fs)
	| _ -> smk_foralls (vs, minimize f0))
    | Binder (Exists, vs, f0) ->
	(match f0 with
	| App (Const Or, fs) ->
	    smk_or (List.rev_map (fun f -> minimize (mk_existses (vs, f))) fs)
	| _ ->
	    let fs, _ = elim_vars (List.rev_map fst vs) (split_conjuncts f0) in
	    smk_exists (vs, minimize (smk_and fs)))
    | TypedForm (f0, ty) -> TypedForm (minimize f0, ty)
  in minimize f

(** Eliminate free variables *)
let elim_free_vars keep_bool prefered ((fs, g) : sequent) : sequent * substMap =
  let rec elimfree fs fs' g' sigma =
    let substitute (v, t as sb) fs fs' g' sigma =
      let sub = subst [sb] in
      elimfree (List.map sub fs) (List.map sub fs') (sub g') 
	(sb :: List.map (fun (v, t) -> (v, sub t)) sigma)
    in
    match fs with
    | [] -> (fs', g'), sigma
    | f::fs ->
	match normalize 2 f with
	| App (Const Eq, [Const (BoolConst true); rhs])
	| App (Const Eq, [rhs; Const (BoolConst true)]) ->
	    elimfree (rhs::fs) fs' g' sigma
	| App (Const Eq, [Var v1; Var v2]) ->
	    if not (List.mem v2 prefered) then
	      substitute (v1, Var v2) fs fs' g' sigma
	    else substitute (v2, Var v1) fs fs' g' sigma
	| App (Const Eq, [Var v; rhs])
	| App (Const Eq, [rhs; Var v])
	| App (Const Seteq, [rhs; Var v])
	| App (Const Seteq, [Var v; rhs])
	| App (Const Iff, [Var v; rhs])
	| App (Const Iff, [rhs; Var v]) 
	  when not (List.mem v (fv rhs)) &&
	    (List.mem v prefered || 
	    not (List.exists (fun v -> List.mem v (fv rhs)) prefered)) ->
	    substitute (v, rhs) fs fs' g' sigma
	| Var v 
	  when not keep_bool ->
	    substitute (v, mk_true) fs fs' g' sigma
	| App (Const Not, [Var v]) 
	  when not keep_bool ->
	    substitute (v, mk_false) fs fs' g' sigma
	| _ -> elimfree fs (f::fs') g' sigma
  in elimfree fs [] g []


let elim_fv_in_seq keep_bool (s : sequent) : sequent = 
  fst (elim_free_vars keep_bool [] s)

(** names of variables used as constants *)
let str_rtrancl = "rtrancl_pt"
let str_tree = "tree"

let pseudo_constants = [str_rtrancl; str_tree]

(** field constraints *)

let field_constraint f = 
  match normalize 5 f with
  | Binder (Forall, [(x1, _) as v1; (y1, _) as v2], 
	    App(Const Impl, [App (Const Eq, [App (Var fld, [Var x2]); Var y2]); _]))
    when x1 = x2 && y1 = y2 ->
      (match f with
      |	Binder (Forall, _, App(Const Impl, [_; fld_def])) -> Some (fld, v1, v2, fld_def)
      |	_ -> None)
  | _ -> None  

let is_tree_constraint f =
  match normalize 3 f with
  | App (Var str_tree, [App (Const ListLiteral, _)]) -> true
  | _ -> false
  
let is_field_constraint f = 
  match field_constraint f with
  | None -> false
  | Some _ -> true

(** Abstract away given constructs to prevent reasoner from getting confused *)
let abstract_constructs (constrs : string list) (f0 : form) : form =
  let rec abst f =
    match f with
      | App(Var v,f1) when List.mem v constrs ->
	  let fvs = fv (mk_and f1) in
	  let unv = fresh_var v in
	    App(Var unv,List.map mk_var fvs)
      | App(TypedForm(Var v,t),f1) when List.mem v constrs ->
	  let fvs = fv (mk_and f1) in
	  let unv = fresh_var v in
	    App(TypedForm(Var unv,t),List.map mk_var fvs)
      | App(Const c,f1) when List.mem (string_of_const c) constrs ->
	  let fvs = fv (mk_and f1) in
	  let unv = fresh_var (string_of_const c) in
	    App(Var unv,List.map mk_var fvs)
      | App(TypedForm(Const c,t),f1) when List.mem (string_of_const c) constrs ->
	  let fvs = fv (mk_and f1) in
	  let unv = fresh_var (string_of_const c) in
	    App(TypedForm(Var unv,t),List.map mk_var fvs)
      | App(f1,f2) -> App(abst f1, List.map abst f2)
      | Var _ -> f
      | Const _ -> f
      | Binder(k,tvs,f1) -> Binder(k,tvs,abst f1)
      | TypedForm(f1,t) -> TypedForm(abst f1,t)
  in
  abst f0

(** Improved version of abstract_constructs. Allows abstracttion of partially applied functions 
   and uses common subterm replacement *)
let smart_abstract_constructs (constrs : (form * int) list) (f0 : form) : form =
  let replace_map = Hashtbl.create 0 in
  let rec consume i acc ts tys_opt =
    if i = 0 then (List.rev acc, ts, tys_opt) else
    match ts with
    | t::ts -> consume (i - 1) (t::acc) ts (Util.optmap List.tl tys_opt)
    | _ -> (List.rev acc, ts, tys_opt)
  in
  let replace (f : form) (fs : form list) =
    try Hashtbl.find replace_map (f, fs) 
    with Not_found ->
      let newv = mk_var (get_fresh_tv "v_") in
      Hashtbl.add replace_map (f, fs) newv; newv
  in
  let rec abst (f : form) : form =
    match f with
    | Const _ 
    | Var _  ->
	if List.exists (fun (f', _) -> f' = f) constrs 
	then replace f [] 
	else f
    | App (TypedForm (f1, ty), fs) when
	List.exists (function (f', _) -> f1 = f') constrs 
      ->
	let tys, res_ty = match normalize_type ty with
	| TypeFun (tys, res_ty) -> (tys, res_ty)
	| ty -> ([], ty)
	in
	let i = List.assoc f1 constrs in
	let consumed_fs, remaining_fs, remaining_tys =
	  consume i [] fs (Some tys)
	in 
	let f' = replace f1 consumed_fs in
	let ty' = normalize_type (TypeFun (Util.unsome remaining_tys, res_ty)) in
	(match remaining_fs with
	| [] -> TypedForm (f', res_ty)
	| _ -> App (TypedForm (f', ty'), List.map abst remaining_fs))
    | App (f1, fs) when 
	List.exists (function (f', _) -> f1 = f') constrs 
      ->
	let i = List.assoc f1 constrs in
	let consumed_fs, remaining_fs, _ =
	  consume i [] fs None
	in 
	let f' = replace f1 consumed_fs in
	(match remaining_fs with
	| [] -> f'
	| _ -> App (f', List.map abst remaining_fs))
    | App (f1, fs) ->
	App (abst f1, List.map abst fs)
    | Binder (b, vs, f1) ->
	Binder (b, vs, abst f1)
    | TypedForm (f1, ty) ->
	TypedForm (abst f1, ty)
  in abst f0

let has_const (c : constValue) (f0 : form) : bool =
  let rec has f =
    match f with
    | Const _ -> true
    | Var _ -> false
    | TypedForm(f,t) -> has f
    | Binder(k,tvs,f1) -> has f1
    | App(f1,fs) -> hass (has f1) fs
  and hass b fs =
    if b then b
    else (match fs with
	    | [] -> false
	    | f1::fs1 -> hass (has f1) fs1)
  in has f0

let rec contains_var (f : form) (id : ident) : bool =
  match f with
    | Const _ -> false
    | Var v -> v == id
    | TypedForm(f0, _) -> contains_var f0 id
    | Binder(_, til, f0) ->
	(not (List.exists (fun (v, _) -> (v == id)) til)) &&
	  (contains_var f0 id)
    | App(f0, f1) ->
	(contains_var f0 id) || (List.exists (contains_var_rev id) f1)
and contains_var_rev (id : ident) (f : form) : bool =
  contains_var f id

let expand_function 
    (func_name : string) (** name of function to expand *)
    (expansion : form list -> form) (** mapping from arguments to function body *)
    (f0 : form) (** formula in which to replace *)
    : form = (** result *)
  let rec repl f = match f with
    | Const _ -> f
    | Var v -> f
    | TypedForm(f1, t) -> TypedForm(repl f1, t)
    | Binder(b, til, f1) -> Binder(b,til,repl f1)
    | App(TypedForm(Var found_func,t),args) when found_func=func_name 
	-> expansion args
    | App(Var found_func,args) when found_func=func_name 
	-> expansion args
    | App(f1, f2) -> App(repl f1, List.map repl f2)	
  in repl f0


(** Make application, while parsing some
    predefined functions as constants *)
let parse_mk_app (f : form) (args : form list) : form =
  match f with
    | Var "intplus" -> App(Const Plus,args)
    | Var "intless" -> App(Const Lt,args)
    | _ -> App(f,args)

(** Remove comments from a formula for easier matching. *)
let rec remove_comments (f : form) : form =
  match f with
    | App(Const Comment, [_; f1]) -> remove_comments f1
    | App(f1, fs) -> App((remove_comments f1), (List.map remove_comments fs))
    | Binder(b, til, f1) -> Binder(b, til, (remove_comments f1))
    | TypedForm(f1, t1) -> TypedForm(remove_comments f1, t1)
    | _ -> f

(** Remove types from a formula for easier matching. 
    List strip types but does not dummify bound variables. *)
let rec remove_typedform (f : form) : form =
  match f with
    | App(f1, fs) -> App((remove_typedform f1), (List.map remove_typedform fs))
    | Binder(b, til, f1) -> Binder(b, til, (remove_typedform f1))
    | TypedForm(f1, t1) -> remove_typedform f1
    | _ -> f

(** Simultaneously removes types and comments. *)
let rec remove_comments_and_typedform (f : form) : form =
  match f with
    | App(Const Comment, [_; f1]) -> 
	remove_comments_and_typedform f1
    | App(f1, fs) -> 
	App((remove_comments_and_typedform f1), 
	    (List.map remove_comments_and_typedform fs))
    | Binder(b, til, f1) -> 
	Binder(b, til, (remove_comments_and_typedform f1))
    | TypedForm(f1, _) -> 
	remove_comments_and_typedform f1
    | _ -> f

(* Returns the list of conjuncts making up f. *)
let get_conjuncts (f : form) : form list =
  let rec get_conjuncts_rec (fs : form list) (f : form) : form list =
    match f with
      | TypedForm(App(Const And, fs0), _)
      | App(Const And, fs0) -> List.fold_left get_conjuncts_rec fs fs0
      | _ -> fs @ [f]
  in
    get_conjuncts_rec [] f

(* Flattens nested and's and or's. *)
let rec flatten (f : form) : form =
  match f with
    | App(Const And, fs) ->
	smk_and (process_conjuncts fs [])
    | App(Const Or, fs) ->
	smk_or (process_disjuncts fs [])
    | App(Const Comment, [f0; f1]) ->
	App(Const Comment, [f0; (flatten f1)])
    | App(f0, fs) ->
	let f1 = flatten f0 in
	let fs0 = List.map flatten fs in
	  App(f1, fs0)
    | Binder(b, til, f0) ->
	Binder(b, til, (flatten f0))
    | TypedForm (f, tf) ->
	TypedForm ((flatten f), tf)
    | _ -> f
and process_conjuncts
    (to_process : form list) 
    (processed : form list) : form list =
  match to_process with
    | [] -> processed
    | TypedForm(App(Const And, fs0), _) :: to_process0
    | App(Const And, fs0) :: to_process0 -> 
	process_conjuncts to_process0 (processed @ fs0)
    | App(Const Comment, [f0; f1]) :: to_process0 ->
	process_conjuncts (f1 :: to_process0) processed
    | f0 :: to_process0 ->
	let f1 = flatten f0 in
	  process_conjuncts to_process0 (processed @ [f1])
and process_disjuncts
    (to_process : form list) 
    (processed : form list) : form list =
  match to_process with
    | [] -> processed
    | TypedForm(App(Const Or, fs0), _) :: to_process0
    | App(Const Or, fs0) :: to_process0 -> 
	process_disjuncts to_process0 (processed @ fs0)
    | App(Const Comment, [f0; f1]) :: to_process0 ->
	process_disjuncts (f1 :: to_process0) processed
    | f0 :: to_process0 ->
	let f1 = flatten f0 in
	  process_disjuncts to_process0 (processed @ [f1])

(* Rewrites "(a and b) or (b and c)" into "b and (a or c)". *)
let rec factor_common_conjuncts (f : form) : form =
  let is_conjunction (f : form) : bool =
    match f with
      | TypedForm(App(Const And, _), _)
      | App(Const And, _)
      | App(Const Comment, [_; App(Const And, _)]) -> true
      | _ -> false in
  let get_conjuncts (f : form) : form list =
    match f with
      | TypedForm(App(Const And, fs), _)
      | App(Const And, fs)
      | App(Const Comment, [_; App(Const And, fs)]) -> fs
      | _ -> [] in
  let in_common (fss : form list list) (f : form) : bool =
    List.for_all (fun (fs) -> List.mem f fs) fss in
  let remove_common 
      (common : form list)
      (to_filter : form list) : form list =
    List.filter (fun (f) -> (not (List.mem f common))) to_filter in
  let handle_disjuncts (disjuncts : form list) : form =
    match disjuncts with
      | d0 :: ds0  ->
	  let c0 = get_conjuncts d0 in
	  let cs0 = List.map get_conjuncts ds0 in
	  let common, not_common = List.partition (in_common cs0) c0 in
	  let cs1 = List.map (remove_common common) cs0 in
	  let conjuncts = List.map smk_and (not_common :: cs1) in
	    smk_and (common @ [smk_or conjuncts])
      | _ -> App(Const Or, disjuncts) in
    match f with
      | App(Const Or, fs) when (List.for_all is_conjunction fs) ->
	  let fs0 = List.map factor_common_conjuncts fs in
	    handle_disjuncts fs0
      | App(f0, fs) ->
	  let f1 = factor_common_conjuncts f0 in
	  let fs0 = List.map factor_common_conjuncts fs in
	    App(f1, fs0)
      | Binder(b, til, f0) ->
	  Binder(b, til, (factor_common_conjuncts f0))
      | TypedForm(f0, tf) ->
	  TypedForm((factor_common_conjuncts f0), tf)
      | _ -> f
(* Performs substitution on formulae in fs and rm according to rm, in 
   the given order.

   Example: 
     rm := [(a, b), (b, a)] 
     f := [a + b = c]
   Result: 
     b + b = c
*)
let rec substitute 
    (fs : form list)
    (rm : substMap)
    (usedMappings : substMap) : form list * substMap =
  match rm with
    | [] -> fs, usedMappings
    | mapping :: rm0 ->
	let rm1 = List.map (fun (id, f) -> (id, (subst [mapping] f))) rm0 in
	let fs0 = List.map (subst [mapping]) fs in
	  substitute fs0 rm1 (usedMappings @ [mapping])

(* Finds equalities in f and performs substitution. *)
(*
let rec substitute_equalities (f : form) : form =
  print_string "SUBSTITUTE EQUALITIES\n";
  print_string ((PrintForm.string_of_form f) ^ "\n");
  match f with
    | App(Const And, fs)  ->
	print_string "CASE 1\n";
	let fs0, _ = substitute_in_conjuncts fs [] [] [] in
	let fs1 = List.map substitute_equalities fs0 in
	  smk_and fs1
    | App(Const Impl, [f0; f1]) ->
	print_string "CASE 2\n";
	let f2, renameMap = substitute_in_impl f0 in
	let [f3], _ = substitute [f1] renameMap [] in
	  smk_impl (f2, (substitute_equalities f3))
    | App(Const Comment, [f0; f1]) ->
	print_string "CASE 3\n";
	App(Const Comment, [f0; (substitute_equalities f1)])
    | TypedForm(f0, tf) ->
	print_string "CASE 4\n";
	TypedForm((substitute_equalities f0), tf)
    | _ -> print_string "CASE 5\n"; f
and substitute_in_conjuncts
    (to_process : form list) 
    (processed : form list)
    (renameMap : substMap) : form list * substMap =
  match to_process with
    | App(Const Eq, [Var v; f]) :: fs0
    | App(Const Eq, [f; Var v]) :: fs0 ->
	substitute_in_conjuncts fs0 processed ((v, f) :: renameMap)
    | App(Const Comment, [_; f]) :: fs0
    | TypedForm(f, _) :: fs0 ->
	substitute_in_conjuncts (f :: fs0) processed renameMap
    | f :: fs0 ->
	let f0 = substitute_equalities f in
	  substitute_in_conjuncts fs0 (f0 :: processed) renameMap
    | [] ->
	substitute processed renameMap []
and substitute_in_impl (f : form) : form * substMap =
  match f with
    | App(Const And, fs) ->
	let fs0, renameMap = substitute_in_conjuncts fs [] [] in
	  (smk_and fs0), renameMap
    | App(Const Comment, [f0; f1]) ->
	let f2, renameMap = substitute_in_impl f1 in
	  App(Const Comment, [f0; f2]), renameMap
    | TypedForm(f0, tf) ->
	let f1, renameMap = substitute_in_impl f0 in
	  TypedForm(f1, tf), renameMap
    | _ -> (substitute_equalities f), []
*)
