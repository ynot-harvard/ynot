open Bf
open Bf_set
open Form
open FormUtil
open PrintForm
open TypeReconstruct
open BohneUtil   

(** Predicates *)   
type pred = Bf.var

(** Predicate properties *)
type pred_props =
  | IsSingleton of typedIdent option
  | IsNull
  | IsConst
  | IsOld of ident
  | Inherit
 
(** Predicate declaration *)
type pred_decl = {
    pred_name : ident;
    pred_index : pred;
    pred_def : form;
    pred_concr_def : form;
    pred_env : typeEnv;
    pred_arity : int;
    mutable pred_props : pred_props list
  }

let var_prefix = ""
	
let free_var_name = "v"

let bound_var_name = "v_"

let null_name = var_prefix ^ (string_of_const NullConst)

let var_name name k = var_prefix ^ name ^ string_of_int k
         
let free_var_name k = var_name free_var_name k

let var name k = mk_var (var_name name k)

let free_var k = mk_var (free_var_name k)

let typed_var name k = (var_prefix ^ name ^ string_of_int k, mk_object_type)

let typed_free_var k = (free_var_name k, mk_object_type)

let typed_var_list name arity =
 let rec l k acc = 
   if k > 0 then l (k-1) (typed_var name (k-1)::acc) else acc
 in l arity []	

let typed_free_var_list arity =
 let rec l k acc = 
   if k > 0 then l (k-1) (typed_free_var (k-1)::acc) else acc
 in l arity []

let pred_prefix = "p__"

(** Construct new predicate declaration *)
let mk_pred_decl pname pdef0 props =
  let i = Bf.new_var () in
  let pdef, env = reconstruct_types [] pdef0 in 
  let pdef' = unlambda pdef in
  let ty = TypeReconstruct.get_type env pdef' in
  let pdef', props = 
    if ty = mk_object_type then
      (Binder (Comprehension, [typed_var bound_var_name 0], 
	       mk_eq (pdef', var bound_var_name 0)),
       IsSingleton None::props)
    else if ty = mk_bool_type then
      (pdef', props)
    else (pdef', props)
  in
  let arity, pdef' = match pdef' with 
  | Binder (Comprehension, vs, f) ->
      let vs', smap, k = List.fold_right 
	  (fun (v, t) (vs', smap, k) -> 
	    let v' = var_name bound_var_name k in
	    ((v', t)::vs', (v, mk_var v')::smap, k+1)) 
	  vs ([], [], 0)
      in 
      (k, Binder (Comprehension, vs', subst smap f))
  | _ -> (0, pdef')
  in
  let vars = List.map (fun (x, _) -> mk_var x) (typed_free_var_list arity) in
  let elem = match vars with [x] -> x | _ -> mk_tuple vars in
  let concr_pdef = match pdef' with
  | Binder (Comprehension, _, f) ->      
      unlambda (mk_elem (elem, pdef'))
  | _ -> pdef'
  in
  { pred_name = pname;
    pred_index = i;
    pred_def = pdef';
    pred_concr_def = concr_pdef;
    pred_env = env;
    pred_arity = arity;
    pred_props = props
  }

(** Predicate for null *)
let null_decl = mk_pred_decl (pred_prefix ^ null_name)
    (Binder (Comprehension, [typed_var bound_var_name 0], 
	     App (Const Eq, [Const NullConst; var bound_var_name 0])))
    [IsSingleton None; IsNull; IsConst; Inherit]

(** Index of null predicate *)
let null_pred = null_decl.pred_index

(** Array containing all predicate declarations *)
let predicates = Array.make Bf.var_max null_decl

let _ = predicates.(0) <- null_decl

(** Maximal predicate index *)
let max_index () = Bf.vars () - 1

let search name = 
  let rec search i =
    if i < 0 then raise Not_found
    else if predicates.(i).pred_name = name then predicates.(i)
    else search (i - 1)
  in search (max_index ())

(** Get predicate by name *)
let pred_by_name name =
  try search name
  with Not_found ->
    Util.warn (Printf.sprintf "Could not find predicate '%s'" name); 
    raise Not_found

(** Add a predicate *)
let add_pred_decl name pdef props =
  try search name 
  with Not_found -> 
    let decl = mk_pred_decl name pdef props in
    predicates.(decl.pred_index) <- decl;
    decl

(** Add a predicate for some variable *) 
let add_var_pred_decl ((ident, ty) as vt) =
  let def, props = 
    if ty = mk_bool_type then
      (mk_var ident, [])
    else if ty = mk_object_type then
      (Binder (Comprehension, [typed_var bound_var_name 0], 
	      mk_eq (mk_var ident, var bound_var_name 0)),
       [IsSingleton (Some vt)])
    else (Util.warn ("Pred.mk_var_pred: unsupported type %s" ^ string_of_type ty); 
	  (mk_true, []))
  in
  add_pred_decl (pred_prefix ^ ident) def props

let union_preds preds1 preds2 =
  let diff = List.filter (fun p -> 
    not (List.exists (fun q -> q.pred_index = p.pred_index) preds2)) 
      preds1
  in diff @ preds2

let _ = 
  Bf.reset ();
  ignore (Bf.new_var ())
  
let has_prop pprop p =
  List.mem pprop p.pred_props

let is_singleton p =
  List.exists (function IsSingleton _ -> true | _ -> false) p.pred_props

let is_old p =
  List.exists (function IsOld _ -> true | _ -> false) p.pred_props

let is_state_pred p =
  p.pred_arity = 0

let get_ident p =
  Util.find_map (function IsSingleton i -> i | _ -> None) p.pred_props

let get_pred_name i = predicates.(i).pred_name

let get_pred_decl i = predicates.(i)

let get_pred_by_def f = 
  let rec lookup i =
    if i = -1 then raise Not_found
    else if equal predicates.(i).pred_def f
    then predicates.(i)
    else lookup (i - 1) 
  in lookup (max_index ())

(** Add an unnamed predicate *)
let add_pred =
  let c = ref (-1) in
  fun pdef props ->
    try get_pred_by_def pdef 
    with Not_found ->
      let pname = 
	c := !c + 1; 
	pred_prefix ^ (string_of_int !c)
      in 
      Debug.print_msg 2 (fun chan ->
	output_string chan ("\nadd predicate: " ^ string_of_form (mk_eq (mk_var pname, pdef)) ^ "\n"));
      add_pred_decl pname pdef props
	
	
let get_all_preds () = 
  let rec get_all i acc =
    if i = -1 then acc
    else get_all (i - 1) (predicates.(i)::acc)
  in 
  get_all (max_index ()) []

let get_pred_def pred = 
  mk_eq (mk_var (pred.pred_name), pred.pred_def)
  
let get_pred_defs preds =
  List.fold_left (fun acc p ->
    if is_old p || is_singleton p then acc 
    else get_pred_def p::acc) [] preds

let get_all_defs () = 
  let rec get_all i acc =
    if i = -1 then acc
    else 
      if is_old predicates.(i) then get_all (i - 1) acc else
      get_all (i - 1) (get_pred_def predicates.(i)::acc)
  in get_all (max_index ()) []

let concretize_preds f =
  smk_impl (smk_and (get_all_defs ()), f)

let pred_to_form conretize p =
  if conretize || is_singleton p then p.pred_concr_def else 
  let vars = List.map (fun (x, _) -> mk_var x) (typed_free_var_list p.pred_arity) in
  let elem = match vars with [x] -> x | _ -> mk_tuple vars in
  if is_state_pred p then
    mk_var p.pred_name
  else mk_elem (elem, mk_var p.pred_name)

  


let print_pred_decl chan pdecl =
  let out = output_string chan in
  let print_props props =
    out " [";
    if List.mem Inherit props then out "inherit, "
    else out "~inherit, ";
    if List.mem IsConst props then out "isConst, "
    else out "~isConst, ";
    if List.exists (function IsSingleton _ -> true | _ -> false) props 
    then out "isSingleton, "
    else out "~isSingleton, ";
    if List.exists (function IsOld _ -> true | _ -> false) props 
    then out "isOld, "
    else out "~isOld, ";
    out "]\n";
  in
  out (PrintForm.string_of_form (App (Const MetaEq, [mk_var pdecl.pred_name; pdecl.pred_def])));
  print_props pdecl.pred_props

