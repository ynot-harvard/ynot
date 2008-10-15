(** Smart constructors and utility functions for MONA formulas *)

open MonaForm

let optimize_forms = ref true

(** Free variables (ignores types) *)

let fv f = 
  let add bv vs v = 
    if List.mem v bv then vs else 
    if List.mem v vs then vs else v::vs in
  let rec fv_term1 t bv acc =
    match t with
    | Var1 v -> add bv acc v
    | Succ1 (t, succs) ->  fv_term1 t bv acc
    | Prefix1 t ->  fv_term1 t bv acc
    | Root1 v_opt -> (match v_opt with
      | Some v -> add bv acc v
      | None -> [])
    | TreeRoot t ->  fv_term2 t bv acc
    | Succ (t, e, v, c) -> fv_term1 t bv acc
    | IntConst _ -> acc
    | Plus (t, _) | Minus (t, _) -> fv_term1 t bv acc
    | Min t | Max t -> fv_term2 t bv acc
  and fv_term2 t bv acc =
    match t with
    | Emptyset -> acc
    | Var2 v -> add bv acc v
    | Set ts -> List.fold_left (fun acc t -> fv_term1 t bv acc) acc ts
    | Union (t1, t2) -> fv_term2 t1 bv (fv_term2 t2 bv acc)
    | Inter (t1, t2) -> fv_term2 t1 bv (fv_term2 t2 bv acc)
    | Diff (t1, t2) -> fv_term2 t1 bv (fv_term2 t2 bv acc)
    | Succ2 (t, succs) -> fv_term2 t bv acc
    | Prefix2 t ->  fv_term2 t bv acc
    | ConstTree (t, v, ct) -> fv_term1 t bv acc in
  let rec fv_atom a bv acc =
    match a with
    | Eq1 (t1, t2) -> fv_term1 t1 bv (fv_term1 t2 bv acc)
    | Neq1 (t1, t2) -> fv_term1 t1 bv (fv_term1 t2 bv acc)
    | Lt1 (t1, t2) -> fv_term1 t1 bv (fv_term1 t2 bv acc)
    | Gt1 (t1, t2) -> fv_term1 t1 bv (fv_term1 t2 bv acc)
    | Leq1 (t1, t2) -> fv_term1 t1 bv (fv_term1 t2 bv acc)
    | Geq1 (t1, t2) -> fv_term1 t1 bv (fv_term1 t2 bv acc)
    | Eq2 (t1, t2) -> fv_term2 t1 bv (fv_term2 t2 bv acc)
    | Neq2 (t1, t2) -> fv_term2 t1 bv (fv_term2 t2 bv acc)
    | Sub (t1, t2) -> fv_term2 t1 bv (fv_term2 t2 bv acc)
    | Elem (t1, t2) -> fv_term1 t1 bv (fv_term2 t2 bv acc)
    | Nelem (t1, t2) -> fv_term1 t1 bv (fv_term2 t2 bv acc)
    | Empty t -> fv_term2 t bv acc
    | Root0 (t, us) -> fv_term1 t bv acc
    | InStateSpace (t, ss) -> fv_term1 t bv acc
    | Variant (t, p, e, v) -> fv_term1 t bv acc
    | Tree v -> add bv acc v
    | Type (t, v) -> fv_term1 t bv acc
    | Sometype1 t -> fv_term1 t bv acc
    | Sometype2 t -> fv_term2 t bv acc
    | _ -> acc in
  let rec fv' f bv acc =
    let fv_letdef defs =
      List.fold_left
	(fun (bv, acc) (v, f) -> (add [] bv v, fv' f bv acc))
	(bv, acc) defs in
    match f with
    | Atom a -> fv_atom a bv acc
    | Not f -> fv' f bv acc
    | And fs -> List.fold_left (fun vs f -> fv' f bv vs) acc fs 
    | Or fs -> List.fold_left (fun vs f -> fv' f bv vs) acc fs 
    | Impl (f1, f2) -> fv' f1 bv (fv' f2 bv acc)
    | Iff (f1, f2) -> fv'  f1 bv (fv' f2 bv acc)
    | Restrict f -> fv' f bv acc
    | Prefix0 f -> fv' f bv acc
    | Pred (v, es) -> 
	List.fold_left (fun vs -> 
	  function 
	    | Form f -> fv' f bv vs
	    | Term1 t -> fv_term1 t bv vs
	    | Term2 t -> fv_term2 t bv vs) (add bv acc v) es
    | Export (fname, f) -> fv' f bv acc
    | Import (fname, vs) -> List.fold_left (fun vs (_,v) -> add bv vs v) acc vs
    | Quant (_, us, vs, f) ->  
	let bv = List.fold_left (add []) bv vs in fv' f bv acc
    | Let0 (defs, f) -> 
	let bv, acc = fv_letdef defs in fv' f bv acc
    | Let1 (defs, f) ->
	let bv, acc = fv_letdef defs in fv' f bv acc
    | Let2 (defs, f) -> 
	let bv, acc = fv_letdef defs in fv' f bv acc
  in
  fv' f [] []
    

let occurs x f =
  let rec oc_term1 t =
    match t with
    | Var1 v -> v = x
    | Succ1 (t, succs) ->  oc_term1 t
    | Prefix1 t ->  oc_term1 t
    | Root1 v_opt -> (match v_opt with
      | Some v -> v = x
      | None -> false)
    | TreeRoot t ->  oc_term2 t 
    | Succ (t, e, v, c) -> oc_term1 t
    | IntConst _ -> false
    | Plus (t, _) | Minus (t, _) -> oc_term1 t
    | Min t | Max t -> oc_term2 t
  and oc_term2 t =
    match t with
    | Emptyset -> false
    | Var2 v -> v = x
    | Set ts -> List.exists (fun t -> oc_term1 t) ts
    | Union (t1, t2) -> oc_term2 t1 || oc_term2 t2 
    | Inter (t1, t2) -> oc_term2 t1 || oc_term2 t2
    | Diff (t1, t2) -> oc_term2 t1  || oc_term2 t2 
    | Succ2 (t, succs) -> oc_term2 t 
    | Prefix2 t ->  oc_term2 t
    | ConstTree (t, v, ct) -> oc_term1 t in
  let rec oc_atom a =
    match a with
    | Eq1 (t1, t2) -> oc_term1 t1 || oc_term1 t2
    | Neq1 (t1, t2) -> oc_term1 t1 || oc_term1 t2
    | Lt1 (t1, t2) -> oc_term1 t1  || oc_term1 t2
    | Gt1 (t1, t2) -> oc_term1 t1  || oc_term1 t2
    | Leq1 (t1, t2) -> oc_term1 t1 || oc_term1 t2
    | Geq1 (t1, t2) -> oc_term1 t1 || oc_term1 t2
    | Eq2 (t1, t2) -> oc_term2 t1 || oc_term2 t2
    | Neq2 (t1, t2) -> oc_term2 t1 || oc_term2 t2
    | Sub (t1, t2) -> oc_term2 t1 || oc_term2 t2
    | Elem (t1, t2) -> oc_term1 t1 || oc_term2 t2
    | Nelem (t1, t2) -> oc_term1 t1 || oc_term2 t2
    | Empty t -> oc_term2 t 
    | Root0 (t, us) -> oc_term1 t
    | InStateSpace (t, ss) -> oc_term1 t
    | Variant (t, p, e, v) -> oc_term1 t
    | Tree v ->  v = x
    | Type (t, v) -> oc_term1 t
    | Sometype1 t -> oc_term1 t
    | Sometype2 t -> oc_term2 t
    | _ -> false in
  let rec oc' f =
    let oc_letdef defs =
      List.fold_left
	(fun (bv, oc) (v, f) -> (bv || v = x, oc || oc' f))
	(false, false) defs in
    match f with
    | Atom a -> oc_atom a
    | Not f -> oc' f
    | And fs -> List.exists (fun f -> oc' f) fs 
    | Or fs -> List.exists (fun f -> oc' f) fs
    | Impl (f1, f2) -> oc' f1 || oc' f2
    | Iff (f1, f2) -> oc' f1 || oc' f2
    | Restrict f -> oc' f
    | Prefix0 f -> oc' f
    | Pred (v, es) ->
	v = x || List.exists 
	  (function
	    | Form f -> oc' f
	    | Term1 t -> oc_term1 t
	    | Term2 t -> oc_term2 t) es
    | Export (fname, f) -> oc' f
    | Import (fname, vs) -> List.exists (fun (_,v) -> v = x) vs
    | Quant (_, us, vs, f) ->  
	if not (List.mem x vs) then oc' f else false
    | Let0 (defs, f) -> 
	let bv, oc = oc_letdef defs in
	if not bv then oc || oc' f else oc
    | Let1 (defs, f) ->
	let bv, oc = oc_letdef defs in 
	if not bv then oc || oc' f else oc
    | Let2 (defs, f) -> 
	let bv, oc = oc_letdef defs in 
	if not bv then oc || oc' f else oc
  in
  oc' f 

(** Smart constructors (no quantifiers) *)


let mk_var1 v = Var1 v
let mk_succ1 t ss = Succ1 (t, ss)
let mk_prefix1 t = Prefix1 t
let mk_root1 v = Root1 v
let mk_treeroot t = TreeRoot t
let mk_succ t e v c = Succ (t, e, v, c)
let mk_intconst i = IntConst i
let mk_plus t i = Plus (t, i)
let mk_minus t i = Minus (t, i)
let mk_max t = Max t
let mk_min t = Min t

let mk_emptyset = Emptyset
let mk_var2 v = Var2 v
let mk_set ts = Set ts
let mk_union t1 t2 = Union (t1, t2)
let mk_inter t1 t2 = Inter (t1, t2)
let mk_diff t1 t2 = Diff (t1, t2)
let mk_succ2 t ss = Succ2 (t, ss)
let mk_prefix2 t = Prefix2 t
let mk_consttree t v c = ConstTree (t, v, c)

let mk_true = Atom True
let mk_false = Atom False

let mk_eq1 t1 t2 = if (t1 = t2) then Atom True else Atom (Eq1 (t1, t2))
let mk_neq1 t1 t2 = if (t1 = t2) then Atom False else Atom (Neq1 (t1, t2))
let mk_eq2 t1 t2 = if (t1 = t2) then Atom True else Atom (Eq2 (t1, t2))
let mk_neq2 t1 t2 = if (t1 = t2) then Atom False else Atom (Neq2 (t1, t2))
let mk_leq1 t1 t2 = if (t1 = t2) then Atom True else Atom (Leq1 (t1, t2))
let mk_geq1 t1 t2 = if (t1 = t2) then Atom True else Atom (Geq1 (t1, t2))
let mk_lt1 t1 t2 = Atom (Lt1 (t1, t2))
let mk_gt1 t1 t2 = Atom (Gt1 (t1, t2))
let mk_sub t1 t2 = if t1 = t2 then Atom True else Atom (Sub (t1, t2))
let mk_elem t1 t2 = Atom (Elem (t1, t2))
let mk_nelem t1 t2 = Atom (Nelem (t1, t2))
let mk_empty t = Atom (Empty t)
let mk_root0 t us = Atom (Root0 (t, us))
let mk_in_state_space t ss = Atom (InStateSpace (t, ss))
let mk_variant t x e v = Atom (Variant (t, x, e, v))
let mk_tree x = Atom (Tree x)
let mk_type t v = Atom (Type (t,v))
let mk_sometype1 t = Atom (Sometype1 t)
let mk_sometype2 t = Atom (Sometype2 t)

let mk_pred p es = Pred (p, es)

let mk_not f = match f with
| Atom False -> Atom True
| Atom True -> Atom False
| Atom (Eq1 (t1, t2)) -> Atom (Neq1 (t1, t2))
| Atom (Neq1 (t1, t2)) -> Atom (Eq1 (t1, t2))
| Atom (Eq2 (t1, t2)) -> Atom (Neq2 (t1, t2))
| Atom (Neq2 (t1, t2)) -> Atom (Eq2 (t1, t2))
| Atom (Elem (t1, t2)) -> Atom (Nelem (t1, t2))
| Atom (Nelem (t1, t2)) -> Atom (Elem (t1, t2))
| Not f -> f
| _ -> Not f

let mk_and fs =
  let add xs x = if List.mem x xs then xs else x::xs in
  let rec mk_and' fs acc = match fs with
  | [] -> 
      (match acc with
      | [] -> Atom True
      | [f] -> f
      | _ -> And acc)
  | [Impl (f11, f12); Impl (f21, f22)] when f11 = f22 && f12 = f21 -> Iff (f11, f12)
  | And fs0 :: fs -> mk_and' (List.rev_append fs0 fs) acc
  | Atom True::fs -> mk_and' fs acc
  | Atom False::fs -> Atom False
  | f::fs -> mk_and' fs (add acc f)
in mk_and' fs []

let mk_or fs =
  let add xs x = if List.mem x xs then xs else x::xs in
  let rec mk_or' fs acc = match fs with
  | [] -> 
      (match acc with
      | [] -> Atom False
      | [f] -> f
      | _ -> Or acc)
  | Or fs0 :: fs -> mk_or' (fs0 @ fs) acc
  | Atom False::fs -> mk_or' fs acc
  | Atom True::fs -> Atom True
  | f::fs -> mk_or' fs (add acc f)
  in 
  if not !optimize_forms then mk_or' fs []
  else match fs with
  | [And ll; And rl] ->
      let i = Util.intersect ll rl in
      mk_and ((mk_or' [mk_and (Util.difference ll i); 
                       mk_and (Util.difference rl i)] [])::i)
  | _ -> mk_or' fs []

let mk_iff f1 f2 = if f1 = f2 then Atom True else Iff (f1, f2)

let mk_impl f1 f2 =
  match (f1,f2) with
  | (Atom True, f2) -> f2
  | (Atom False, f2) -> Atom True
  | (f1, Atom False) -> mk_not f1
  | (f1, Atom True) -> Atom True
  | (f1, Impl (f21, f22)) -> Impl (mk_and [f1;f21], f22)
  | _ -> if f1 = f2 then Atom True else Impl (f1, f2)

let mk_restrict f = Restrict f
let mk_prefix0 f = Prefix0 f
let mk_export fname f = Export (fname, f)
let mk_import fname vs = Import (fname, vs) 

(** Substitution !!! Not capture avoiding. Use with care !!! *)

let subst sigma f =
  let rec subst_term1 t sigma =
    match t with
    | Var1 v ->
	(try 
	  let e = List.assoc v sigma in
	  match e with
	  | Term1 t' -> t'
	  | _ -> t
	with Not_found -> t)
    | Succ1 (t, succs) ->  mk_succ1 (subst_term1 t sigma) succs
    | Prefix1 t ->  mk_prefix1 (subst_term1 t sigma)
    | TreeRoot t ->  mk_treeroot (subst_term2 t sigma) 
    | Succ (t, e, v, c) -> mk_succ (subst_term1 t sigma) e v c
    | Plus (t, i) -> mk_plus (subst_term1 t sigma) i
    | Minus (t, i) -> mk_minus (subst_term1 t sigma) i
    | Max t -> mk_max (subst_term2 t sigma)
    | Min t -> mk_min (subst_term2 t sigma)
    | _ -> t
  and subst_term2 t sigma =
    match t with
    | Emptyset -> t
    | Var2 v -> 
	(try 
	  let e = List.assoc v sigma in
	  match e with
	  | Term2 t' -> t'
	  | _ -> t
	with Not_found -> t)
    | Set ts -> mk_set (List.map (fun t -> subst_term1 t sigma) ts)
    | Union (t1, t2) -> mk_union (subst_term2 t1 sigma) (subst_term2 t2 sigma) 
    | Inter (t1, t2) -> mk_inter (subst_term2 t1 sigma) (subst_term2 t2 sigma)
    | Diff (t1, t2) -> mk_diff (subst_term2 t1 sigma) (subst_term2 t2 sigma)
    | Succ2 (t, succs) -> mk_succ2 (subst_term2 t sigma) succs
    | Prefix2 t ->  mk_prefix2 (subst_term2 t sigma)
    | ConstTree (t, v, ct) -> mk_consttree (subst_term1 t sigma) v ct
  and subst_atom a sigma =
    match a with
    | Eq1 (t1, t2) -> mk_eq1 (subst_term1 t1 sigma) (subst_term1 t2 sigma)
    | Neq1 (t1, t2) -> mk_neq1 (subst_term1 t1 sigma) (subst_term1 t2 sigma)
    | Lt1 (t1, t2) -> mk_lt1 (subst_term1 t1 sigma) (subst_term1 t2 sigma)
    | Gt1 (t1, t2) -> mk_gt1 (subst_term1 t1 sigma) (subst_term1 t2 sigma)
    | Leq1 (t1, t2) -> mk_leq1 (subst_term1 t1 sigma) (subst_term1 t2 sigma)
    | Geq1 (t1, t2) -> mk_geq1 (subst_term1 t1 sigma) (subst_term1 t2 sigma)
    | Eq2 (t1, t2) -> mk_eq2 (subst_term2 t1 sigma) (subst_term2 t2 sigma)
    | Neq2 (t1, t2) -> mk_neq2 (subst_term2 t1 sigma) (subst_term2 t2 sigma)
    | Sub (t1, t2) -> mk_sub (subst_term2 t1 sigma) (subst_term2 t2 sigma)
    | Elem (t1, t2) -> mk_elem (subst_term1 t1 sigma) (subst_term2 t2 sigma)
    | Nelem (t1, t2) -> mk_nelem (subst_term1 t1 sigma) (subst_term2 t2 sigma)
    | Empty t -> mk_empty (subst_term2 t sigma)
    | Root0 (t, us) -> mk_root0 (subst_term1 t sigma) us
    | InStateSpace (t, ss) -> mk_in_state_space (subst_term1 t sigma) ss
    | Variant (t, p, e, v) -> mk_variant (subst_term1 t sigma) p e v
    (* | Tree v -> check v!!! *)
    | Type (t, v) -> mk_type (subst_term1 t sigma) v
    | Sometype1 t -> mk_sometype1 (subst_term1 t sigma)
    | Sometype2 t -> mk_sometype2 (subst_term2 t sigma) 
    | _ -> Atom a
  and subst_form f sigma =
    let subst_letdef defs sigma =
      let sigma' = List.filter (fun (x, e) -> 
	not (List.exists (fun (v, _) -> x = v) defs)) sigma in
      let defs' = List.rev_map (fun (v, f) -> (v, subst_form f sigma)) defs in
      (sigma', defs')
    in
    match f with
    | Atom a -> subst_atom a sigma
    | Not f -> mk_not (subst_form f sigma)
    | And fs -> mk_and (List.map (fun f -> subst_form f sigma) fs)
    | Or fs -> mk_or (List.map (fun f -> subst_form f sigma) fs)
    | Impl (f1, f2) -> mk_impl (subst_form f1 sigma) (subst_form f2 sigma)
    | Iff (f1, f2) -> mk_iff (subst_form f1 sigma) (subst_form f2 sigma)
    | Restrict f -> mk_restrict (subst_form f sigma)
    | Prefix0 f -> mk_prefix0 (subst_form f sigma)
    | Pred (v, []) ->
	(try 
	  let e = List.assoc v sigma in
	  match e with
	  | Form f' -> f'
	  | _ -> f
	with Not_found -> f)
    | Pred (v, es) ->
	mk_pred v (List.map
	  (function
	    | Form f -> Form (subst_form f sigma)
	    | Term1 t -> Term1 (subst_term1 t sigma)
	    | Term2 t -> Term2 (subst_term2 t sigma)) es)
    | Export (fname, f) -> mk_export fname (subst_form f sigma)
    | Quant (q, us, vs, f') ->
	let sigma' = List.filter (fun (x, e) -> not (List.exists ((=) x) vs)) sigma in
	(match sigma' with 
	| [] -> f
	| _ -> Quant (q, us, vs, subst_form f' sigma'))
    | Let0 (defs, f') -> 
	let sigma', defs = subst_letdef defs sigma in
	(match sigma' with
	| [] -> Let0 (defs, f')
	| _ -> Let0 (defs, subst_form f' sigma'))
    | Let1 (defs, f') ->
	let sigma', defs = subst_letdef defs sigma in
	(match sigma' with
	| [] -> Let1 (defs, f')
	| _ -> Let1 (defs, subst_form f' sigma'))
    | Let2 (defs, f') -> 
	let sigma', defs = subst_letdef defs sigma in
	(match sigma' with
	| [] -> Let2 (defs, f')
	| _ -> Let2 (defs, subst_form f' sigma'))
    | _ -> f
  in
  subst_form f sigma


(** Smart constructors (quantifiers) *)

let mk_quant q us xs f =
  (* eliminate existential quantifiers *)
  let eliminate conj xs =
    let subst sigma = List.rev_map (subst sigma) in
    let rec remove conj acc =
      match conj with
      |	[] -> acc 
      |	c::conj' ->
	  match c with 
	  | Atom Eq1 (Var1 v1, Var1 v2) ->
	      if v1 = v2 then conj' else
	      if List.mem v1 xs then
		remove (subst [(v1, Term1 (Var1 v2))] conj') (subst [(v1, Term1 (Var1 v2))] acc)
	      else if List.mem v2 xs then
		remove (subst [(v2, Term1 (Var1 v1))] conj') (subst [(v2, Term1 (Var1 v1))] acc)
	      else remove conj' (c :: acc)
	  | Atom Eq1 (Var1 v1, t) 
	  | Atom Eq1 (t, Var1 v1) ->
	      if List.mem v1 xs && not (occurs v1 (Pred ("", [Term1 t]))) then
		remove (subst [(v1, Term1 t)] conj') (subst [(v1, Term1 t)] acc)
	      else remove conj' (c :: acc)
	  | Atom Eq2 (Var2 v1, Var2 v2) ->
	      if v1 = v2 then conj' else
	      if List.mem v1 xs then
		remove (subst [(v1, Term2 (Var2 v2))] conj') (subst [(v1, Term2 (Var2 v2))] acc)
	      else if List.mem v2 xs then
		remove (subst [(v2, Term2 (Var2 v1))] conj') (subst [(v2, Term2 (Var2 v1))] acc)
	      else remove conj' (c :: acc)
	  | Atom Eq2 (Var2 v1, t) 
	  | Atom Eq2 (t, Var2 v1) ->
	      if List.mem v1 xs  && not (occurs v1 (Pred ("", [Term2 t]))) then
		remove (subst [(v1, Term2 t)] conj') (subst [(v1, Term2 t)] acc)
	      else remove conj' (c :: acc)
	  | Pred(v, []) when List.mem v xs ->
	      remove conj' acc
	  | _ -> remove conj' (c :: acc)
    in
    let conj' = remove conj [] in
    (List.filter (fun x -> List.exists (fun c -> occurs x c) conj') xs, conj')
  in
  let mk_quant' q xs f = 
    let fvs = fv f in
    let xs' = List.filter (fun x -> List.mem x fvs) xs in
    match xs' with
    | [] -> f
    | _ -> Quant (q, us, xs', f)
  in
  let merge_quants q us xs f =
    let add xs x = 
      if List.exists (fun y -> x = y) xs then xs else x::xs in
    match f with
    | Quant (q', us', xs',f) when q' = q && us' = us -> 
	Quant (q, us, List.fold_left add xs' xs, f) 
    | _ -> Quant (q, us, xs, f)
  in
  let dual_quant = function
    | Exists0 -> Forall0
    | Forall0 -> Exists0
    | Exists1 -> Forall1
    | Forall1 -> Exists1
    | Exists2 -> Forall2
    | Forall2 -> Exists2
  in 
  let eq_quant q q' = match (q, q') with
  | (Forall0, Forall0) 
  | (Forall0, Forall1) 
  | (Forall0, Forall2)
  | (Forall1, Forall0) 
  | (Forall1, Forall1)
  | (Forall1, Forall2)
  | (Forall2, Forall0)
  | (Forall2, Forall1)
  | (Forall2, Forall2)
  | (Exists0, Exists0) 
  | (Exists0, Exists1) 
  | (Exists0, Exists2) 
  | (Exists1, Exists0) 
  | (Exists1, Exists1) 
  | (Exists1, Exists2)
  | (Exists2, Exists0) 
  | (Exists2, Exists1)
  | (Exists2, Exists2) -> true
  | _ -> false
  in
  let rec mk_opt_quant q xs f : form =
    if [] = xs then f else
    match f with
    | Not f -> mk_not (mk_opt_quant (dual_quant q) xs f)
    | And fs ->
	(match q with
	| Forall0 | Forall1 | Forall2 -> 
	    mk_and (List.map (mk_opt_quant q xs) fs)
	| _ -> 
	    let xs', fs' = eliminate fs xs in
	    let min_scope res x = 
	      let dep, indep = List.partition (fun f -> occurs x f) res in
	      match dep with
	      |	[] -> indep
	      |	[f] -> mk_opt_quant q [x] f :: indep
	      |	_ -> Quant(q, us, [x], (And dep)) :: indep 
	    in
	    mk_and (List.fold_left min_scope fs' xs'))
    | Or fs ->
	(match q with
	| Exists0 | Exists1 | Exists2 -> 
	    mk_or (List.map (mk_opt_quant q xs) fs)
	| _ -> 
	    let min_scope res x = 
	      let dep, indep = List.partition (fun f -> occurs x f) res in
	      match dep with
	      |	[] -> indep
	      |	[f] -> mk_opt_quant q [x] f :: indep
	      |	_ -> Quant (q, us, [x], Or dep) :: indep 
	    in
	    mk_or (List.fold_left min_scope fs xs))
    | Impl (f1, f2) ->
	(match q with
	| Exists0 | Exists1 | Exists2 -> 
	    Impl (mk_opt_quant (dual_quant q) xs f1, mk_opt_quant q xs f2)
	| _ -> 
	    let xs_1, xs_2, xs_12 =
	      List.fold_left 
		(fun (xs_1, xs_2, xs_12) x ->
		  if occurs x f1 then 
		    if occurs x f2 then (xs_1, xs_2, x::xs_12) 
		    else (x::xs_1, xs_2, xs_12)
		  else (xs_1, x::xs_2, xs_12))
		([], [], []) xs
	    in
	    let f1 = mk_opt_quant (dual_quant q) xs_1 f1
	    and f2 = mk_opt_quant q xs_2 f2 in
	    match xs_12 with
	    | [] -> Impl (f1, f2)
	    | _ -> Quant (q, us, xs_12, Impl (f1, f2)))
    | Quant (q', us', xs', f') when eq_quant q' q ->
	let xs = List.filter
	    (fun x -> not (List.exists (fun x' -> x = x') xs')) xs in
	(match xs with 
	| [] -> f
	| _ -> merge_quants q' us' xs' (mk_opt_quant q xs f'))
    | Atom a -> (match q with 
      |	Forall0 | Forall1 | Forall2 -> mk_quant' q xs f
      |	_ -> let xs', fs' = eliminate [f] xs in
	mk_quant' q xs' (mk_and fs'))
    | _ -> mk_quant' q xs f
  in
  if !optimize_forms then mk_opt_quant q xs f
  else merge_quants q us xs f 
  
let mk_exists0 = mk_quant Exists0 [] 
let mk_ex0 = mk_exists0
let mk_forall0 = mk_quant Forall0 []
let mk_all0 = mk_forall0
let mk_exists1 = mk_quant Exists1
let mk_ex1 = mk_quant Exists1 [] 
let mk_forall1 = mk_quant Forall1
let mk_all1 = mk_quant Forall1 []
let mk_exists2 = mk_quant Exists2
let mk_ex2 = mk_quant Exists2 [] 
let mk_forall2 = mk_quant Forall2
let mk_all2 = mk_quant Forall2 []
    
let mk_let0 defs f = Let0 (defs, f)
let mk_let1 defs f = Let1 (defs, f)
let mk_let2 defs f = Let2 (defs, f)
