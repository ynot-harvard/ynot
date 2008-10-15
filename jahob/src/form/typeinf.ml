(**
  Doing some simple type inference for {!Form} formulas.
*)

open Form
open FormUtil

type typeEnv = typedIdent list

let bool_type = TypeApp (TypeBool, [])
let int_type = TypeApp (TypeInt, [])
let set_type = TypeApp (TypeSet, []) (* ??? set is always applied to some type, even if it's a variable *)
let set_type_of tf = TypeApp (TypeSet, [tf])
let unknown_type = TypeApp (TypeDefined "__unknown__", [])
let object_type = mk_class_type "Object"

let mk_bool (v : string) : typedIdent = (v, TypeApp (TypeBool, []))
let mk_int (v : string) : typedIdent = (v, TypeApp (TypeInt, []))

let panic (msg : string) = failwith msg
let warn (msg : string) = print_string (msg ^ "\n")


let lookup (iden : ident) (tenv : typeEnv) : typeForm option = 
  try
    match List.assoc iden tenv with
      | t -> Some t
  with
      Not_found -> None

let rec infer (f : form) (tenv : typeEnv) : form = 
  let (f, ts) = inferHelper f tenv in
    f

(*
  new form and identifiers to be translated to singleton sets
*)
and inferHelper (f0 : form) (tenv : typeEnv) : (form * ident list) = match f0 with
  | TypedForm (f, _) -> (* (f0, []) *)
      inferHelper f tenv

  | Const c ->
      begin
	match c with
	  | BoolConst _ -> (TypedForm (f0, bool_type), [])
	  | IntConst _ -> (TypedForm (f0, int_type), [])
	  | EmptysetConst -> (TypedForm (f0, set_type), [])
	  | NullConst -> (TypedForm (Const EmptysetConst,set_type), [])
	  | _ -> panic ("typeinf:inferHelper: don't know type of constant" ^ Form.string_of_const (c))
      end

  | Var v ->
      begin
	(* assume that v is already declared *)
	match lookup v tenv with
	  | Some t -> (TypedForm (f0, t), [])
	  | None -> 
	      panic ("typeinf:inferHelper: type of variable " ^ v ^ " is not known in env:" ^
		    PrintForm.wr_bindings tenv ^ "\n")
      end
	
  | App (f, fs) ->
      (* supporting function that builds new formulua along with its type using TypedForm *)
      let typeBuilder appconst argtype restype =
	let fs1 = List.map (fun ff -> inferHelper ff tenv) fs in
	let (flist, vss) = List.split fs1 in
	let flist1 = List.map (fun ff -> matchType ff argtype) flist in
	  (TypedForm (App (appconst, flist1), restype), List.concat vss)
	    
      (* main body of App pattern *)
      in
	begin
	  match f with
	    | (Const And | Const Or | Const Not | Const Impl | Const Iff) as appconst -> 
		(* [ bool -> ] bool -> bool *)
		typeBuilder appconst bool_type bool_type
		  
	    | (Const Lt | Const Gt | Const LtEq | Const GtEq) as appconst ->
		(* int -> int -> bool *)
		typeBuilder appconst int_type bool_type
		  
	    | (Const UMinus | Const Plus | Const Minus) as appconst ->
		(* int -> int -> int *)
		typeBuilder appconst int_type int_type
		  
	    | (Const Mult) as appconst -> (* special case: arguments are not uniform *)
		let fs1 = inferHelper (List.nth fs 1) tenv in
		let fs2 = matchType (fst fs1) int_type in
		  (TypedForm (App (appconst, [List.hd fs; fs2]), int_type), snd fs1)
		    
	    | (Const Card) as appconst -> 
		(* set -> int *)
		typeBuilder appconst set_type int_type
		  
	    | (Const Cardeq | Const Cardleq | Const Cardgeq | Const Subseteq | Const Subset | Const Seteq) as appconst ->
		(* set -> set -> bool *)
		typeBuilder appconst set_type bool_type
		  
	    | (Const Cap | Const Cup | Const Diff) as appconst ->
		(* set -> set -> set *)
		typeBuilder appconst set_type set_type

	    | (Const Elem) as appconst ->
		(* eletype -> set -> bool *)
		if List.length fs != 2 then
		  panic ("typeinf:inferHelper: Elem needs two parameters, received " 
			 ^ (string_of_int (List.length fs)))
		else
		  let fs1 = inferHelper (List.nth fs 1) tenv in
		  let fs2 = matchType (fst fs1) set_type in
		  let rec get_name ele = match ele with
		    | Var name -> name
		    | TypedForm (f, _) -> get_name f
		    | _ -> panic "typeinf:inferHelper: only membership of variable is supported" in
		    (TypedForm (App (Const Subseteq, [Var (get_name (List.hd fs)); fs2]), 
				bool_type), (get_name (List.hd fs))::(snd fs1))
		  
	    | (Const Eq) as appconst ->
		(* either set -> set -> bool or int -> int -> bool *)
		let fs1 = inferHelper (List.hd fs) tenv in
		let fs2 = inferHelper (List.nth fs 1) tenv in
		  if is_set_form (fst fs1) || is_set_form (fst fs2) then
		    begin
		      if is_empty_set (get_form (fst fs1)) || is_empty_set (get_form (fst fs2)) then
			(* if one of them is empty set, i.e. they represent null values,
			   force the other to be set *)
			let to_set tf0 = match tf0 with 
			  | TypedForm (f, tf) -> 
			      if is_set_type tf then
				tf0
			      else
				TypedForm (f, set_type_of tf)
			  | _ -> panic ("typeinf:inferHelper:get_form: "
					^ "inferHelper returns non-TypedForm formula") in
			let setfs1 = to_set (fst fs1) in
			let setfs2 = to_set (fst fs2) in
			  (TypedForm (App (Const Seteq, [setfs1; setfs2]), bool_type),
			   snd fs1 @ snd fs2)
		      else
			(* otherwise, set types *)
			typeBuilder (Const Seteq) set_type bool_type
		    end
		  else if is_object_form (fst fs1) || is_object_form (fst fs2) then
		    typeBuilder (Const Seteq) object_type bool_type
		  else if is_int_form (fst fs1) || is_int_form (fst fs2) then
		    typeBuilder appconst int_type bool_type
		  else
		    typeBuilder appconst (get_type (fst fs1)) bool_type
	    | Const Subseteq ->
		typeBuilder (Const Subseteq) set_type bool_type
	    | (Const Old) as appconst ->
		let (tf, vs) = inferHelper (List.hd fs) tenv in
		  (TypedForm (App (Const Old, [tf]), get_type tf), vs)

	    | (Const FiniteSetConst) as appconst ->
		let rec getVar v = match v with
		  | Var name -> name
		  | TypedForm (f, _) -> getVar f
		  | _ -> panic ("typeinf:inferHelper: finite set elements must be variable") in
		let vs = List.map getVar fs in
		let svars = List.map (fun v -> TypedForm (Var v, set_type)) vs in
		  if List.length svars = 1 then
		    (List.hd svars, vs)
		  else
		    (TypedForm (App (Const Cup, svars), set_type), vs)

	    | Var fsym ->
		(* for now, do something very lousy for user-defined function symbol: just
		   compute the number of arguments, resulting type is fsym : unknown -> ... -> unknown *)
		let argtypes = List.map (fun _ -> unknown_type) fs in
		  (TypedForm (f0, TypeFun (argtypes, unknown_type)), [])

	    | _ -> panic ("typeinf:infHelper:App: not handled yet at application of " ^ PrintForm.string_of_form f ^ " to " ^ 
			 PrintForm.string_of_form (mk_list fs))
	end;

  | Binder (binder, tvids, f) ->
      (* assuming prenex normal form *)
      let (body, tenv, bders) = splitQuants f0 in
      let (tf, vs) = inferHelper body tenv in
      let vsref = ref vs in
      let tfref = ref tf in
      let bdersref = ref bders in
      let newbdersref = ref [] in
	while List.length !bdersref > 0 do
	  let (bder, tvs) = List.hd !bdersref in
	  let (newf, newtvs, remains) = varToSet bder tvs !vsref !tfref in
	    bdersref := List.tl !bdersref;
	    vsref := remains;
	    tfref := newf;
	    newbdersref := (bder, newtvs)::(!newbdersref)
	done;
	(List.fold_right (fun (bder, tvs) -> fun ff -> Binder (bder, tvs, ff)) !newbdersref !tfref, !vsref)
	  (*
	    let localtenv = tvids @ tenv in
	    let (f1, vs1) = inferHelper f localtenv in
	    let vs = Util.remove_dups vs1 in
	    let (f2, remains) = varToSet binder tvids vs f1 in
	    (TypedForm (f2, bool_type), remains)
	  *)

(*
  Converting quantified variables in qvars0 that appear in
  vars0 into quantified singleton sets.

  Return value: transformed formula
*)
and varToSet (binder : binderKind) (qvars0 : typedIdent list)
    (vars0 : ident list) (f0 : form) : (form * typedIdent list * ident list) =
  let rec varToSetHelper qvars1 newqvars f1 xvars = match qvars1 with (* xvars : variables translated by the helper, the rest of the variables are to be translated by outer binders *)
    | [] -> (f1, newqvars, xvars)
    | qvar :: qvars ->
	begin
	  if List.mem (fst qvar) vars0 then
	    (* convert this element variable into a singleton set with the same name *)
	    begin
	      match binder with
		| Forall ->
		    let (f2, newqvars2, xvars1) = varToSetHelper qvars newqvars f1 xvars in
		      (TypedForm (App (Const Impl,
				      [App (Const Eq, 
					    [App (Const Card, [Var (fst qvar)]); 
					     Const (IntConst 1)]); f2]), bool_type),
		       (fst qvar, set_type_of (snd qvar))::newqvars2,
		       (fst qvar) :: xvars1)
		| Exists ->
		    let (f2, newqvars2, xvars1) = varToSetHelper qvars newqvars f1 xvars in
		      (TypedForm(App (Const And,
				      [App (Const Eq,
					    [App (Const Card, [Var (fst qvar)]); 
					     Const (IntConst 1)]); f2]), bool_type),
		       (fst qvar, set_type_of (snd qvar))::newqvars2,
		       (fst qvar) :: xvars1)
		| _ -> panic "formbapa:varToSet: unsupported binder kind"
	    end
	  else
	    let (f2, newqvars2, xvars1) = varToSetHelper qvars newqvars f1 xvars in
	      (f2, qvar::newqvars2, xvars1)
	end
  in
  let (f, newqvars, xvars) = varToSetHelper qvars0 [] f0 [] in
    (f, newqvars, List.filter (fun v -> not (List.mem v xvars)) vars0)

and splitQuants (f0 : form) : (form * typeEnv * (binderKind * typedIdent list) list) =
  let rec helper body tenv bders  = match body with
    | Binder (binder, tvids, f) -> helper f (tvids @ tenv) ((binder, tvids)::bders)
    | _ -> (body, tenv, bders)
  in
    helper f0 [] []

(*
  let newtenv = inferHelper f localtenv in (* removing vars in tvids, keeping new funcs, preds *)
  List.filter (fun (iden, t) -> not (List.mem_assoc iden tvids)) newtenv
*)
	  
	  
(*
  If f0's type is known, it must match t0.
  If f0's type is unknown, force it to be t0.
*)
and matchType (f0 : form) (t0 : typeForm) : form =
  match f0 with
    | TypedForm (f, t) ->
	begin
	  match t with
	    | TypeFun (ts, t1) -> 
		if t1 = unknown_type then
		  TypedForm (f0, TypeFun (ts, t0))
		else if is_same_type t1 t0 then
		  f0
		else
		  panic ("typeinf:matchType: non-matching types: " ^
			   PrintForm.wr_type_p t0 ^ " and " ^
			   PrintForm.wr_type_p t1)
	    | _ ->
		if t = unknown_type then
		  TypedForm (f0, t0)
		else if is_same_type t t0 then
		  f0
		else
		  panic ("typeinf:matchType: non-matching types: " ^
			   PrintForm.wr_type_p t ^ " and " ^
			   PrintForm.wr_type_p t0)
	end
    | _ -> TypedForm (f0, t0)


(*
and helperPred (f : form) (te : typeEnv) : typeEnv =
        let te1 = makePredicate f te in
	  List.append te1 te

and makePred (pred : form) (tenv : typeEnv) : typeEnv = match pred with
  | Const b ->
      begin
	match b with
	  | BoolConst _ -> tenv
	  | _ -> panic ("typeinf:makePredicate: constant of other type (" 
			^ (string_of_const (Const b)) ^ ") used as type bool")
      end
	
  | Var iden ->
      begin
	try
	  match List.assoc iden tenv with
	    | TypeApp (t, _) ->
		begin
		  match t with
		    | TypeBool -> tenv (* consistent usage, no more information *)
		    | _ -> panic ("typeinf:makePredicate: inconsistent use of identifier: " 
				  ^ iden ^ " is used as bool type and other type")
		end
	    | _ -> panic ("typeinf:makePredicate: inconsistent use of identifier: " 
			  ^ iden ^ " is used as variable and function/predicate")
	with
	  | Not_found -> (iden, mk_bool iden)
      end
	
  | Binder (binder, tvids, f) -> tenv
  | TypedForm (f, ft) -> tenv
*)


(*
	  | Const Plus | Const Minus | Const UMinus | Const Mult | Const Div | Const Mod
	  | Const Lt | Const Gt | Const LtEq | Const GtEq -> (* integer *)
*)
(* 
  | Var iden -> 
      try
	match List.assoc iden typeenv with
	  | SimpleType t -> (Some t, typeenv)
	  | Func (f, 
		  with
		      Not_found -> (None, typeenv)
  and makeIntVar f = match f with
    | Var iden -> typestore := (iden, SimpleType TypeInt) :: !typestore
    | _ -> ()

  and makeSetVar f = match f with
    | Var iden -> typestore := (iden, SimpleType TypeSet) :: !typestore
    | _ -> ()
*)

