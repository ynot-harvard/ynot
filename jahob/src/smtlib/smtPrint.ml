(** Printing {!Form} formulas to SMT-LIB format. *)

open Form
open FormUtil
open TypeVars
open TypeReconstruct
open TermRewrite
open Common

let default_opts () : options_t = 
  let smtPrint_defaults = [("TimeOut",       string_of_int !CmdLine.timeout);
			   ("MaxQuantInst",  "300");
			   ("TryHeuristics", "yes");
			   ("KeepRtrancl",   "no")
			  ] in
    map_of_list smtPrint_defaults

let heuristics_opts : options_t = 
  let smtPrint_defaults = [("TimeOut",       "20");
			   ("MaxQuantInst",  "300");
			   ("TryHeuristics", "yes");
			   ("KeepRtrancl",   "no")
			  ] in
    map_of_list smtPrint_defaults

let getOption (option_name : string) (options : options_t) : string = 
  StringMap.find option_name options

(** Indent and add backslash in front of every left and right parenthesis. *)
let format_source (s : string) : string =
  Str.global_replace (Str.regexp "{") "\\{"
    (Str.global_replace (Str.regexp "}") "\\}"
       (Str.global_replace (Str.regexp "\n") "\n\t" s))

let not_yet_declared (env : typeEnv) (i : ident) : bool =
  (not (List.exists (fun (id, _) -> id = i) env))

let get_type (env : typeEnv) (i : ident) : typeForm =
  try
    let _, ty = List.find (fun (id, _) -> id = i) env in ty
  with Not_found -> failwith ("get_type could not find type for " ^ i ^ "\n")

let declare (env : typeEnv) (i : ident) (ty : typeForm) : typeEnv =
  if (not_yet_declared env i) then
    (i, ty) :: env
  else env

let remove_declaration (env : typeEnv) (i : ident) : typeEnv =
  List.filter (fun (x, _) -> (x <> i)) env

let globalArrayObjectType = (TypeApp (TypeDefined "globalArrayObj", []))

let declare_arrayRead (env : typeEnv) (ty : typeForm) : typeEnv =
  let id = "arrayRead" in
    declare env id 
      (FormUtil.mk_fun_type 
	 [globalArrayObjectType; FormUtil.mk_object_type; FormUtil.mk_int_type]
	 ty)

let declare_arrayWrite (env : typeEnv) (ty : typeForm) : typeEnv =
  let id = "arrayWrite" in
    declare env id
      (FormUtil.mk_fun_type [globalArrayObjectType; FormUtil.mk_object_type; 
			     FormUtil.mk_int_type; ty] 
	 globalArrayObjectType)

let get_elem_type (env : typeEnv) (id : ident) : typeForm =
  let ty = get_type env id in
    match ty with
      | TypeApp(TypeArray, [_; TypeApp(TypeArray,[_; ty'])]) -> ty'
      | _ -> raise Not_found

(* Add any necessary declarations, and returns the new state. *)
let rec process_formula (env : typeEnv) (f : form) : typeEnv =
  match f with
    | (Const NullConst) ->
	(* Declare null if necessary. *)
	let f0 = Form.string_of_const NullConst in 
	  declare env f0 FormUtil.mk_object_type
    | App(Const ArrayRead, (Var v :: frest)) ->
	let env =
	  try
	    let ty = get_elem_type env v in
	    let env = remove_declaration env "arrayRead" in
	      declare_arrayRead env ty
	  with Not_found -> env in
	let env = remove_declaration env v in
	let env = declare env v globalArrayObjectType in
	  List.fold_left process_formula env frest
    | App(Const ArrayRead, fs) ->
	let env = declare_arrayRead env FormUtil.mk_object_type in
	  List.fold_left process_formula env fs
    | App(Const ArrayWrite, (Var v :: frest)) ->
	let env =
	  try
	    let ty = get_elem_type env v in
	    let env = remove_declaration env "arrayWrite" in
	      declare_arrayWrite env ty
	  with Not_found -> env in
	let env = remove_declaration env v in
	let env = declare env v globalArrayObjectType in
	  List.fold_left process_formula env frest
    | App(Const ArrayWrite, fs) ->
	let env = declare_arrayWrite env FormUtil.mk_object_type in
	  List.fold_left process_formula env fs
    | App(fa, fl) -> 
	List.fold_left process_formula (process_formula env fa) fl
    | Binder(_, _, fb) -> process_formula env fb
    | TypedForm(ft, _) -> 
	    (* There shouldn't be any typed formulas at this point. *)
	failwith ("process_formula: can't handle " ^ (PrintForm.string_of_form f))
    | _ -> env

let process_assumptions (env: typeEnv) (fs : form list) : typeEnv =
  List.fold_left process_formula env fs

let string_of_simpletype (st : simpleType) : string =
  match st with
    | TypeUnit -> "Unit"
    | TypeInt -> "Int"
    | TypeString -> "String"
    | TypeBool -> "Bool"
    | TypeObject -> "Obj"
    | TypeSet -> "Set"
    | TypeList -> "List"
    | TypeArray -> "Obj" (* SMT-LIB Array is for integer arrays only *)
    | TypeDefined(i) -> i

let rec string_of_typeform (str : string) (tf : typeForm) : string =
  let strnew = if (not (str = "")) then (str ^ " ") else str in
    match tf with
      | TypeApp(st, []) -> 
	  strnew ^ (string_of_simpletype st)
      | TypeApp(st, tl) ->
	  List.fold_left string_of_typeform (strnew ^ (string_of_simpletype st)) tl
      | TypeFun(args, res) ->
	  List.fold_left string_of_typeform str (args @ [res])
      | TypeVar i -> strnew ^ i
      | TypeProd tys ->
	  List.fold_left string_of_typeform str tys
      | _ -> failwith 
	  ("string_of_typeform: Not yet implemented:\n" ^ 
	     (MlPrintForm.string_of_type tf))

let smt_ident (i : ident) : string =
  let nocarets = Str.global_replace (Str.regexp "\\^") "$" i in
  let rec replace_dots (s : string) : string =
    try
      let j = Str.search_forward (Str.regexp "\\.") s 0 in
	(Str.string_before s j) ^ 
	  replace_dots (String.capitalize (Str.string_after s (j + 1)))
    with Not_found -> s in
    String.uncapitalize (replace_dots nocarets)

let smt_extras (env : typeEnv) : string =
  let rec get_sorts (tfl : typeForm list) (tf : typeForm) : (typeForm list) =
    match tf with
      | TypeApp(st0, tfl0) ->
	  let tf0 = TypeApp (st0, []) in
	    if (st0 = TypeInt || st0 = TypeSet || st0 = TypeArray ||
		(List.exists (fun (x) -> x = tf0) tfl)) then
	      List.fold_left get_sorts tfl tfl0
	    else
	      List.fold_left get_sorts (tf0 :: tfl) tfl0
      | TypeFun(args, ret) ->
	  get_sorts (List.fold_left get_sorts tfl args) ret
      | TypeProd tfl0 ->
	  List.fold_left get_sorts tfl tfl0
      | _ -> if (not (List.exists (fun(x) -> x = tf) tfl)) then (tf :: tfl) else tfl in
  let make_extrasorts (str : string) (tf : typeForm) : string =
    match tf with
      | TypeApp(TypeBool, []) -> str
      | _ -> str ^ "  :extrasorts (" ^ (string_of_typeform "" tf) ^ ")\n" in
  let extrasorts_list = snd (List.split env) in
  let extrasorts = List.fold_left make_extrasorts "" 
    (List.fold_left get_sorts [] extrasorts_list) in
  let func_and_pred_string (str : string) ((id0, ty) : typedIdent) : string =
    let id = smt_ident id0 in
      match normalize_type ty with
	| TypeApp(TypeBool, []) ->
	    str ^ "  :extrapreds ((" ^ id ^ "))\n"
	| TypeApp(sta, []) -> 
	    str ^ "  :extrafuns  ((" ^ id ^ " " ^ (string_of_simpletype sta) ^ "))\n"
	| TypeApp(TypeSet, TypeApp(sta, []) :: []) ->
	    str ^ "  :extrapreds ((" ^ id ^ " " ^ (string_of_simpletype sta) ^ "))\n"
	| TypeApp(TypeArray, [_; ret]) ->
	    str ^ "  :extrafuns  ((" ^ id ^ " " ^ (string_of_simpletype TypeArray) ^ 
	      " " ^ (string_of_typeform "" ret) ^ "))\n"
	| TypeFun(args, TypeApp(TypeBool, [])) ->
	    str ^ "  :extrapreds ((" ^ id ^ " " ^ 
	      (List.fold_left string_of_typeform "" args) ^ "))\n"
	| TypeFun(args, TypeApp(TypeSet, [set_of])) ->
	    str ^ "  :extrapreds ((" ^ id ^ " " ^
	      (List.fold_left string_of_typeform "" args) ^ " " ^
	      (string_of_typeform "" set_of) ^ "))\n"
	| TypeFun(args, ret) ->
	    str ^ "  :extrafuns  ((" ^ id ^ " " ^ 
	      (List.fold_left string_of_typeform "" args) ^ " " ^
	      (string_of_typeform "" ret) ^ "))\n"
	| TypeVar i ->
	    str ^ "  :extrafuns  ((" ^ id ^ " " ^ i ^ "))\n"
	| _ -> 
	    failwith ("smt_extras: " ^ id ^ " " ^ (PrintForm.string_of_type ty)) in
    extrasorts ^ List.fold_left func_and_pred_string "" env

let fresh_smt_var_counter = (ref 0 : int ref)
let fresh_smt_var (i : ident) : ident =
  fresh_smt_var_counter := !fresh_smt_var_counter + 1;
  (i ^ "_smt_" ^ (string_of_int !fresh_smt_var_counter))

let rec smt_form (f : form) (defs : form list) : (form * (form list)) =
  (* print_string ("smt_form: " ^ (MlPrintForm.string_of_form f) ^ "\n"); *)
  match f with
    | App(Const FieldRead, [App(Const FieldWrite, [f0; f1; f2]); f3])
    | App(App(Const FieldWrite, [f0; f1; f2]), [f3])
    | App(Const FieldWrite, [f0; f1; f2; f3]) ->
	smt_form
	  (FormUtil.mk_ite
	     (FormUtil.mk_eq (f1, f3), f2, (FormUtil.mk_fieldRead f0 f3))) defs
    | App(App(Const ArrayWrite, [arrayState; array0; index0; val0]), [array1; index1])
	(* This is not the right way to do an array read, but let's handle it anyhow. *)
    | App(Const ArrayRead, [App(Const ArrayWrite, [arrayState; array0; index0; val0]); array1; index1]) ->
	let arrReadVar = Var (fresh_smt_var "arrayRead_") in
	let fDef =
	  begin
	    let fEqRes = FormUtil.mk_eq (arrReadVar, val0) in
	    let fNeqRes = FormUtil.mk_eq (arrReadVar, FormUtil.mk_arrayRead arrayState array1 index1) in
	    let fIndEq = FormUtil.mk_eq (index0, index1) in
	      if (array0 = array1) then
		if (index0 = index1) then
		  fEqRes
		else
		  let fEqImpl = FormUtil.smk_impl (fIndEq, fEqRes) in
		  let fNeqImpl = FormUtil.smk_impl (FormUtil.smk_not fIndEq, fNeqRes) in
		    FormUtil.smk_and [fEqImpl; fNeqImpl]
	      else
		let fArrEq = FormUtil.mk_eq (array0, array1) in
		let fCond = FormUtil.smk_and [fArrEq; fIndEq] in
		let fEqImpl = FormUtil.smk_impl (fCond, fEqRes) in
		let fNeqImpl = FormUtil.smk_impl ((FormUtil.smk_not fCond), fNeqRes) in
		  FormUtil.smk_and [fEqImpl; fNeqImpl]
	  end
	in
	let fAux, defs0 = smt_form fDef defs in
	  (arrReadVar, (fAux :: defs0))
    | App(Const Elem, _) ->
	failwith ("smt_form unexpected form: " ^ (PrintForm.string_of_form f) ^ "\n")
    | App(Const Eq, [f1; Binder(Lambda, til, f2)])
    | App(Const Eq, [Binder(Lambda, til, f2); f1]) ->
	(* Turn lambdas into universal quantification. *)
	let til0 = List.map (fun (v, t) -> ("?" ^ v, t)) til in
	let old_ids, _ = List.split til in
	let new_ids = List.map (fun (id) -> ("?" ^ id)) old_ids in
	let new_vars = List.map (fun (id) -> (Var id)) new_ids in
	let rename_map = List.combine old_ids new_vars in
	let f10, defs0 = smt_form f1 defs  in
	let f20, defs1 = smt_form (subst rename_map f2) defs0 in
	let to_conjoin, defs2 = List.partition 
	  (fun (f) -> List.exists (contains_var f) new_ids) defs1 in
	let f0 = App(Const Eq, [App(f10, new_vars); f20]) in
	  (Binder(Forall, til0, smk_and (f0 :: to_conjoin)), defs2)
    | App(Binder(Lambda, til, f0), f1) ->
	(* Remove lambda by applying to argument. *)
	let (il, _) = List.split til in
	let rename_map = List.combine il f1 in
	  smt_form (subst rename_map f0) (List.map (subst rename_map) defs)
    | App(Const Ite, [App(Const Eq, [f0; f1]); f2; f3]) when (f0 = f1) ->
	smt_form f2 defs
    | App(Const Ite, [(Const (BoolConst true)); fresult; _])
    | App(Const Ite, [(Const (BoolConst false)); _; fresult]) ->
	smt_form fresult defs
    | App(Const Ite, [fCond; fTrue; fFalse]) ->
	(* Remove Ite's altogether. *)
	let fCond0, defs0 = smt_form fCond defs in
	let fTrue0, defs1 = smt_form fTrue defs0 in
	let fFalse0, defs2 = smt_form fFalse defs1 in
	let iteVar = Var (fresh_smt_var "ite_") in
	let fTrueRes = FormUtil.mk_eq (iteVar, fTrue0) in
	let fTrueImpl = FormUtil.smk_impl (fCond0, fTrueRes) in
	let fFalseRes = FormUtil.mk_eq (iteVar, fFalse0) in
	let fFalseImpl = FormUtil.smk_impl ((FormUtil.smk_not fCond0), fFalseRes) in
	let fAux = FormUtil.smk_and [fTrueImpl; fFalseImpl] in
	  (iteVar, (fAux :: defs2))
    | App(Const Ite, _) ->
	(* All Ite's should have three arguments, so if it's not
	   caught by the previous case, there's something wrong with
	   the formula. *)
	failwith ("smt_form: Can't convert " ^ (MlPrintForm.string_of_form f))
    | App(fa0, fl0) -> 
	(* This is the catch-all case for App. *)
	let (fa1, defs0) = smt_form fa0 defs in
	let (fl1, defs1) = smt_form_list fl0 defs0 in
	  (App(fa1, fl1), defs1)
    | Binder(Forall as b, til, f0) 
    | Binder(Exists as b, til, f0) ->
	(* Prepend '?' to names of quantified variables to conform to SMTLIB standard. *)
	let til0 = List.map (fun(v, t) -> ("?" ^ v, t)) til in
	let old_ids, _ = List.split til in
	let new_ids = List.map (fun (id) -> ("?" ^ id)) old_ids in
	let new_vars = List.map (fun (id) -> (Var id)) new_ids in
	let rename_map = List.combine old_ids new_vars in
	let (f00, defs0) = smt_form (subst rename_map f0) (List.map (subst rename_map) defs) in
	let to_conjoin, defs1 = List.partition 
	  (fun (f) -> List.exists (contains_var f) new_ids) defs0 in
	  (Binder(b, til0, (smk_and (f00 :: to_conjoin))), defs1)
    | Binder(b0, til0, f0) -> 
	(* This is the catch-all case for Binder. *)
	let f00, defs0 = smt_form f0 defs in
	let ids, _ = List.split til0 in
	let to_conjoin, defs1 = List.partition
	  (fun (f) -> List.exists (contains_var f) ids) defs0 in
	  (Binder(b0, til0, (smk_and (f00 :: to_conjoin))), defs1)
    | TypedForm(f0, t0) ->
	(* There should be no TypedForm's passed to smt_form. It makes
	   matching too painful. *)
	failwith ("smt_form: Can't convert " ^ (MlPrintForm.string_of_form f))
    | _ -> f, defs (* This is the catch-all case for Var's and Const's. *)
and smt_form_list (fl : form list) (defs : form list) : (form list) * (form list) =
  match fl with
    | [] -> (fl, defs)
    | f0 :: frest -> let (f1, defs0) = smt_form f0 defs in
      let (fl0, defs1) = smt_form_list frest defs0 in
	(f1 :: fl0, defs1)

let rec smt_string (f : form) : string =
  let check_type ((_, ty) : typedIdent) : unit =
    match ty with
      | TypeVar _ | TypeApp(_, []) -> ()
      | _ -> failwith ("Formulas in smtlib cannot have quantification over type: " ^ 
			 (PrintForm.string_of_type ty) ^ "\n")
  in
  match f with
    | (Var i) -> smt_ident i
    | (Const Not) -> "not"
    | (Const Or) -> "or"
    | (Const And) -> "and"
    | (Const Ite) -> "ite"
    | (Const Iff) -> "iff"
    | (Const UMinus) -> "~"
    | (Const (IntConst i)) -> if i < 0 then Printf.sprintf ("(~ %d)") (- i) else string_of_int i
    | (Const c) -> Form.string_of_const c
    | App(Const Tuple, fs) -> smt_string_list fs
    | App(Var rtrancl, [p; t1; t2]) when rtrancl = str_rtrancl ->
	let st1 = smt_string t1 in
	let st2 = smt_string t2 in
	let sp = smt_string p in
	Printf.sprintf "(or (= %s %s) (%s %s %s : transclose))" st1 st2 sp st1 st2
    | App(Const fop, fs) when (fop = FieldRead || fop = FieldWrite) ->
	"(" ^ (smt_string_list fs) ^ ")"
    | App(Const ArrayRead, [f0; f1; f2]) ->
	"(arrayRead " ^ smt_string f0 ^ " " ^ smt_string f1 ^ " " ^ smt_string f2 ^ ")"
    | App(Const Elem, _) ->
	failwith ("smt_string did not expect: " ^ (PrintForm.string_of_form f) ^ "\n")
    | App(App(f0, fs0), fs1) ->
	smt_string (App(f0, fs0 @ fs1))
    | App(f1, fs) -> "(" ^ (smt_string f1) ^ " " ^ (smt_string_list fs) ^ ")"
    | Binder(Forall, til, f1) ->
	List.iter check_type til;
	"(forall " ^ (smt_typedident_list til) ^ " " ^ (smt_string f1) ^ ")"
    | Binder(Exists, til, f1) ->
	List.iter check_type til;
	"(exists " ^ (smt_typedident_list til) ^ " " ^ (smt_string f1) ^ ")"
    | _ -> 
	print_string ("\n" ^ (MlPrintForm.string_of_form f) ^ "\n");
	failwith ("smt_string: Can't convert " ^ (PrintForm.string_of_form f))
and smt_string_list (fs : form list) : string =
  match fs with
    | [] -> ""
    | [f0] -> smt_string f0
    | f0 :: f1 -> (smt_string f0) ^ " " ^ (smt_string_list f1)
and smt_typedident_list (til : typedIdent list) : string =
  match til with
    | [] -> ""
    | [ti0] -> smt_typedident ti0
    | ti0 :: ti1 -> (smt_typedident ti0) ^ " " ^ (smt_typedident_list ti1)
and smt_typedident (i, t) : string =
  "(" ^ (smt_ident i) ^ " " ^ (string_of_typeform "" t) ^ ")"

(** This pass is no longer in use, because it has been subsumed by
    rewrite_sets. If you want to use this pass, you must run it on
    typed form, because this translation needs the type of the set
    elements. *)
let rec translate_set_exprs (f : form) : (form) =
  match f with
    | Var _ -> f
    | Const _ -> f
    | App(Const Eq, [TypedForm (f0, TypeApp (TypeSet, [t0])); f1])
    | App(Const Eq, [f0; TypedForm (f1, TypeApp (TypeSet, [t0]))]) ->
	(match f0 with
	   | (Const EmptysetConst) ->
	       let fv = fresh_smt_var "setElem" in
	       let f2 = App (Const Elem, [(Var fv); f1]) in
	       let f3 = Binder (Forall, [(fv, t0)], (App ((Const Not), [f2]))) in
		 translate_set_exprs f3
	   | _ ->
	       let fv = fresh_smt_var "setElem" in
	       let f2 = App (Const Elem, [(Var fv); f0]) in
	       let f3 = App (Const Elem, [(Var fv); f1]) in
	       let f4 = Binder (Forall, [(fv, t0)], (App ((Const Iff), [f2; f3]))) in
		 translate_set_exprs f4)
    | App(Const Comment, [f0; f1]) -> translate_set_exprs f1 (* remove comments *)
    | App(f0, fs) ->
	let fs0 = List.map translate_set_exprs fs in
	  App((translate_set_exprs f0), fs0)
    | Binder (b0, t0, f0) -> Binder(b0, t0, (translate_set_exprs f0))
    | TypedForm (f0, t0) -> translate_set_exprs f0

(* Renames bound variables so that variable names are unique. *)
let rec unique_variables (f : form) (used : ident list) : (form * ident list) =
  match f with
    | Binder (b, [(i,t)], f0) ->
	if (List.exists (fun(x) -> x = i) used) then
	  let ni = (fresh_smt_var i) in
	  let renamed = subst [(i, (Var ni))] f0 in
	  let (f1, nused) = unique_variables renamed used in
	    (Binder(b, [(ni, t)], f1), nused)
	else
	  let (f1, nused) = unique_variables f0 (i :: used) in
	    (Binder(b, [(i, t)], f1), nused)
    | Binder (b, (i,t) :: til, f0) ->
	if (List.exists (fun(x) -> x = i) used) then
	  let ni = (fresh_smt_var i) in
	  let renamed = subst [(i, (Var ni))] (Binder(b, til, f0)) in
	  let (f1, nused) = unique_variables renamed used in
	    (Binder(b, [(ni, t)], f1), nused)
	else
	  let (f1, nused) = unique_variables (Binder(b, til, f0)) (i :: used) in
	    (Binder(b, [(i, t)], f1), nused)
    | App (f0, fs) ->
	let (f1, used0) = unique_variables f0 used in
	let (fs1, used1) = unique_variables_list fs used0 in
	  (App(f1, fs1), used1)
    | TypedForm (_,_) ->
	failwith ("unique_variables: Can't handle " ^ (PrintForm.string_of_form f))
    | _ -> (f, used)
and unique_variables_list 
    (fs : form list) (used : ident list) : (form list * ident list) =
  match fs with
    | [] -> (fs, used)
    | f0 :: fs0 ->
	let (f1, used0) = unique_variables f0 used in
	let (fs1, used1) = unique_variables_list fs0 used0 in
	  ((f1 :: fs1), used1)

(* Returns the skolemized formula and a list of the new skolem functions. *)
let rec skolemize (f : form) (til : typedIdent list) : (form * typedIdent list) =
  match f with
    | Binder (Forall, til0, f0) ->
	let (f1, til1) = skolemize f0 (til @ til0) in
	  (Binder(Forall, til0, f1), til1)
    | Binder (Exists, til0, f0) ->
	let (il, tl) = List.split til0 in
	let il0 = List.map 
	  (fun (x) -> 
	     (fresh_smt_var
		((String.uncapitalize 
		    (String.sub x 1 ((String.length x) - 1))) ^ "Sk"))) il in
	let (args, argts) = List.split til in
	let tl0 = List.map 
	  (fun (x) -> if (argts = []) then x else (FormUtil.mk_fun_type argts x)) tl in
	let til1 = List.combine il0 tl0 in
	let argvs = List.map (fun (x) -> (Var x)) args in
	let nil = List.map 
	  (fun (x) -> if (argvs = []) then (Var x) else App ((Var x), argvs)) il0 in
	let rename_map = List.combine il nil in
	let (f1, til2) = skolemize (subst rename_map f0) til in
	  (f1, til1 @ til2)
    | App (f0, fs) ->
	let (f1, til1) = skolemize f0 til in
	let (fs1, til2) = skolemize_list fs til in
	  (App (f1, fs1), til1 @ til2)
    | TypedForm (_,_) ->
	failwith ("skolemize: Can't handle " ^ (PrintForm.string_of_form f))
    | _ -> (f, [])
and skolemize_list 
    (fs : form list) (til : typedIdent list) : (form list * typedIdent list) = 
  match fs with
    | [] -> (fs, [])
    | f0 :: fs0 ->
	let (f1, til1) = skolemize f0 til in
	let (fs1, til2) = skolemize_list fs0 til in
	  ((f1 :: fs1), til1 @ til2)

(* fs0 is the to-be-processed list. fs1 is the done list. *)
let rec skolemize_assumptions (fs0 : form list) (fs1 : form list) (e : typeEnv) : 
    (form list * form list * typeEnv) =
  match fs0 with
    | [] -> ([], fs1, e) (* done *)
    | f0 :: frest -> 
	let (il, _) = List.split e in
	let (f1, _)  = unique_variables (negation_normal_form f0) il in
	let (f2, e1) = skolemize f1 [] in
	  skolemize_assumptions frest (f2 :: fs1) (e @ e1)

let process_goal (f : form) : form * typedIdent list =
  let (f0, _) = unique_variables (negation_normal_form (mk_not f)) [] in 
  let (f1, til1) = skolemize f0 [] in
  (f1, til1)

(** Remove rtrancl_pt from sequent *)
let remove_rtrancl (s : sequent) : sequent =
  let rtrancl_vs = [str_tree; str_rtrancl] in
  let remove_smart = smart_abstract_constructs (List.map (fun s -> (mk_var s, 1)) rtrancl_vs) in 
  let f = remove_smart (form_of_sequent s) in
  sequent_of_form f

(** Rewrite rule for removal of Ite *)
let rewrite_ite : rewriteRule =
  let r _ replace_map pol genv env t =
    let rec rewrite f  =
      match f with
      | App(Const Ite, [f0; f1; f2]) ->
	  (try (mk_var (fst (FormHashtbl.find replace_map f)), [])
	  with Not_found ->
	    let v = fresh_smt_var "ite" in
	    let v0 = Var v in
	    let f00, na0 = rewrite f0 in
	    let f10, na1 = rewrite f1 in
	    let f20, na2 = rewrite f2 in
	    let f11, defs0 = smt_form (FormUtil.smk_impl (f00, FormUtil.mk_eq(v0, f10))) [] in
	    let f21, defs1 = smt_form (FormUtil.smk_impl ((FormUtil.mk_not f00),
							     FormUtil.mk_eq(v0, f20))) defs0 in
	    let vdef = smk_and ([f11; f21] @ defs1) in	    
	    let new_var = mk_outer_forall pol f (mk_const_decl (v, TypeUniverse) (Some vdef)) in
	    let _ = FormHashtbl.add replace_map f (v, TypeUniverse) in
	    (v0, new_var :: na0 @ na1 @ na2))
      | App(f0, fl0) -> 
	  let f1, na0 = rewrite f0 in
	  let fl1, na1 = List.fold_right 
	      (fun f (fl1, new_vars) ->
		let f', new_vars' = rewrite f in
		(f'::fl1, new_vars' @ new_vars))  
	      fl0 ([], [])
	  in
	  (App(f1, fl1), na0 @ na1)
      | TypedForm (f', ty) -> 
	  let f'', na = rewrite f' in
	  (TypedForm (f'', ty), na)
      | _ -> (f, [])
    in rewrite t
  in (r, RewriteAtoms)

(** Rewrite rule that replaces predicates under rtrancl_pt by fresh predicate symbols *)
let rewrite_rtc : rewriteRule =
  let r call_back replace_map pol genv env f =
    let rec rewrite f =
      match f with
      | App(Var rtrancl, (Binder (Lambda, [(v1,ty1); (v2,ty2)], f') as p::args)) 
      | App(Var rtrancl, (Binder (Lambda, [(v1,ty1)], Binder (Lambda, [(v2,ty2)], f')) as p::args))
      | App(TypedForm (Var rtrancl, _), (Binder (Lambda, [(v1,ty1); (v2,ty2)], f') as p::args)) 
      | App(TypedForm (Var rtrancl, _), (Binder (Lambda, [(v1,ty1)], Binder (Lambda, [(v2,ty2)], f')) as p::args))
	when rtrancl = str_rtrancl ->
	  let p1, aux_vars =
	    try (mk_var (fst (FormHashtbl.find replace_map p)), [])
	    with Not_found ->
	      let vs = [(v1, ty1); (v2, ty2)] in
	      let p1_name = fresh_smt_var "rtc_p" in
	      let p1 = Var p1_name in
	      let p1_def0 = smk_foralls (vs, mk_iff(App(p1, [mk_var v1; mk_var v2]), f')) in	    
	      let p1_def, aux_vars' = call_back pol env p1_def0 in
	      let p1_type = TypeFun ([ty1; ty2], mk_bool_type) in
	      let new_var = mk_outer_forall pol p (mk_const_decl (p1_name, p1_type) (Some p1_def)) in
	      let _ = FormHashtbl.add replace_map p (p1_name, p1_type) in
	      (p1, new_var :: aux_vars')
	  in (App (Var str_rtrancl, (p1::args)), aux_vars)
      | _ -> (f, [])
    in rewrite f
  in (r, RewriteAtoms)

let convert_to_smt_string 
    (s : sequent) (name : string) (env : typeEnv) (fs : form list) (goal : form) : string =
  let smt_header_string 
      (s : sequent) (name : string) (logic : string) : string = 
    "(benchmark " ^ name ^ "\n" ^
      "  :source {\n" ^ 
      "\t" ^ (format_source (string_of_sequent s)) ^ "\n" ^
      "   }\n" ^
      "  :logic " ^ logic ^ "\n" in
  let header = smt_header_string s name "AUFLIA" in
  let extras = smt_extras env in
  let smt_assumptions (str : string) (f : form) : string =
    let str0 = smt_string f in
    if (not (str0 = "")) then
      str ^ "  :assumption " ^ str0 ^ "\n"
    else str in
  let assumptions = List.fold_left smt_assumptions "" fs in
  let formula = "  :formula    " ^ (smt_string goal) ^ "\n" in
    header ^ "\n" ^ extras ^ "\n" ^ assumptions ^ "\n" ^ formula ^ 
      "\n  :status     unknown\n)"

(* This procedure applies rewriter until a fixed point is reached.
   The rewriter should return the rewritten formula and flag that
   indicates whether the formula has changed.
*)
let rec fixed_point_rewrite (rewriter : form -> form * bool) (f : form): form =
  let f0, changed = rewriter f in
    (* iterate until a fixed point is reached *)
    if (changed) then
      fixed_point_rewrite rewriter f
    else f

(* This pass rewrites the very simple case of an array read which either:
   (1) reads the result of the preceding write or
   (2) is orthogonal to the preceding write
   in a way in which we can determine this from the text of the formula.

   This pass is best used with fixed_point_rewrite, to handle cases such as:
   arrayRead (arrayWrite (arrayWrite a0 0 v0) a0 1 v1) a0 0

   In one pass, this would reduce to:
   arrayRead (arrayWrite a0 0 v0) a0 0

   whereas if we iterate to a fixed point, we would get: v0
*)
let rec simple_array_rewrite (f : form) : form * bool = 
  match f with
    | Var _ | Const _ -> f, false
    | App(App(Const ArrayWrite, [arrayState; array0; index0; val0]), [array1; index1]) 
	(* This is not the right way to do an array read, but let's handle it anyhow. *)
    | App(Const ArrayRead, [App(Const ArrayWrite, [arrayState; array0; index0; val0]); array1; index1])
	when (array0 = array1) ->
	begin
	  if (index0 = index1) then
	    let val1, _ = simple_array_rewrite val0 in
	      (val1, true)
	  else
	    match index0, index1 with
	      | Const (IntConst i), Const (IntConst j) ->
		  assert (not (i = j));
		  let as0, _ = simple_array_rewrite arrayState in
		  let a0, _ = simple_array_rewrite array0 in
		  let f0 = App(Const ArrayRead, [as0; a0; index1]) in
 		    (f0, true)
	      | _ ->
		  let args0, a0changed = List.split (List.map simple_array_rewrite [arrayState; array0; index0; val0]) in
		  let args1, a1changed = List.split (List.map simple_array_rewrite [array1; index1]) in
		  let changed = List.exists (fun(b) -> b) (a0changed @ a1changed) in
		    (App(Const ArrayRead, (App(Const ArrayWrite, args0) :: args1)), changed)
	end
    | App(f0, fl0) ->
	let f1, fchanged = simple_array_rewrite f0 in
	let fl1, flchanged = List.split (List.map simple_array_rewrite fl0) in
	let changed = fchanged || List.exists (fun(b) -> b) flchanged in
	  (App(f1, fl1), changed)
    | Binder(bk0, til0, f0) ->
	let f1, changed = simple_array_rewrite f0 in
	  (Binder(bk0, til0, f1), changed)
    | TypedForm _ ->
	(* There shouldn't be any typed formulas at this point. *)
	failwith ("simple_array_rewrite: can't handle " ^ (PrintForm.string_of_form f))

let simplify (goal : form) (assumptions : form list) : form * form list =
  let is_const_false (f : form) : bool = 
    (f = Const (BoolConst false)) in
  let not_const_false (f : form) : bool = 
    (f <> Const (BoolConst false)) in
  let is_const_true (f : form) : bool = 
    (f = Const (BoolConst true)) in  
  let not_const_true (f : form) : bool = 
    (f <> Const (BoolConst true)) in  
  let rec simplify_form (f : form) : form =
    match f with
      | App(Const Or, fs) ->
	  if (List.exists is_const_true fs) then
	    Const (BoolConst true)
	  else
	    let fs' = List.filter not_const_false fs in
	      if (fs' = []) then
		Const (BoolConst false)
	      else 
		App(Const Or, fs')
      | App(Const And, fs) ->
	  if (List.exists is_const_false fs) then
	    Const (BoolConst false)
	  else 
	    let fs' = List.filter not_const_true fs in
	      if (fs' = []) then
		Const (BoolConst true)
	      else
		App(Const And, fs')
      | App(f0, fs) ->
	  App((simplify_form f0), (List.map simplify_form fs))
      | Binder(b, til, f0) ->
	  Binder(b, til, (simplify_form f0))
      | TypedForm(f0, ty) ->
	  TypedForm((simplify_form f0), ty)
      | _ -> f in
  let rec split_assumption (f : form) : form list =
    match f with
      | App(Const And, fs0) -> 
	  List.flatten (List.map split_assumption fs0)
      | _ -> [f]
  in
  let goal = simplify_form (FormUtil.flatten goal) in
  let assumptions = List.map FormUtil.flatten assumptions in
  let assumptions = List.map simplify_form assumptions in
  let assumptions = List.flatten (List.map split_assumption assumptions) in
    (goal, assumptions)

(* This is a shorthand for printing debug messages for this module using the smt flag. *)
let debug_id : int = Debug.register_debug_module "SmtPrint"
let debug_msg : (string -> unit) = Debug.debug_msg debug_id
let debug_is_on () : bool = Debug.debug_is_on debug_id

let process_sequent (o : options_t) (s0 : sequent) : (typeEnv * (form list) * form) =
  (* Remove rtrancl_pt and tree *)
  let s = if flag_positive o "KeepRtrancl" then s0 else remove_rtrancl s0 in 
  (* let _ = print_endline ( "\n" ^ string_of_sequent s) in *) 
  (* Eliminate free variables *)
  let s = elim_fv_in_seq false s in
  (* Get types *)
  let f = FormUtil.form_of_sequent s in
  let env0 = get_annotated_types f in
  (* Resolve ambiguous operators and remove lambda abstraction *)
  let f0 = disambiguate (unlambda f) in
  (* Rewrite set expressions and higher order constructs *)
  let rewrite_rules =
    if flag_positive o "KeepRtrancl" then
      [rewrite_tree; 
       rewrite_function_eq;
       rewrite_pointsto;
       rewrite_FieldRead_FieldWrite;
       rewrite_rtc]
    else 
      [rewrite_function_eq;
       rewrite_pointsto;
       rewrite_FieldRead_FieldWrite]
  in
  let f1, env = TermRewrite.rewrite true rewrite_rules env0 f0 in
  let f1, env = TermRewrite.rewrite true [rewrite_sets] env (elim_quants f1) in
  let f1, env = TermRewrite.rewrite_elems f1 env in
  let f1, env = TermRewrite.rewrite_tuples (Hashtbl.create 10) f1 env in
  let _ = debug_msg ("after rewriting:\n" ^ PrintForm.string_of_form f1 ^ "\n") in
  (* Remove types to make formulas easier to process. *)
  let f2, defs = smt_form 
    (fixed_point_rewrite simple_array_rewrite 
       (FormUtil.remove_typedform f1)) [] in
  let assumptions, to_prove = sequent_of_form f2 in
  let f20 = form_of_sequent (assumptions @ defs, to_prove) in
    (* Rewrite Ite *)
  let f21, env = TermRewrite.rewrite true [rewrite_ite] env f20 in 
  (* Get types for introduced ite variables. *)
  let f22, env = TypeReconstruct.reconstruct_types env f21 in
  let fs, rhs = sequent_of_form (unnotate_all_types (disambiguate f22)) in
  let f3, sfs = process_goal rhs in
  let _, fs0, env0 = skolemize_assumptions fs [] (sfs @ env) in
  let f3, fs0 = simplify f3 fs0 in
  let env0 = process_formula (process_assumptions env0 fs0) f3 in
    (env0, fs0, f3)
	
let cvcl_command o (in_fn : string) (out_fn : string) : string = 
  let timeout = getOption "TimeOut" o in
  let max_quant_inst = getOption "MaxQuantInst" o in
  let transclose = if flag_positive o "KeepRtrancl" then "+trans-closure " else "" in
  ("cvcl " ^ transclose ^ 
   " -max-quant-inst " ^ max_quant_inst ^ 
   " -timeout " ^ timeout ^ 
   " -lang smtlib " ^ in_fn ^ " > " ^ out_fn)

let infile_counter = (ref 0 : int ref)
let incr_infile () =
    infile_counter := !infile_counter + 1
let incr_infile_if_debug () =
  if (debug_is_on ()) then (incr_infile ())
let next_infile () : string = 
  "vc" ^ (string_of_int !infile_counter) ^ ".smt"

let outfile_counter = (ref 0 : int ref)
let incr_outfile () =
    outfile_counter := !outfile_counter + 1
let next_outfile () : string =
  "cvcl" ^ (string_of_int !outfile_counter) ^ ".out"

type cvcl_result = Proved | NotProved | TooManyQuantifiers

let check_cvcl_results (fn : string) : cvcl_result =
  let outfile = open_in fn in
    try
      let line = input_line outfile in
      let _ = close_in outfile in
      let valid_regexp = Str.regexp "Valid" in
      let unsat_regexp = Str.regexp "Unsatisfiable" in
      let invalid_regexp = Str.regexp "Not Valid" in
      let sat_regexp = Str.regexp "Satisfiable" in
      let unknown_regexp = Str.regexp "Unknown" in
	if ((Str.string_match valid_regexp line 0) || 
	      (Str.string_match unsat_regexp line 0)) then
	  (debug_msg "Proved by cvcl.\n"; Proved)
	else
	  (if (Str.string_match unknown_regexp line 0) then
	     (debug_msg "There may be too many quantifiers.\n"; 
	      TooManyQuantifiers)
	   else
	     (if ((Str.string_match invalid_regexp line 0) ||
		    (Str.string_match sat_regexp line 0)) then
		debug_msg ("Disproved by cvcl.\n")
	      else
		debug_msg ("cvcl error.\n");
	      debug_msg ("Please see " ^ fn ^ " for complete output.\n");
	      NotProved))
    with End_of_file -> NotProved

let report_timeout (name : string) (o : options_t) : unit =
  Util.msg ("Failed to prove using " ^ name ^ " within the given timeout of " ^
	      (getOption "TimeOut" o) ^
	      "s.\nUse \'-timeout <seconds>\' to increase timeout.\n")

(* The suppress_errs flag was added for the -bohne option, which uses
   cvcl to prove loop invariants. We may want to specialize this
   further using a callback function for error messages, but for now,
   this will avoid the whole problem of the timeout errors that get
   spit out. *)
let invoke_cvcl (o : options_t)
    (s : sequent) (env : typeEnv) (fs : form list) (f : form) (suppress_errs : bool) : cvcl_result =
  let in_fn = (next_infile ()) in
  let fq_in_fn = Util.tmp_name in_fn in
  let fq_out_fn = Util.tmp_name (next_outfile ()) in
  let infile = open_out fq_in_fn in
  let smt_str = (convert_to_smt_string s in_fn env fs f) in
    output_string infile smt_str;
    close_out infile;
    try
      debug_msg ("Invoking cvcl on " ^ in_fn ^ ".\n");
      let exit_code = Util.run_with_timeout (cvcl_command o fq_in_fn fq_out_fn) !CmdLine.timeout in
	if (exit_code = 0) then
	  (check_cvcl_results fq_out_fn)
	else if suppress_errs then
	  NotProved
	else ((report_timeout "cvcl" o); NotProved)
    with Failure x -> Util.warn x; NotProved

let rec try_one_quantified_form (s : sequent) (env : typeEnv) (nqfs : form list) 
    (totry : form list) (f : form) (suppress_errs : bool) (o : options_t) : bool =
  match totry with
    | [] -> false
    | next :: rest ->
	let result = invoke_cvcl o s env (next :: nqfs) f suppress_errs in
	  match result with
	    | Proved -> true
	    | NotProved | TooManyQuantifiers ->
		(try_one_quantified_form s env nqfs rest f suppress_errs o)

let rec try_fewer_quantifiers (s : sequent) (env : typeEnv) (nqfs : form list) 
    (qfs0 : form list) (qfs1 : form list) (f : form) (suppress_errs : bool) 
    (o : options_t) : bool =
  match qfs0 with
    | [] -> false
    | next :: qfs -> 
	let result = invoke_cvcl o s env (nqfs @ qfs) f suppress_errs in
	  match result with
	    | Proved -> true
	    | NotProved | TooManyQuantifiers ->
		(try_fewer_quantifiers s env nqfs qfs (next :: qfs1) f suppress_errs o)

let try_heuristics (s : sequent) (env : typeEnv) (assumptions : form list) (goal : form) 
    (suppress_errs : bool) (o : options_t) : bool =
  let is_quantified (f : form) : bool =
    match f with
      | Binder(Forall, _, _)
      | Binder(Exists, _, _) -> true
      | _ -> false in
  let (qfs, nqfs) = List.partition is_quantified assumptions in
    ((try_fewer_quantifiers s env nqfs qfs [] goal suppress_errs o) ||
       (try_one_quantified_form s env nqfs qfs goal suppress_errs o))

let cvcl_prove (suppress_errs : bool) (s1 : sequent) (options : options_t) : bool =
  let s = (List.map remove_comments (fst s1), remove_comments (snd s1)) in
  let options = merge_opts (default_opts ()) options in
  try
    let (env, fs, f) = (process_sequent options s) in
    let result = invoke_cvcl options s env fs f suppress_errs in
      match result with
	| Proved -> incr_infile_if_debug (); true
	| NotProved -> incr_infile (); false
	| TooManyQuantifiers -> incr_infile ();
	    if flag_positive options "TryHeuristics" then
	      (try_heuristics s env fs f suppress_errs heuristics_opts)
	    else false
  with Failure x -> incr_infile (); Util.warn x; false


