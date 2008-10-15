(** Print MONA formulas and programs *)

open MonaForm

let keywords = List.fold_left (fun tbl keyw -> Hashtbl.add tbl keyw true; tbl)  
    (Hashtbl.create 54)
    ["ws1s"; "ws2s"; "m2l-str"; "m2l-tree"; "guide"; "universe"; "include";
     "assert"; "execute"; "const"; "defaultwhere1"; "defaultwhere2";
     "var0"; "var1"; "var2"; "tree"; "macro"; "pred"; "allpos"; "type";
     "true"; "false"; "in"; "notin"; "empty"; "restrict"; "export"; "import";
     "ex0"; "ex1"; "ex2"; "all0"; "all1"; "all2"; "let0"; "let1"; "let2";
     "prefix"; "root"; "in_state_space"; "variant"; "sometype"; "min"; "max";
     "pconst"; "union"; "inter"; "tree_root"; "union"; "inter"; "succ";
     "const_tree"; "where"]
    

(** Printing comma separated lists, etc. *)

let opsl_convert op empty convert skip_first ls =
  let csl' ls = String.concat op (List.map convert ls) in
  if not skip_first then match ls with
  | [] -> empty
  | _ -> op ^ csl' ls
  else match ls with
  | [] -> empty
  | _ -> csl' ls

let csl_convert b ls = opsl_convert ", " "" b ls

let csl = csl_convert (fun x -> x) 

let print_opsl_convert chan op empty p skip_first ls = 
  let csl' ls = List.iter (fun x -> output_string chan op; p x) ls in
  if not skip_first then match ls with
  | [] -> output_string chan empty
  | _ -> csl' ls
  else match ls with
  | x::ls -> p x; csl' ls
  | [] -> output_string chan empty

let print_csl_convert chan b ls = print_opsl_convert chan ", " "" b ls

let print_csl chan = print_csl_convert chan (output_string chan)

let mask_ident x0 = 
  let x = Util.replace_dot_with_uscore x0 in
  let masked_x = "$" ^ x in
  try
    let _ = Hashtbl.find keywords x in
    masked_x
  with Not_found -> x

let wrap s =
  let margin = 60 in
  let eol = '\n' in
  let isBreakable ch = (ch=' ') || (ch=eol) in
  let res = String.copy s in
  let rec rpl pos =
    if pos < String.length res then
      if isBreakable res.[pos] then
        (String.set res pos eol;
         rpl (pos + margin))
      else rpl (pos+1)
    else res
  in rpl margin

let csl_mask = csl_convert (fun x -> mask_ident x)

let print_csl_mask chan = print_csl_convert chan (fun x -> output_string chan (mask_ident x))

let convert_varwhere c (v, fopt) =
    match fopt with 
    | None -> mask_ident v
    | Some f -> mask_ident v ^ " where " ^ c f

let print_varwhere chan c (v, fopt) =
    match fopt with 
    | None -> output_string chan (mask_ident v)
    | Some f -> output_string chan (mask_ident v); output_string chan " where "; c chan f
    
  
let succ_to_string succs = 
  String.concat "" 
    (List.map (fun s -> match s with L -> "0" | R -> "1") succs)

(** Convert MONA formula to string *)

let form_to_string f =
  let strPrefix t = "^ " ^ t 
  and strSucc t succs = t ^ "." ^ succ_to_string succs
  and strTreeSucc t e v c =  "succ(" ^ csl true [t;e;v;c] ^ ")"
  and strIntConst i = Printf.sprintf "%d" i
  and strPlus t i = Printf.sprintf "%s + %d" t i
  and strMinus t i = Printf.sprintf "%s - %d" t i
  and strMax t = "max(" ^ t ^ ")"
  and strMin t = "min(" ^ t ^ ")"
  and strRoot1 = "root"
  and strTreeRoot t = "tree_root(" ^ t ^ ")" 
  and strEmptyset = "empty"
  and strSet ts = "{" ^ csl true ts ^ "}"
  and strUnion t1 t2 = "(" ^ t1 ^ " union " ^ t2 ^ ")"
  and strInter t1 t2 = "(" ^ t1 ^ " inter " ^ t2 ^ ")"
  and strDiff t1 t2 = "(" ^ t1 ^ "\\" ^ t2 ^ ")"
  and strConstTree t v ct = "const_tree(" ^ t ^ ", " ^ mask_ident v ^ ", " ^ ct ^ ")"
  and strNot f = "~ " ^ f
  and strAnd = " & "
  and strOr = " | "
  and strImpl f1 f2 = f1 ^ " => " ^ f2
  and strIff f1 f2 = f1 ^ " <=> " ^ f2
  and strRestrict s = "restrict(" ^ s ^ ")"
  and strPred p es = match es with 
  | [] -> mask_ident p 
  | _ -> mask_ident p ^ "(" ^ csl_mask true es ^ ")"
  and strExport fname f = "export(\"" ^ fname ^ "\" " ^ f ^ ")"
  and strImport fname vs = 
    let vlist = csl_convert (fun (v,var) -> mask_ident v ^ " -> " ^ mask_ident var) false vs in
    "import (\"" ^ fname ^ "\"" ^ vlist ^ ")"
  and strExists0 = "ex0 "
  and strForall0 = "all0 "
  and strExists1 = "ex1 "
  and strForall1 = "all1 "
  and strExists2 = "ex2 "
  and strForall2 = "all2 "
  and strLet0 = "let0 " 
  and strLet1 = "let1 " 
  and strLet2 = "let2 " 
  and strTrue = "true"
  and strFalse = "false"
  and strEq t1 t2 = t1 ^ " = " ^ t2
  and strNeq t1 t2 = t1 ^ " ~= " ^ t2
  and strLt t1 t2 = t1 ^ " < " ^ t2
  and strGt t1 t2 = t1 ^ " > " ^ t2
  and strLeq t1 t2 = t1 ^ " <= " ^ t2
  and strGeq t1 t2 = t1 ^ " >= " ^ t2
  and strSub t1 t2 = t1 ^ " sub " ^ t2
  and strElem t1 t2 = t1 ^ " in " ^ t2
  and strNelem t1 t2 = t1 ^ " notin " ^ t2
  and strEmpty f = "empty(" ^ f ^ ")"
  and strPrefix0 f = "prefix(" ^ f ^ ")"
  and strRoot0 t us = "root(" ^ t ^ csl_mask false us ^ ")"
  and strInStateSpace t ss = "in_state_space(" ^ t ^ csl_mask false ss ^ ")"
  and strVariant t p e v = "variant(" ^ csl true [t;mask_ident p; mask_ident e; mask_ident v] ^ ")"
  and strTree v = "tree(" ^ mask_ident v ^ ")"
  and strType t v = "type(" ^ t ^ ", " ^ mask_ident v ^ ")"
  and strSometype t = "sometype(" ^ t ^ ")" in
  let rec convert_consttree (V (v, cts)) = 
    if cts = [] then mask_ident v else
    mask_ident v ^ "(" ^ csl_convert convert_consttree true cts ^ ")" in
  let rec term1ts t =
    let pterm1ts t = "(" ^ term1ts t ^ ")" in
    match t with
    | Var1 v -> mask_ident v
    | Succ1 (t, succs) -> strSucc (pterm1ts t) succs
    | Prefix1 t -> strPrefix (pterm1ts t)
    | Root1 v_opt -> (match v_opt with
      | Some v -> strRoot1 ^ " (" ^ v ^ ")" 
      | None -> strRoot1)
    | TreeRoot t -> strTreeRoot (term2ts t)
    | Succ (t, e, v, c) -> strTreeSucc (term1ts t) (mask_ident e)
	  (mask_ident v) (mask_ident c)
    | IntConst i -> strIntConst i
    | Plus (t, i) -> strPlus (term1ts t) i
    | Minus (t, i) -> strMinus (term1ts t) i
    | Max t -> strMax (term2ts t)
    | Min t -> strMin (term2ts t)
  and term2ts t =
    let pterm2ts s t = 
      let prec t = 
	match t with
	| Union _-> 0
	| Inter _ -> 1
	| Diff _ -> 2
	| Succ2 _ | Prefix2 _ -> 3
	| _ -> 4 
      in
      if prec t > prec s then term2ts t 
      else "(" ^ term2ts t ^ ")" 
    in
    match t with
    | Emptyset -> strEmptyset
    | Var2 v -> mask_ident v
    | Set ts -> strSet (List.map term1ts ts)
    | Union (t1, t2) -> strUnion (pterm2ts t t1) (pterm2ts t t2)
    | Inter (t1, t2) -> strInter (pterm2ts t t1) (pterm2ts t t2)
    | Diff (t1, t2) -> strDiff (pterm2ts t t1) (pterm2ts t t2)
    | Succ2 (t', succs) -> strSucc (pterm2ts t t') succs
    | Prefix2 t' -> strPrefix (pterm2ts t t')
    | ConstTree (t, v, ct) -> 
	strConstTree (term1ts t) v (convert_consttree ct) 
  in
  let rec ats a = 
    match a with
    | True -> strTrue
    | False -> strFalse
    | Eq1 (t1, t2) -> strEq (term1ts t1) (term1ts t2)
    | Neq1 (t1, t2) -> strNeq (term1ts t1) (term1ts t2)
    | Lt1 (t1, t2) -> strEq (term1ts t1) (term1ts t2)
    | Gt1 (t1, t2) -> strGt (term1ts t1) (term1ts t2)
    | Leq1 (t1, t2) -> strLeq (term1ts t1) (term1ts t2)
    | Geq1 (t1, t2) -> strGeq (term1ts t1) (term1ts t2)
    | Eq2 (t1, t2) -> strEq (term2ts t1) (term2ts t2)
    | Neq2 (t1, t2) -> strNeq (term2ts t1) (term2ts t2)
    | Sub (t1, t2) -> strSub (term2ts t1) (term2ts t2)
    | Elem (t1, t2) -> strElem (term1ts t1) (term2ts t2)
    | Nelem (t1, t2) -> strNelem (term1ts t1) (term2ts t2)
    | Empty t -> strEmpty (term2ts t)
    | Root0 (t, us) -> strRoot0 (term1ts t) us
    | InStateSpace (t, ss) -> strInStateSpace (term1ts t) ss
    | Variant (t, p, e, v) -> strVariant (term1ts t) p e v
    | Tree v -> strTree v
    | Type (t, v) -> strType (term1ts t) v
    | Sometype1 t -> strSometype (term1ts t)
    | Sometype2 t -> strSometype (term2ts t) 
  and fts f =
    let pfts g f =
      let prec f =
	match f with
	|	Quant _ | Let1 _ 
	| Let2 _ | Let0 _ -> 0
	|	Iff _ -> 1
	|	Impl _ -> 2
	|	Or _ -> 3
	|	And _ -> 4
	|	Not _ -> 5
	|	Atom _ | Pred _ 
	|	Restrict _ | Prefix0 _
	|	Export _ | Import _ -> 6
      in 
      if prec f > prec g then fts f
      else "(" ^ fts f ^ ")" in
    let strQuant q us vs f =  
      let str_q = match q with
      |	Exists0 -> strExists0
      |	Exists1 -> strExists1
      |	Exists2 -> strExists2
      | Forall0 -> strForall0
      |	Forall1 -> strForall1
      |	Forall2 -> strForall2 in
      let ulist = if us = [] then "" else "[" ^ csl_mask true us ^ "] " in
      str_q ^ ulist ^ csl_mask true vs ^ " : " ^ fts f
    and strLet l defs f =
      let def_list = csl_convert (fun (v,f) -> mask_ident v ^ " = " ^ (fts f)) true defs in
      l ^ def_list ^ " in " ^ (fts f) in 
    match f with
    | Atom a -> ats a
    | Not f' -> strNot (pfts f f')
    | And fs -> opsl_convert strAnd strTrue (pfts f) true fs
    | Or fs -> opsl_convert strOr strFalse (pfts f) true fs
    | Impl (f1, f2) -> strImpl (pfts f f1) (pfts f f2)
    | Iff (f1, f2) -> strIff (pfts f f1) (pfts f f2)
    | Restrict f -> strRestrict (fts f)
    | Prefix0 f -> strPrefix0 (fts f)
    | Pred (p, es) -> strPred p 
	  (List.map (function 
	    | Form f -> fts f
	    | Term1 t -> term1ts t
	    | Term2 t -> term2ts t) es)
    | Export (fname, f) -> strExport fname (fts f)
    | Import (fname, vs) -> strImport fname vs 
    | Quant (q, us, vs, f) -> strQuant q us vs f
    | Let0 (defs, f) -> strLet strLet0 defs f
    | Let1 (defs, f) -> strLet strLet1 defs f
    | Let2 (defs, f) -> strLet strLet2 defs f
  in fts f

let decl_to_string d = 
  let strGuide gs = 
    "guide " ^ csl_convert 
		 (fun (s1,s2,s3) -> mask_ident s1 ^ " -> (" ^ 
		   mask_ident s2 ^ ", " ^ mask_ident s3 ^")") 
		 true gs
  and strUniverse us = 
    let convert_univarg (uname, udef) =
      let udef_str =
	match udef with
	| Some (UnivSucc succs) -> ": " ^ succ_to_string succs  
	| Some (UnivTree v) -> ": " ^ mask_ident v
	| None -> "" in 
      uname ^ udef_str in 
    "universe " ^ csl_convert convert_univarg true us
  and strInclude fname = "include \"" ^ fname ^ "\"" 
  and strAssert f = "assert (" ^ f ^ ")"
  and strExecute f = "execute (" ^ f ^ ")"
  and strConst c i = Printf.sprintf "const %s = %d" (mask_ident c) i
  and strDefaultwhere1 p f = "defaultwhere1 " ^ "(" ^ f ^ ")"
  and strDefaultwhere2 p f = "defaultwhere2 " ^ "(" ^ f ^ ")"
  and strVarDecl0 vars = "var0 " ^ csl_mask true vars
  and strVarDecl1 = "var1 "
  and strVarDecl2 = "var2 "
  and strTreeDecl = "tree "
  and strVarDecl decl us vars = 
    let ulist = if us = [] then "" else "[" ^ csl_mask true us ^ "] " in
    decl ^ ulist ^ csl_convert (convert_varwhere form_to_string) true vars 
  and strMacro = "macro "
  and strPredDecl = "pred "
  and strDef d name paras f = 
    let convert_par p = match p with
    | VarPar0 vs -> "var0 " ^ csl_mask true vs 
    | VarPar1 vs -> "var1 " ^ csl_convert (convert_varwhere form_to_string) true vs
    | VarPar2 vs -> "var2 " ^ csl_convert (convert_varwhere form_to_string) true vs
    | UnivPar u -> "universe " ^ mask_ident u in
    let parlist = csl_convert convert_par true paras in
    d ^ mask_ident name ^ "(" ^ parlist ^ ") = " ^ f
  and strAllpos v = "allpos " ^ mask_ident v
  and strTypeDecl t tys = 
    let convert_ty (v, args) = 
      match args with
      |	[] -> mask_ident v 
      |	_ -> mask_ident v ^ "(" ^ 
	  csl_convert (fun (c, e) -> mask_ident c ^ ": " ^ mask_ident e) true args ^ ")" in
    let ty_decls = csl_convert convert_ty true tys in
    "type " ^ mask_ident t ^ " = " ^ ty_decls
  in match d with
  | FormDecl f -> form_to_string f 
  | Guide gs -> strGuide gs
  | Universe us -> strUniverse us
  | Include fname -> strInclude fname 
  | Assert f -> strAssert (form_to_string f)
  | Execute f -> strExecute (form_to_string f)
  | Const (c,i) -> strConst c i
  | Defaultwhere1 (v, f) -> strDefaultwhere1 v (form_to_string f)
  | Defaultwhere2 (v, f) -> strDefaultwhere2 v (form_to_string f)
  | VarDecl0 vars -> strVarDecl0 vars
  | VarDecl1 (us, vars) -> strVarDecl strVarDecl1 us vars
  | VarDecl2 (us, vars) -> strVarDecl strVarDecl2 us vars
  | TreeDecl (us, vars) -> strVarDecl strTreeDecl us vars
  | Macro (name, paras, f) -> strDef strMacro name paras (form_to_string f)
  | PredDecl (name, paras, f) -> strDef strPredDecl name paras (form_to_string f)
  | Allpos v -> strAllpos v
  | TypeDecl (t, tys) -> strTypeDecl t tys

(** Convert MONA program to string *)

let prog_to_string (h, decls) =
  let str_h = match h with
  | Ws1s -> "ws1s;\n"
  | Ws2s -> "ws2s;\n"
  | M2l_str -> "m2l-str;\n"
  | M2l_tree -> "m2l-tree;\n"
  in str_h ^ String.concat ";\n" (List.map (fun d -> wrap (decl_to_string d)) decls) ^ ";\n"

(** Print MONA formula *)

let print_form chan f =
  let print = output_string chan in
  let print_char = output_char chan in
  let printPrefix p t = print "^ "; p t 
  and printSucc p t succs = p t; print_char '.'; print (succ_to_string succs);
  and printIntConst i = print (Printf.sprintf "%d" i) in
  let printPlus p t i = p t; print " + "; printIntConst i
  and printMinus p t i = p t; print " + "; printIntConst i
  and printMax p t = print "max("; p t; print_char ')'
  and printMin p t = print "min("; p t; print_char ')'
  and printTreeSucc p t e v c =  print "succ("; p t; print_csl chan false [e;v;c]; print_char ')'
  and printTreeRoot p t = print "tree_root("; p t; print_char ')' 
  and printEmptyset () = print "empty"
  and printSet p ts = print_char '{'; print_csl_convert chan p true ts; print_char '}'
  and printUnion p t1 t2 = print_char '('; p t1; print " union "; p t2; print_char ')'
  and printInter p t1 t2 = print_char '('; p t1; print " inter "; p t2; print_char ')'
  and printDiff p t1 t2 = print_char '('; p t1; print_char '\\'; p t2; print_char ')'
  and printConstTree p t v ct = print "const_tree("; p t; print (", " ^ mask_ident v ^ ", " ^ ct ^ ")")
  and printNot p f = print "~ "; p f
  and strAnd = " & "
  and strOr = " | "
  and printRestrict p f = print "restrict("; p f; print_char ')'
  and printPred p pred es = match es with 
  | [] -> print (mask_ident pred) 
  | _ -> print (mask_ident pred); print_char '('; print_csl_convert chan p true es; print_char ')'
  and printExport fname p f = print "export(\""; print fname; print "\" "; p f; print_char ')'
  and printImport fname vs = 
    let print_vs = print_csl_convert chan (fun (v, var) -> print (mask_ident v); print " -> "; 
      print (mask_ident var)) false in
    print "import (\""; print fname; print "\""; print_vs vs; print_char ')'
  and strExists0 = "ex0 "
  and strForall0 = "all0 "
  and strExists1 = "ex1 "
  and strForall1 = "all1 "
  and strExists2 = "ex2 "
  and strForall2 = "all2 "
  and strLet0 = "let0 " 
  and strLet1 = "let1 " 
  and strLet2 = "let2 " 
  and strTrue = "true"
  and strFalse = "false"
  and printBinOp p op t1 t2 = p t1; print op; p t2
  and printElem p1 p2 t1 t2 = p1 t1; print " in "; p2 t2
  and printNelem p1 p2 t1 t2 = p1 t1; print " notin "; p2 t2
  and printEmpty p f = print "empty("; p f; print_char ')'
  and printPrefix0 p f = print "prefix("; p f; print_char ')'
  and printRoot0 p t us = print "root("; p t; print_csl_mask chan false us; print_char ')'
  and printInStateSpace p t ss = print "in_state_space("; p t; print_csl_mask chan false ss; print_char ')'
  and printVariant p t tr e v = print "variant(";  p t; print_csl chan false [mask_ident tr; mask_ident e; mask_ident v]; print_char ')'
  and printTree v = print "tree("; print (mask_ident v); print_char ')'
  and printType p t v = print "type("; p t; print ", "; print (mask_ident v); print_char ')'
  and printSometype p t = print "sometype("; p t; print_char ')' in
  let rec convert_consttree (V (v, cts)) = 
    if cts = [] then mask_ident v else
    mask_ident v ^ "(" ^ csl_convert convert_consttree true cts ^ ")" in
  let rec print_term1 t =
    let pprint_term1 t = print_char '('; print_term1 t;  print_char ')' in
    match t with
    | Var1 v -> print (mask_ident v)
    | Succ1 (t, succs) -> printSucc pprint_term1 t succs
    | Prefix1 t -> printPrefix pprint_term1 t
    | Root1 v_opt -> print "root"; (match v_opt with
      | Some v -> print (" (" ^ v ^ ")") 
      | None -> ())
    | TreeRoot t -> printTreeRoot print_term2 t
    | Succ (t, e, v, c) -> printTreeSucc print_term1 t (mask_ident e)
	  (mask_ident v) (mask_ident c)
    | IntConst i -> printIntConst i
    | Plus (t, i) -> printPlus print_term1 t i
    | Minus (t, i) -> printMinus print_term1 t i
    | Max t -> printMax print_term2 t
    | Min t -> printMin print_term2 t
  and print_term2 t =
    let pprint_term2 s t = 
      let prec t = 
	match t with
	| Union _-> 0
	| Inter _ -> 1
	| Diff _ -> 2
	| Succ2 _ | Prefix2 _ -> 3
	| _ -> 4 
      in
      if prec t > prec s then print_term2 t 
      else (print_char '('; print_term2 t; print_char ')') 
    in
    match t with
    | Emptyset -> printEmptyset ()
    | Var2 v -> print (mask_ident v)
    | Set ts -> printSet print_term1 ts
    | Union (t1, t2) -> printUnion (pprint_term2 t) t1 t2
    | Inter (t1, t2) -> printInter (pprint_term2 t) t1 t2
    | Diff (t1, t2) -> printDiff (pprint_term2 t) t1 t2
    | Succ2 (t', succs) -> printSucc (pprint_term2 t) t' succs
    | Prefix2 t' -> printPrefix (pprint_term2 t) t'
    | ConstTree (t, v, ct) -> 
	printConstTree print_term1 t v (convert_consttree ct) 
  in
  let rec print_atom a = 
    match a with
    | True -> print strTrue
    | False -> print strFalse
    | Eq1 (t1, t2) -> printBinOp print_term1 " = " t1 t2
    | Neq1 (t1, t2) -> printBinOp print_term1 " ~= " t1 t2
    | Lt1 (t1, t2) -> printBinOp print_term1 " < " t1 t2
    | Gt1 (t1, t2) -> printBinOp print_term1 " > " t1 t2
    | Leq1 (t1, t2) -> printBinOp print_term1 " <= " t1 t2
    | Geq1 (t1, t2) -> printBinOp print_term1 " >= " t1 t2
    | Eq2 (t1, t2) -> printBinOp print_term2 " = " t1 t2
    | Neq2 (t1, t2) -> printBinOp print_term2 " ~= " t1 t2
    | Sub (t1, t2) -> printBinOp print_term2 " sub " t1 t2
    | Elem (t1, t2) -> printElem print_term1 print_term2 t1 t2
    | Nelem (t1, t2) -> printNelem print_term1 print_term2 t1 t2
    | Empty t -> printEmpty print_term2 t
    | Root0 (t, us) -> printRoot0 print_term1 t us
    | InStateSpace (t, ss) -> printInStateSpace print_term1 t ss
    | Variant (t, p, e, v) -> printVariant print_term1 t p e v
    | Tree v -> printTree v
    | Type (t, v) -> printType print_term1 t v
    | Sometype1 t -> printSometype print_term1 t
    | Sometype2 t -> printSometype print_term2 t 
  and print_form f =
    let pprint_form g f =
      let prec f =
	match f with
	| Quant _ | Let1 _ 
	| Let2 _ | Let0 _ -> 0
	| Iff _ -> 1
	| Impl _ -> 2
	| Or _ -> 3
	| And _ -> 4
	| Not _ -> 5
	| Atom _ | Pred _ 
	| Restrict _ | Prefix0 _
	| Export _ | Import _ -> 6
      in 
      if prec f > prec g then print_form f
      else (print_char '('; print_form f; print_char ')') in
    let printQuant q us vs f =  
      let str_q = match q with
      |	Exists0 -> strExists0
      |	Exists1 -> strExists1
      |	Exists2 -> strExists2
      | Forall0 -> strForall0
      |	Forall1 -> strForall1
      |	Forall2 -> strForall2 in
      match vs with
      |	[] -> print_form f
      |	_ ->
	  let print_us us = if us = [] then () else (print_char '[';  print_csl_mask chan true us; print "] ") in
	  print str_q; print_us us; print_csl_mask chan true vs; print " : "; print_form f
    and printLet l defs f =
      let print_defs defs = print_csl_convert chan 
	  (fun (v, f) -> print (mask_ident v); print " = "; print_form f) true defs in
      print l; print_defs defs; print " in "; print_form f in 
    match f with
    | Atom a -> print_atom a
    | Not f' -> printNot (pprint_form f) f'
    | And fs -> print_opsl_convert chan strAnd strTrue (pprint_form f) true fs
    | Or fs -> print_opsl_convert chan strOr strFalse (pprint_form f) true fs
    | Impl (f1, f2) -> printBinOp (pprint_form f) " => " f1 f2 
    | Iff (f1, f2) -> printBinOp (pprint_form f) " <=> " f1 f2
    | Restrict f -> printRestrict print_form f
    | Prefix0 f -> printPrefix0 print_form f
    | Pred (p, es) -> printPred 
	  (function 
	    | Form f -> print_form f
	    | Term1 t -> print_term1 t
	    | Term2 t -> print_term2 t) p es
    | Export (fname, f) -> printExport fname print_form f
    | Import (fname, vs) -> printImport fname vs 
    | Quant (q, us, vs, f) -> printQuant q us vs f
    | Let0 (defs, f) -> printLet strLet0 defs f
    | Let1 (defs, f) -> printLet strLet1 defs f
    | Let2 (defs, f) -> printLet strLet2 defs f
  in print_form f

let print_decl chan d = 
  let print = output_string chan 
  and print_char = output_char chan in
  let printGuide gs = 
    print "guide "; print_csl_convert chan
      (fun (s1,s2,s3) -> print (mask_ident s1); print " -> ("; 
	print (mask_ident s2); print ", "; print (mask_ident s3); print_char ')') 
      true gs
  and printUniverse us = 
    let convert_univarg (uname, udef) =
      let print_udef str =
	match udef with
	| Some (UnivSucc succs) -> print ": "; print (succ_to_string succs)  
	| Some (UnivTree v) -> print ": "; print (mask_ident v)
	| None -> () in 
      print uname; print_udef udef in 
    print "universe "; print_csl_convert chan convert_univarg true us
  and printInclude fname = print "include \""; print fname; print_char '\"' 
  and printAssert f = print "assert ("; print_form chan f; print_char ')'
  and printExecute f = print "execute ("; print_form chan f; print_char ')'
  and printConst c i = Printf.fprintf chan "const %s = %d" (mask_ident c) i
  and printDefaultwhere1 p f = print "defaultwhere1 ("; print_form chan f; print_char ')'
  and printDefaultwhere2 p f = print "defaultwhere2 ("; print_form chan f; print_char ')'
  and printVarDecl0 vars = print "var0 "; print_csl_mask chan true vars
  and strVarDecl1 = "var1 "
  and strVarDecl2 = "var2 "
  and strTreeDecl = "tree "
  and printVarDecl decl us vars = 
    let print_us us = if us = [] then () else (print_char '['; print_csl_mask chan true us; print "] ") in
    print decl; print_us us; print_csl_convert chan (print_varwhere chan print_form) true vars 
  and strMacro = "macro "
  and strPredDecl = "pred "
  and printDef d name paras f = 
    let print_par p = match p with
    | VarPar0 vs -> print "var0 "; print_csl_mask chan true vs 
    | VarPar1 vs -> print "var1 "; print_csl_convert chan (print_varwhere chan print_form) true vs
    | VarPar2 vs -> print "var2 "; print_csl_convert chan (print_varwhere chan print_form) true vs
    | UnivPar u -> print "universe "; print (mask_ident u) in
    let print_paras paras = print_csl_convert chan print_par true paras in
    print d; print (mask_ident name); print_char '('; print_paras paras; print ") = "; print_form chan f
  and printAllpos v = print "allpos "; print (mask_ident v)
  and printTypeDecl t tys = 
    let print_ty (v, args) = 
      match args with
      |	[] -> print (mask_ident v) 
      |	_ -> print (mask_ident v); print_char '('; 
	  print_csl_convert chan (fun (c, e) -> print (mask_ident c); print ": "; print (mask_ident e)) true args; print_char ')' in
    let print_tys tys = print_csl_convert chan print_ty true tys in
    print "type "; print (mask_ident t); print " = "; print_tys tys
  in match d with
  | FormDecl f -> print_form chan f 
  | Guide gs -> printGuide gs
  | Universe us -> printUniverse us
  | Include fname -> printInclude fname 
  | Assert f -> printAssert f
  | Execute f -> printExecute f
  | Const (c,i) -> printConst c i
  | Defaultwhere1 (v, f) -> printDefaultwhere1 v f
  | Defaultwhere2 (v, f) -> printDefaultwhere2 v f
  | VarDecl0 vars -> printVarDecl0 vars
  | VarDecl1 (us, vars) -> printVarDecl strVarDecl1 us vars
  | VarDecl2 (us, vars) -> printVarDecl strVarDecl2 us vars
  | TreeDecl (us, vars) -> printVarDecl strTreeDecl us vars
  | Macro (name, paras, f) -> printDef strMacro name paras f
  | PredDecl (name, paras, f) -> printDef strPredDecl name paras f
  | Allpos v -> printAllpos v
  | TypeDecl (t, tys) -> printTypeDecl t tys

(** Print MONA program *)
	
let print_prog chan (h, decls) =
  (match h with
  | Ws1s -> output_string chan "ws1s;\n"
  | Ws2s -> output_string chan "ws2s;\n"
  | M2l_str -> output_string chan "m2l-str;\n"
  | M2l_tree -> output_string chan "m2l-tree;\n");
  print_opsl_convert chan ";\n" "" (fun d -> print_decl chan d) true decls;
  output_string chan ";\n"
