(** Transform Java to Jast:
     - expressions to three-address form
     - resolving variables and fields.

Because we are resolving identifiers, traverse first all variable declarations
and method headers, and only then process method bodies.

Partially translated program acts as an environment.

*)

open Syntax
open JastUtil
open Common

let mkvdi id t init = { 
  Jast.vd_name = id_string id; 
  Jast.vd_type = t;
  Jast.vd_init = init;
  Jast.vd_readonly = false}
  
let mkvdir id t init r = { 
  Jast.vd_name = id_string id; 
  Jast.vd_type = t;
  Jast.vd_init = init;
  Jast.vd_readonly = r}

let mkvd id t = { 
  Jast.vd_name = id_string id; 
  Jast.vd_type = t;
  Jast.vd_init = None;
  Jast.vd_readonly = false}

let mkvd0 n t = { 
  Jast.vd_name = n; 
  Jast.vd_type = t; 
  Jast.vd_init=None;
  Jast.vd_readonly = false}
  
let c_formal (v : var) : Jast.var_decl = mkvd v.v_name v.v_type
let c_field (fd : field) : Jast.var_decl = 
  mkvd fd.f_var.v_name fd.f_var.v_type

let name2str (n:name) : string = pr_name n

let init_expr_to_str 
    (msg : string) 
    (initial : init option) : string option =
  match initial with
    | None -> None
    | Some e -> 
	(match e with
	   | ArrayInit _ -> Util.fail msg	
	   | ExprInit ex -> 
	       (match ex with
		  | Literal s -> Some s
		  | _ -> Util.fail msg))

let parse_contract (method_name : string) (oa : annotation option) : 
    (Form.form option * Jast.mod_item list option * Form.form option) =
  match oa with
  | None -> (None, None, None)
  | Some a -> 
      let emsg = "Contract for method " ^ method_name ^ "." in
      ParseSpec.parse_contract emsg a

(* ------------------------------------------------------------ *)
(*                    Translating method bodies                 *)
(* ------------------------------------------------------------ *)

type computation = Jast.simpval * Jast.stmt list

let dummy_simpval = Jast.LiteralVal (Jast.StringLiteral "dummyString")
let dummy_computation = (dummy_simpval,[])

(** Parse literal from string. *)
let parse_literal (s : string) : Jast.literal =
  let len = String.length s in
  let rec get_digits (i : int) (x : int) : Jast.literal =
    if i >= len then Jast.IntLiteral x
    else 
      let ch = s.[i] in
      if ('0' <= ch && ch <= '9') then
        let d = int_of_char ch - int_of_char '0' in
        get_digits (i+1) (10 * x + d)
      else Jast.OtherLiteral s
  in
  if s="" then Util.fail "Javajast.parse_literal: empty literal"
  else if s = "true" then Jast.BoolLiteral true
  else if s = "false" then Jast.BoolLiteral false
  else if s = "null" then Jast.NullLiteral
  else if s.[0]='"' then Jast.StringLiteral (String.sub s 1 (len - 2))
  else get_digits 0 0


let parse_literal_opt (os : string option) : Jast.literal option = 
  match os with
    | None -> None
    | Some s -> Some (parse_literal s)

let rec mk_array_type k t =
  if k=0 then t else mk_array_type (k-1) (Syntax.ArrayType t)
let get_named_type (t : typ) : string = 
  match t with
    | TypeName [n] -> id_string n
    | TypeName _ ->
	Util.fail ("Unexpected complex named type " ^ print_typ t ^ ", simple named type expected.")
    | ArrayType _ -> 
	Util.fail ("Unexpected array type " ^ print_typ t ^ ", simple named type expected.")

let c_proc_body 
    (env : Jast.program)
    (c : Jast.class_decl)
    (m : Jast.method_decl)
    (st0 : stmt) : 
    (Jast.var_def list *
     Jast.avar_decl list * 
     Jast.var_decl list *
     Jast.stmt) = 
  let mn = m.Jast.m_name in
  let clname = c.Jast.cl_name in

  let (vardefs : Jast.var_def list ref) = ref [] in
  let add_local_defs (defs : Jast.var_def list) =
    vardefs := defs @ !vardefs in

  let (speclocals : Jast.avar_decl list ref) = ref [] in
  let add_local_avd (avd : Jast.avar_decl) =
    speclocals := avd::!speclocals in

  let (locals : Jast.var_decl list ref) = ref [] in
  let add_local (vd : Jast.var_decl) =
    if not (Jtype.is_void vd.Jast.vd_type) then
      locals := vd::!locals
    else () in

  let (id_counter : int ref) = ref 0 in
  let get_new_id (t : typ) : ident = 
    (id_counter := !id_counter + 1;
     let id = synth_id ("tmp_" ^ (Printf.sprintf "%d" !id_counter)) in
       add_local (mkvd id t); id) in
  let get_new_lval (t : typ) : Jast.lval = Jast.LocalVar
    (mkvd (get_new_id t) t) in

  let err msg = Util.fail ("Error in method " ^ clname ^ "." ^ mn ^ ": " ^ msg) in
  let rerr v msg = 
    (Util.warn (" in method " ^ clname ^ "." ^ mn ^ ": " ^ msg); v) in

  let rec c_name (n : string list) : computation =  (* n is reversed *)
    let recur f n1 = (* similar to translation of Dot *)
      let (res_e,st_e) = c_name n1 in
      let cl_e = get_simpval_class env res_e in
      let fd = must_get_field env cl_e f in
      let t = field_result_type fd in
      let lv = get_new_lval t in
	(Jast.VarVal lv,
	 st_e @ [load_stmt_n env lv res_e f])
    in match n with
      | [] -> err "Empty name!"
      | [x] when x="this" -> (Jast.this_val clname,[])
      | [x] -> 
	  (match find_var !locals x with
	     | Some vd -> (Jast.VarVal(Jast.LocalVar vd),[])
	     | None ->
		 (match find_var m.Jast.m_formals x with
		    | Some vd -> (Jast.ParamVar vd,[])
		    | None ->
			(match find_field c x with
			   | Some fd ->
			       let t = field_result_type fd in
			       let lv = get_new_lval t in
				 (Jast.VarVal lv, [load_stmt 
					 lv
					 (Jast.this_val clname)
					 fd])
			   | None -> (match find_static_var c x with
					| Some vd -> 
					    let cv = {Jast.cv_cl = c.Jast.cl_name;
						      Jast.cv_var = vd} in
					    let v = Jast.StaticVar cv in
					      (Jast.VarVal v, [])
					| None -> err ("Unknown non-dotted variable or classname " ^ x)))))
      | [f;x] -> 
	  (match (get_class env x) with	       
	     | None -> recur f [x]
	     | Some c_x ->
		 (match find_static_var c_x f with
		    | None -> err ("Could not find static variable " ^ f ^
				     " in class " ^ x)
		    | Some vd ->
			(Jast.VarVal(Jast.StaticVar {Jast.cv_cl = x;
						     Jast.cv_var = vd}),
			 [])))
      | f::n1 -> recur f n1

  and c_short_circuit_or (e1 : expr) (e2 : expr) : computation =
    let (res1,st1) = c_exp e1 in
    let (res2,st2) = c_exp e2 in
    let res3 = get_new_id Jtype.boolean_type in
      (*
	The next translation avoids assignments and uses
	assumes instead:

	st1;
	if (res1) assume res3;
	else {
          st2;
	  assume (res3 = res2);
        }
      *)
    let res3l = Jast.LocalVar (mkvd res3 Jtype.boolean_type) in
    let res3f = FormUtil.mk_var (Syntax.id_string res3) in
    let res2f = Jast2ast.c_simpval res2 in
      (Jast.VarVal res3l,
       st1 @
	 [Jast.If(res1,
		  mk_assume res3f,
		  Jast.Block 
		    (st2 @ [mk_assume (FormUtil.mk_eq(res3f, res2f))]))])
	
  and c_short_circuit_and (e1 : expr) (e2 : expr) : computation =
    let (res1,st1) = c_exp e1 in
    let (res2,st2) = c_exp e2 in
    let res3 = get_new_id Jtype.boolean_type in
      (*
	st1;
	if (res1) {
          st2;
	  assume (res3 = res2);
	}
	else assume (~res3)
      *)
    let res3l = Jast.LocalVar (mkvd res3 Jtype.boolean_type) in
    let res3f = FormUtil.mk_var (Syntax.id_string res3) in
    let res2f = Jast2ast.c_simpval res2 in
      (Jast.VarVal res3l,
       st1 @
	 [Jast.If(res1,
		  Jast.Block 
		    (st2 @ [mk_assume (FormUtil.mk_eq(res3f, res2f))]),
		  mk_assume (FormUtil.mk_not res3f))])

  and c_exp (e : expr) : computation = 
    match e with
    | Literal s -> (Jast.LiteralVal (parse_literal s), [])
    | NewClass(t,args,None, None) -> (* x = new Toto(blabla) *)
    	c_constructor_call c t args None
    | NewClass(t,args,None, Some a) -> (* x = new /*: hidden */ Toto(blabla) *)
    	c_constructor_call c t args (Some a)
    | NewArray(t,dims,_,None, annot) ->
	let dims_c = List.map c_exp dims in
	let dims_res = List.map fst dims_c in
	let dims_st = List.map snd dims_c in
	let dim_no = List.length dims in
	let array_type = mk_array_type dim_no t in
	let tname = get_named_type t in
	let lv = get_new_lval array_type in
	let lv_name : Jast.var_name = match lv with 
	  | Jast.LocalVar {Jast.vd_name=x} -> x 
	  | _ -> assert false 
	in
	let opt_stmt = match annot with
	  | None -> []
	  | Some a -> match ParseSpec.parse_modifier "in ''new'' statement" a with
	      | Specs.Hidden -> [JastUtil.mk_add_hidden lv_name]
	      | _ -> Util.warn ("modifier " ^ a ^ " not allowed in new statement"); []
	in
	  (Jast.VarVal lv,
	   List.concat dims_st @ 
	     [mk_newarray lv tname dims_res] @ opt_stmt)

    | Dot(e,fn) ->
	let (res_e,st_e) = c_exp e in
	let cl_e = get_simpval_class env res_e in
	let fd = must_get_field env cl_e (id_string fn) in
	let t = field_result_type fd in
	let lv = get_new_lval t in
	  (Jast.VarVal lv,
	   st_e @ [load_stmt_n env lv res_e (id_string fn)])
    | Call(expr,args) -> c_call expr args
    | ArrayAccess(a,i) ->
	let (res_a,st_a) = c_exp a in
	let (res_i,st_i) = c_exp i in
	let t = (match get_simpval_typ res_a with
		   | TypeName n -> 
		       err ("Expected an array type and not " ^ name2str n)
		   | ArrayType t -> t) in	  
	let lv = get_new_lval t in
	  (Jast.VarVal lv,
	   st_a @ st_i @ [array_load lv res_a res_i])
    | Postfix(e,op) ->
	if op="++" or op=="--" then 
	  Util.fail "++ and -- operators not supported, please use assignment instead"
	else
	  (let (res,st) = c_exp e in
	   let t = get_simpval_typ res in
	   let lv = get_new_lval (Jtype.type_postfix t op) in
	     (Jast.VarVal lv,
	      st @ [mk_postfix lv res op]))
    | Prefix(op,e) ->
	if op="++" or op=="--" then 
	  Util.fail "++ and -- operators not supported, please use assignment instead"
	else
	  (let (res,st) = c_exp e in
	   let t = get_simpval_typ res in
	   let lv = get_new_lval (Jtype.type_prefix op t) in
	     (Jast.VarVal lv,
	      st @ [mk_prefix lv op res]))
    | Cast(t,e) ->
	let (res,st) = c_exp e in
	let lv = get_new_lval t in
	  (Jast.VarVal lv,
	   st @ [mk_cast lv t res])
    | Infix(e1,"&&",e2) -> c_short_circuit_and e1 e2
    | Infix(e1,"||",e2) -> c_short_circuit_or e1 e2
    | Infix(e1,op,e2) ->
	let (res1,st1) = c_exp e1 in
	let (res2,st2) = c_exp e2 in
	let t1 = get_simpval_typ res1 in
	let t2 = get_simpval_typ res1 in
	let t = Jtype.type_infix t1 op t2 in
	let lv = get_new_lval t in
	  (Jast.VarVal lv,
	   st1 @ st2 @ [mk_infix lv res1 op res2])
    | InstanceOf(e,t) ->
	let (res,st) = c_exp e in
	let lv = get_new_lval Jtype.boolean_type in
	  (Jast.VarVal lv,
	   st @ [mk_instanceOf lv res t])
    | Conditional(ec,e1,e2) ->
	let (resc,ecst) = c_exp ec in
	let (res1,est1) = c_exp e1 in
	let (res2,est2) = c_exp e2 in
	let t1 = get_simpval_typ res1 in
	let res = get_new_lval t1 in
	  (Jast.VarVal res,
	   (ecst @ [Jast.If(resc,
                            Jast.Block (est1 @ 
					  [slval_asgn res res1]),
                            Jast.Block (est2 @
					  [slval_asgn res res2]))]))
    | Assignment(_,_,_) ->	
	err "Found assignment that is not a standalone statement. Jahob does not like that."
    | Name n -> c_name (List.rev (List.map id_string n))
    | st -> let lv = get_new_lval no_type in 
	rerr (Jast.VarVal lv,[]) ("Unrecognized expression")

  and c_init (i : init) : computation = match i with
    | ExprInit e -> c_exp e
    | ArrayInit _ -> err "array initializers for variables not supported"

  and c_assign (lhs : expr) (rhs : expr) : Jast.stmt list =
    let (res_rhs,st_rhs) = c_exp rhs in
    match lhs with
    | Dot(e,f) -> 
        let (res_e,st_e) = c_exp e in         
          st_e @ st_rhs @ 
	    [field_asgn_n env res_e (id_string f) res_rhs]
    | ArrayAccess(a,i) ->
        (let (res_a,st_a) = c_exp a in
         let (res_i,st_i) = c_exp i in
           st_a @ st_i @ st_rhs @ [array_asgn res_a res_i res_rhs])
    | Name [n] -> 
	let n_s = id_string n in
	  st_rhs @ [some_asgn c !locals n_s res_rhs]
    | Name [x;f] ->
	let x_s = id_string x and f_s = id_string f in
	  (match qasgn env c m !locals x_s f_s res_rhs with
	    | Some st -> st_rhs @ [st]
	    | None -> (* this.x.f = y *)
		c_assign (Dot(Name [x],f)) rhs)
(*
		let x_fd = get_field env c x_s in
		let t = field_result_type x_fd in
		let lv = get_new_lval t in
		let load = load_stmt lv Jast.this_val x_fd in
		let f_fd = get_field c f_s in
		let store = 
		  field_asgn (VarVal lv) f_fd res_rhs in
		  st_rhs @ [load;store])
*)
    | Name ns ->
        let (ns1,f) = Util.firsts_last ns in
        c_assign (Dot(Name ns1,f)) rhs
    | _ -> (Printf.printf "Unexpected left-hand side, an l-value expected but got ";
	    Pretty.print_expr Format.std_formatter lhs;
	    Format.print_newline();
            Printf.printf "%s" ("(in method " ^ mn ^ ")\n");
	    Util.fail "unexpected left-hand side")

  and c_constructor_call
      (cl : Jast.class_decl)
      (t : typ)
      (args : expr list) 
      (a : annotation option)
      : computation = 
    let constructor_name = 
      match t with 
  	| TypeName n ->
	    (match n with
  	      | [x] ->
  		  id_string x
  	      | _ ->
  		  err( "Multiple identities for constructor" ))
  	| _ ->
  	    err( "Multiple types for constructor" ) in
    let args_c = List.map c_exp args in
    let args_res = List.map fst args_c in
    let args_sts = List.map snd args_c in
    let lv : Jast.lval = get_new_lval t in
    let lv_name : Jast.var_name = match lv with 
      | Jast.LocalVar {Jast.vd_name=x} -> x 
      | _ -> assert false 
    in
    let opt_stmt = match a with
      | None -> []
      | Some a -> match ParseSpec.parse_modifier "in ''new'' statement" a with
	  | Specs.Hidden -> [JastUtil.mk_add_hidden lv_name]
	  | _ -> Util.warn ("modifier " ^ a ^ " not allowed in new statement"); []
    in
    let is_default = 
      (args_c=[]) && 
	not (has_defined_constructor constructor_name env) in
    let res = Some lv in
      (Jast.VarVal lv, 
       List.concat args_sts 
       @ [mk_constructor_call res constructor_name args_res is_default]
       @ opt_stmt
      )
	    
  and c_static_call
      (cl : Jast.class_decl)
      (callee : string)
      (args : expr list) : computation = 
    let args_c = List.map c_exp args in
    let args_res = List.map fst args_c in
    let args_sts = List.map snd args_c in
    let t = method_result_type env cl callee in
    let lv = get_new_lval t in
    let res = if Jtype.is_void t then None else Some lv in
      (Jast.VarVal lv,
       List.concat args_sts @ 
	 [mk_stat_proc_call res
	    cl.Jast.cl_name callee args_res])

  and c_dynamic_call 
      (receiver : expr)
      (callee : string)
      (args : expr list) : computation =
    let (rec_res,rec_st) = c_exp receiver in
    let args_c = List.map c_exp args in
    let args_res = List.map fst args_c in
    let args_sts = List.map snd args_c in
    let cn = get_simpval_typ_name rec_res in
      match get_class env cn with
	| Some cl ->
	    let t = method_result_type env cl callee in
	    let lv = get_new_lval t in
	    let res = if Jtype.is_void t then None else Some lv in
	      (Jast.VarVal lv,
	       rec_st @ List.concat args_sts @ 
		 [mk_dyn_proc_call res rec_res callee args_res])
	| None -> 
	    (match get_interface env cn with
	       | Some ifc ->
		   let t = imethod_result_type ifc callee in
		   let lv = get_new_lval t in
		   let res = if Jtype.is_void t then None else Some lv in
		     (Jast.VarVal lv,
		      rec_st @ List.concat args_sts @ 
			[mk_dyn_proc_call res rec_res callee args_res])
	       | None -> Util.fail ("Could not find class or interface " ^
				     cn))

  and c_call 
      (mth : expr)
      (args : expr list) : computation = match mth with
      | Name n -> 
	  (match n with
	     | [] -> err "empty name of method?!"
	     | [cmn] ->
		 (* call to this class or object *)
		 let cmn_s = id_string cmn in
		   if is_static_call c (id_string cmn)
		   then c_static_call c cmn_s args
		   else c_dynamic_call (Name [this_ident]) cmn_s args
	     | [cc;cmn] -> (* static or dynamic call *)
		 (let cmn_s = id_string cmn in
		  let cc_s = id_string cc in
		    (match get_class env cc_s with
		       | None -> c_dynamic_call (Name [cc]) cmn_s args
		       | Some cl -> 
			   if is_static_call cl cmn_s then
			     c_static_call cl cmn_s args
			   else c_dynamic_call (Name [cc]) cmn_s args))
	     | _ -> rerr dummy_computation 
		 ("Method call " ^ name2str n ^ 
		    " has at least three components."))
      | Dot(receiver,cmn_s) -> 
	  c_dynamic_call receiver (id_string cmn_s) args
      | _ -> err ("method description is not of expected form")

  and c_annot_stmt (msg : string) (spc : Specs.spec) : Jast.stmt list =
    match spc with
      | Specs.Assert f -> [JastUtil.mk_assert f]
      | Specs.NoteThat f -> [JastUtil.mk_noteThat f]
      | Specs.Assume f -> [JastUtil.mk_assume f]
      | Specs.Split f -> [JastUtil.mk_split f]
      | Specs.Havoc fs -> [JastUtil.mk_havoc fs]
      | Specs.Assign {Specs.aa_lhs=lhs; Specs.aa_rhs=rhs} -> 
	  [JastUtil.mk_aassign lhs rhs]

      | Specs.SpecVar avd -> 
	     (add_local_avd avd;
	      match avd.Specs.avd_init with
		| None -> []
		| Some f ->
		    [JastUtil.mk_aassign (Form.Var avd.Specs.avd_name) f])

      | Specs.Vardefs vds -> add_local_defs vds; []
      | Specs.Operation ao -> [JastUtil.mk_aoperation ao]
      | _ ->
	  (Util.warn ("Unexpected annotation " ^ msg);
	   [])
  and c_st (st : stmt) : Jast.stmt list = 
    let emsg = "(statement in method " ^ clname ^ "." ^ mn ^ ")" in
  match st with
  | Block sts -> List.concat (List.map c_st sts)
  | LocalVar fd ->
      (let vd = c_field fd in
      add_local vd;
      match fd.f_init with
      | None -> []
      | Some i ->
	  let (res,sts) = c_init i in
	  sts @ [slocal_asgn vd res])
  | Empty -> []
  | Label (id,s) -> c_st s
  | Expr e -> (match e with
    | Call(mth,args) -> snd (c_call mth args)
    | Assignment(lhs,op,rhs) ->
        if op="=" then c_assign lhs rhs	
        else Util.fail ("Assignment operator '" ^ op ^ "' found.\n" ^
                      "Only '=' is accepted as an assignment operator.\n" ^
                       "(in method " ^ mn ^ ")")
    | _ -> Util.warn ("ignored unexpected expression as statement" ^ emsg); [])
  | If(e,s1,os2) -> (match os2 with
    | None -> c_st (If(e,s1, Some Empty))
    | Some s2 ->
        let (res,est) = c_exp e in
        let s1t = c_st s1 in
        let s2t = c_st s2 in
        est @ [Jast.If(res,Jast.Block s1t,Jast.Block s2t)])
  | While(ao, e, s) -> 
      (* FIX: add support while true, break in middle *)
      (let (res,est) = c_exp e in
       let emsg = "Expected a loop invariant" in
       let oinv = match ao with
	 | None -> None 
	 | Some a -> Some (ParseSpec.parse_inv emsg a).Specs.inv_form in
      [Jast.Loop(oinv, Jast.Block est,res,Jast.Block (c_st s))])
  | Break _ -> Util.fail ("This use of break statement not supported " ^
			 emsg)
  | Return oe ->
      (match oe with 
      | None -> [Jast.Return None]
      | Some e -> 
          let (res,et) = c_exp e in
          et @ [Jast.Return (Some res)])
  | AnnotationStmt a ->
      List.concat (List.map (c_annot_stmt (a ^ emsg)) (ParseSpec.parse_specs a))
  | _ -> (Util.warn ("Unexpected statement" ^ emsg);
	 [])
  in 
  let st = c_st st0 in
  (!vardefs, !speclocals, !locals, Jast.Block st)

let find_method (mn : string) (cl : class_decl) =
  let rec search (ds : decl list) = match ds with
  | [] -> Util.fail ("not found in find_method(" ^ mn ^ ")")
  | d::ds0 -> (match d with
    | Method ({m_var={v_name=idnt}} as m) when id_string idnt=mn -> m
    | Constructor ({m_var={v_name=idnt}} as m) when id_string idnt=mn -> m
    | _ -> search ds0)
  in search cl.cl_body

let method_with_body 
    (env : Jast.program)
    (c : Jast.class_decl)
    (cl : class_decl)
    (task : analysis_task)
    (m : Jast.method_decl) 
    : Jast.method_decl =
  let cname = c.Jast.cl_name in
  let mname = m.Jast.m_name in
    if method_is_relevant (cname,mname) task then      
      let (ml : method_decl) = find_method mname cl in
      let _ = Debug.msg ("Java->Jast: method " ^ 
			   cname ^ "." ^ mname ^ "\n") in
      let (vardefs,speclocals,locals,body) = c_proc_body env c m ml.m_body in
	{ m with 
	    Jast.m_locals = locals; 
	    Jast.m_speclocals = speclocals;
	    Jast.m_vardefs = vardefs;
	    Jast.m_body = body }
    else m

let find_class (cn : string) (cus0 : compilation_unit list) : class_decl =
  let rec search (ds : decl list) (cus : compilation_unit list) = match ds with
  | [] -> (match cus with
    | [] -> Util.fail ("find_class failed to find class " ^ cn)
    | cu::cus1 -> search cu.decls cus1)
  | d::ds0 -> (match d with
    | Class ({cl_name=cln} as c) when id_string cln=cn -> c
    | _ -> search ds0 cus)
  in search [] cus0

let class_with_bodies
    (env : Jast.program)
    (cus : compilation_unit list)
    (task : analysis_task)
    (c:Jast.class_decl) : Jast.class_decl =
  let (cl : class_decl) = find_class c.Jast.cl_name cus in
    { c with Jast.cl_methods = 
	  List.map (method_with_body env c cl task) c.Jast.cl_methods }

let compilation_unit_bodies 
    (env0 : Jast.program)
    (cus : compilation_unit list)
    (task : analysis_task) : Jast.program = 
  let env = { env0 with 
		 Jast.classes = Jast.standard_classes @ env0.Jast.classes } in
  (* env contains declarations, now convert method bodies *)
  { env with Jast.classes = 
    Jast.standard_classes @ 
      List.map (class_with_bodies env cus task) env0.Jast.classes }


(* ------------------------------------------------------------ *)
(*                    Translating fields and signatures         *)
(* ------------------------------------------------------------ *)

type decl_modifiers = {
  mod_readonly : bool;
  mod_public : bool;
  mod_private : bool;
  mod_ownerOpt : Jast.class_name option;
  mod_static : bool;
}

let parse_var_modifiers (clvar : string) (mods : modifier list) = 
  let rec collect (ms:modifier list) res = match ms with
    | [] -> 
	let res1 = res in
	let res = (if (not res.mod_public && not res.mod_private) then
		     (
		       Debug.msg ("Variable declared neither public nor private (variable " ^ clvar ^ "), assuming public.\n");
		      {res1 with mod_public = true})
		   else res1) in
	let r = (res.mod_readonly,res.mod_ownerOpt,res.mod_private,res.mod_static) in
	  if (res.mod_public && res.mod_private) then
	    Util.fail ("Variable declared both public and private (variable " ^ clvar ^ ")")
	  else if res.mod_ownerOpt <> None then
	    if res.mod_static then
	      Util.fail ("Static variable cannot be owned (variable " ^ clvar ^ ")")
	    else if res.mod_readonly then 
	      Util.fail ("Readonly variable cannot be owned (variable " ^ clvar ^ ")")
	    else if (res.mod_private || not res.mod_public) then
	      Util.fail ("Owned variable must be public (variable " ^ clvar ^ ")")
	    else r
	  else if res.mod_readonly then
	    if res.mod_private then
	      Util.fail ("Readonly variable must be public (variable " ^ clvar ^ ")")
	    else r
	  else r
    | m::ms1 -> 
	(match m with
	   | AnnotationModifier s ->
	       (match ParseSpec.parse_modifier "" s with
		  | Specs.Readonly -> collect ms1 {res with mod_readonly=true}
		  | Specs.ClaimedBy s -> 
		      (match res.mod_ownerOpt with
			 | None -> collect ms1 {res with mod_ownerOpt=Some s}
			 | Some _ -> Util.fail ("Cannot have multiple claimedby modifiers (variable " ^ clvar ^ ")")))
	   | Public -> collect ms1 {res with mod_public=true}
	   | Protected -> Util.fail ("Unsupported modifier 'protected' (variable " ^ clvar ^ ")")
	   | Private -> collect ms1 {res with mod_private=true}
	   | Abstract -> Util.fail ("Unsupported modifier 'abstract' (variable " ^ clvar ^ ")")
	   | Static -> collect ms1 {res with mod_static=true}
	   | Final -> collect ms1 res
	   | StrictFP -> Util.fail ("Unsupported modifier 'StrictFP' (variable " ^ clvar ^ ")")
	   | Transient -> Util.fail ("Unsupported modifier 'transient' (variable " ^ clvar ^ ")")
	   | Volatile -> Util.fail ("Unsupported modifier 'volotile' (variable " ^ clvar ^ ")")
	   | Synchronized -> Util.fail ("Unsupported modifier 'synchronized' (variable " ^ clvar ^ ")")
	   | Native -> Util.fail ("Unsupported modifier 'native' (variable " ^ clvar ^ ")")
	       )
  in collect mods {mod_readonly = false; 
		   mod_public=false;
		   mod_private=false;
		   mod_ownerOpt=None; 
		   mod_static=false}

let parse_class_modifiers (cl : string) (mods : modifier list) : decl_modifiers = 
  let rec collect (ms:modifier list) res = match ms with
    | [] -> 
	let res1 = res in
	let res = (if (not res.mod_public && not res.mod_private) then
		     (
		       Debug.msg ("Class declared neither public nor private (class " ^ cl ^ "), assuming public.\n");
		      {res1 with mod_public = true})
		   else res1) in
	  (if (res.mod_public && res.mod_private) then
	     Util.fail ("Class declared both public and private (class " ^ cl ^ ")")
	   else if res.mod_ownerOpt <> None then
	     if (res.mod_private || not res.mod_public) then
	       Util.fail ("Owned variable must be public (class " ^ cl ^ ")")
	     else ());
	  res
    | m::ms1 -> 
	(match m with
	   | AnnotationModifier s ->
	       (match ParseSpec.parse_modifier "" s with
		  | Specs.Readonly -> collect ms1 {res with mod_readonly=true}
		  | Specs.ClaimedBy s -> 
		      (match res.mod_ownerOpt with
			 | None -> collect ms1 {res with mod_ownerOpt=Some s}
			 | Some _ -> Util.fail ("Cannot have multiple claimedby modifiers (class " ^ cl ^ ")")))
	   | Public -> collect ms1 {res with mod_public=true}
	   | Protected -> Util.fail ("Unsupported modifier 'protected' (class " ^ cl ^ ")")
	   | Private -> collect ms1 {res with mod_private=true}
	   | Abstract -> Util.fail ("Unsupported modifier 'abstract' (class " ^ cl ^ ")")
	   | Static -> collect ms1 {res with mod_static=true}
	   | Final -> collect ms1 res
	   | StrictFP -> Util.fail ("Unsupported modifier 'StrictFP' (class " ^ cl ^ ")")
	   | Transient -> Util.fail ("Unsupported modifier 'transient' (class " ^ cl ^ ")")
	   | Volatile -> Util.fail ("Unsupported modifier 'volotile' (class " ^ cl ^ ")")
	   | Synchronized -> Util.fail ("Unsupported modifier 'synchronized' (class " ^ cl ^ ")")
	   | Native -> Util.fail ("Unsupported modifier 'native' (class " ^ cl ^ ")")
	       )
  in collect mods {mod_readonly = false; 
		   mod_public=false;
		   mod_private=false;
		   mod_ownerOpt=None; 
		   mod_static=false}

let get_class_owner (cln : string) (ms : modifier list) : string option =
  (parse_class_modifiers cln ms).mod_ownerOpt

let translate_method_sig 
	( m  : method_decl ) 
	( class_id : string )
	: Jast.method_decl 
= 
  let method_name = id_string m.m_var.v_name in
  let mods = m.m_var.v_mods in
  let publicity = 
    if List.mem Public mods then true 
    else if List.mem Private mods then false
    else ((* Util.warn ("Method " ^ class_id ^ "." ^ method_name ^ 
		       " declared neither public nor private, assuming public.");  *)
	  true) in
  let (pre1,mod1,post1) = parse_contract method_name m.m_annotation in
  { Jast.m_name = method_name;
    Jast.m_result = m.m_var.v_type;
    Jast.m_public = publicity;
    Jast.m_static = List.mem Static mods;
    Jast.m_formals = List.map c_formal m.m_formals;  
    Jast.m_pre = pre1;
    Jast.m_modifies = mod1;
    Jast.m_post = post1;
    Jast.m_locals = [];
    Jast.m_speclocals = [];
    Jast.m_vardefs = [];
    Jast.m_body = mkbasic Jast.Empty; 
    Jast.m_constructor = (method_name = class_id); }

let translate_class_sigs (c:class_decl) : Jast.class_decl = 
  let clname = id_string c.cl_name in
  let emsg = "Error in class " ^ clname ^ "." in
  let rec collect (ds:decls) (cl:Jast.class_decl) : Jast.class_decl =
    (match ds with
       | [] -> { cl with
		   Jast.cl_claimed_fields = List.rev cl.Jast.cl_claimed_fields;
		   Jast.cl_public_fields = List.rev cl.Jast.cl_public_fields;
		   Jast.cl_private_fields = List.rev cl.Jast.cl_private_fields;
		   Jast.cl_public_globals = List.rev cl.Jast.cl_public_globals;
		   Jast.cl_private_globals = List.rev cl.Jast.cl_private_globals;
		   Jast.cl_abst_fields = List.rev cl.Jast.cl_abst_fields;
		   Jast.cl_abst_globals = List.rev cl.Jast.cl_abst_globals;
		   Jast.cl_vardefs = List.rev cl.Jast.cl_vardefs;
		   Jast.cl_constdefs = List.rev cl.Jast.cl_constdefs;
		   Jast.cl_pubconstdefs = List.rev cl.Jast.cl_pubconstdefs;
		   Jast.cl_invariants = List.rev cl.Jast.cl_invariants;
		   Jast.cl_methods = List.rev cl.Jast.cl_methods
	       }
       | d::ds0 -> 
	   (match d with
	      | Class ic -> Util.fail ("Inner classes not supported: " ^
					 "inner class " ^ id_string ic.cl_name ^ emsg)
	      | Interface ii -> Util.fail ("Inner interfaces not supported:" ^
					     "(inner interface " ^ id_string ii.if_name ^ ". "
					   ^ emsg)
	      | Field f -> 
		  (let t = f.f_var.v_type in
		   let n = f.f_var.v_name in
		   let msg = "Complex field initializers not supported: " ^
		     "at field " ^ id_string n ^ ". " ^ emsg in
		   let initial = parse_literal_opt (init_expr_to_str msg f.f_init) in
		   let mods = f.f_var.v_mods in
		   let (is_readonly,ownerOpt,is_private,is_static) = 
 		     parse_var_modifiers (clname ^ "." ^ id_string n) mods in
		   let vd = mkvdir n t initial is_readonly in
		     if is_static then
		       if is_private then
                         collect ds0 {cl with 
					Jast.cl_private_globals = vd::cl.Jast.cl_private_globals}
		       else
			 collect ds0 {cl with
					Jast.cl_public_globals = vd::cl.Jast.cl_public_globals}
		     else (* field *)
		       if is_private then
                         collect ds0 {cl with
					Jast.cl_private_fields = vd::cl.Jast.cl_private_fields}
		       else
			 (match ownerOpt with
			    | None ->
				collect ds0 {cl with
					       Jast.cl_public_fields = vd::cl.Jast.cl_public_fields}
			    | Some clname ->
				collect ds0 {cl with
					       Jast.cl_claimed_fields = (vd,clname)::cl.Jast.cl_claimed_fields})
		  )
	      | Method m ->
                  collect ds0 {cl with Jast.cl_methods =				 
		      add_distinct clname (translate_method_sig m clname) cl.Jast.cl_methods}
	      | InstanceInit s -> Util.fail ("Instance initializers not supported. " ^ emsg)
	      | StaticInit s -> Util.fail ("Static initializers not supported " ^ emsg)
	      | Constructor m ->
              	  collect ds0 
		    {cl with
		       Jast.cl_methods = translate_method_sig m (id_string c.cl_name)::cl.Jast.cl_methods}
	      | AnnotationDecl a ->
		  collect_annot a (ParseSpec.parse_specs a) ds0 cl
	   )
    )
      (* end of collect *)
  and collect_annot
      (a : string) (spcs : Specs.spec list) 
      (ds:decls) (cl:Jast.class_decl) : Jast.class_decl =
    match spcs with
      | [] -> collect ds cl
      | spc::spcs1 ->
	  (match spc with
	     | Specs.Lemma lm ->
		 collect_annot a spcs1 ds
		   {cl with 
		      Jast.cl_lemmas=lm::cl.Jast.cl_lemmas}
    	     | Specs.Invariant inv ->
		 collect_annot a spcs1 ds
		   {cl with 
		      Jast.cl_invariants=inv::cl.Jast.cl_invariants}
	     | Specs.Contract _ -> Util.fail ("Found standalone contract " ^ a ^
						" but contracts should be in method headers " ^ 
						"(after arguments, before curly brace)." ^ emsg)
	     | Specs.SpecField sf ->
		 collect_annot a spcs1 ds
		   {cl with
		      Jast.cl_abst_fields=sf::cl.Jast.cl_abst_fields}
	     | Specs.SpecStatic sg ->
		 collect_annot a spcs1 ds
		   {cl with
		      Jast.cl_abst_globals=sg::cl.Jast.cl_abst_globals}
	     | Specs.SpecVar sv ->
		 collect_annot a spcs1 ds
		   (if sv.Specs.avd_field then 
		      {cl with Jast.cl_abst_fields = sv::cl.Jast.cl_abst_fields}
		    else
		      {cl with Jast.cl_abst_globals = sv::cl.Jast.cl_abst_globals})
	     | Specs.Constdefs vds ->
		 collect_annot a spcs1 ds
		   {cl with
		      Jast.cl_constdefs = List.rev_append vds cl.Jast.cl_constdefs}
	     | Specs.PubConstdefs vds ->
		 collect_annot a spcs1 ds
		   {cl with
		      Jast.cl_pubconstdefs = List.rev_append vds cl.Jast.cl_pubconstdefs}
	     | Specs.Vardefs vds ->
		 collect_annot a spcs1 ds
		   {cl with
		      Jast.cl_vardefs = List.rev_append vds cl.Jast.cl_vardefs}
	     | Specs.PubVardefs vds ->
		 collect_annot a spcs1 ds
		   {cl with
		      Jast.cl_pubvardefs = List.rev_append vds cl.Jast.cl_pubvardefs}
	     | _ -> 
		 (Util.warn ("Unexpected annotation " ^ a ^ emsg);
		  collect_annot a spcs1 ds cl)
	  )
	    (* end of collect_annots *)
  in
  let cln = id_string c.cl_name in
    collect c.cl_body {
      Jast.cl_name = cln;
      Jast.cl_super = Util.optmap name2str c.cl_super;
      Jast.cl_owner = get_class_owner cln c.cl_mods;
      Jast.cl_impls = List.rev (List.map name2str c.cl_impls);
      Jast.cl_lemmas = [];
      Jast.cl_claimed_fields = [];
      Jast.cl_public_fields = [];
      Jast.cl_private_fields = [];
      Jast.cl_public_globals = [];
      Jast.cl_private_globals = [];
      Jast.cl_abst_fields = [];
      Jast.cl_abst_globals = [];
      Jast.cl_vardefs = [];
      Jast.cl_pubvardefs = [];
      Jast.cl_constdefs = [];
      Jast.cl_pubconstdefs = [];
      Jast.cl_invariants = [];
      Jast.cl_methods = [];
    }

let translate_interface_sigs (ifc : interface) : Jast.interface =
  let ifname = id_string ifc.if_name in
  let emsg = "Error in interface " ^ ifname ^ "." in
  let rec collect 
      (ds:decls) (** declarations to process *)
      (cif : Jast.interface) (** currently accumulated translated interface *) = 
    match ds with
      | [] -> {cif with
                Jast.if_abst_fields = List.rev cif.Jast.if_abst_fields;
                Jast.if_abst_globals = List.rev cif.Jast.if_abst_globals;
                Jast.if_constants = List.rev cif.Jast.if_constants;
		Jast.if_constdefs = List.rev cif.Jast.if_constdefs;
                Jast.if_invariants = cif.Jast.if_invariants;
                Jast.if_method_specs = List.rev cif.Jast.if_method_specs;
	      }
      | d::ds0 -> 
	  (match d with
	     | Method m ->
		 collect ds0 
		   {cif with 
		      Jast.if_method_specs = add_distinct ifname 
		       (translate_method_sig m ifname) cif.Jast.if_method_specs}
	     | AnnotationDecl a ->
		 (match ParseSpec.parse_spec a with
		    | Specs.Invariant f -> 
			collect ds0
			  {cif with Jast.if_invariants = f::cif.Jast.if_invariants}
(*		    | Specs.PubInvariant f -> 
			collect ds0
			  {cif with Jast.if_invariants = f::cif.Jast.if_invariants} *)
		    | Specs.SpecField sf ->
			collect ds0
			  {cif with Jast.if_abst_fields = sf::cif.Jast.if_abst_fields}
		    | Specs.SpecVar sv ->
			((if (not sv.Specs.avd_public) then
			    Util.warn ("Private specvar in interface makes no sense, assuming public")
			  else ());
			 collect ds0
			   (if sv.Specs.avd_field then 
			      {cif with Jast.if_abst_fields = sv::cif.Jast.if_abst_fields}
			    else
			      {cif with Jast.if_abst_globals = sv::cif.Jast.if_abst_globals}))
		    | Specs.Constdefs vds -> 
			collect ds0 
			  {cif with
			     Jast.if_constdefs = List.rev_append vds cif.Jast.if_constdefs}
		    | Specs.PubConstdefs vds ->
			collect ds0 
			  {cif with
			     Jast.if_constdefs = List.rev_append vds cif.Jast.if_constdefs}
		    | Specs.Vardefs vds ->
			collect ds0 
			  {cif with
			     Jast.if_vardefs = List.rev_append vds cif.Jast.if_vardefs}
		    | Specs.PubVardefs vds ->
			collect ds0 
			  {cif with
			     Jast.if_vardefs = List.rev_append vds cif.Jast.if_vardefs}
		    | _ -> Util.fail emsg)
             | Field f -> 
		 (
        	   (
            	     let mods = f.f_var.v_mods in
                     let t = f.f_var.v_type in
                     let n = f.f_var.v_name in
                     let msg = "Complex field initializers not supported: " ^
                       "at field " ^ id_string n ^ ". " ^ emsg in
                     let initial = parse_literal_opt (init_expr_to_str msg f.f_init) in
                     let vd = mkvdi n t initial in                
                       if List.mem Static mods & List.mem Public mods & List.mem Final mods then
                	 collect ds0 
			   {cif with Jast.if_constants = vd::cif.Jast.if_constants}
		       else
			 Util.fail( "Field modifiers incorrect (expected public static final). " ^ emsg)
		   )
		 )
             | _ -> Util.fail ("Unexpected declaration in interface." ^ emsg))
  in collect ifc.if_body {
      Jast.if_name = id_string ifc.if_name;
      Jast.if_exts = List.rev (List.map name2str ifc.if_exts);
      Jast.if_abst_fields = [];
      Jast.if_abst_globals = [];
      Jast.if_constants = [];
      Jast.if_vardefs = [];
      Jast.if_constdefs = [];
      Jast.if_invariants = [];
      Jast.if_method_specs = [];
    }

(** Convert field definitions and method signatures for all classes. *)
let compilation_unit_sigs (cus : compilation_unit list) : Jast.program =
  let rec collect 
      (ds:decls) 
      (cus:compilation_unit list) 
      (cls0:Jast.class_decl list) (ifs0:Jast.interface list) = 
    match ds with
    | [] -> (match cus with
      | [] -> (List.rev cls0, List.rev ifs0)
      | cu::cus0 -> collect cu.decls cus0 cls0 ifs0)
    | d::ds0 -> (match d with
      | Class cd -> collect ds0 cus (translate_class_sigs cd::cls0) ifs0
      | Interface i -> collect ds0 cus cls0 (translate_interface_sigs i::ifs0)
      | _ -> (Pretty.print_decl (Format.std_formatter) d;
         Util.fail "Unexpected top-level declaration: expected class or interface"))
  in let (classes,interfaces) = collect [] cus [] [] in
  { Jast.classes = classes; Jast.interfaces = interfaces }

let get_task_if_empty (prog : Jast.program) (task : analysis_task) : analysis_task =
  let get_class (cl : Jast.class_decl) : Jast.class_name = cl.Jast.cl_name in
    if task_is_empty task then
      {task with task_classes=List.map get_class prog.Jast.classes}
    else task

(* ------------------------------------------------------------ *)
(** Top-level translation function.  
   @param cus    the input program
   @param ocm    the list of (class,method)-pairs to process
   @return       the translated {!Jast} program
*)
let joust2jast 
    (cus : compilation_unit list)
    (task : analysis_task)
    : (Jast.program * analysis_task) = 
  let program_no_bodies = compilation_unit_sigs cus in
  let newTask = get_task_if_empty program_no_bodies task in
  let prog = compilation_unit_bodies program_no_bodies cus newTask in
  (* check tree consistency *)
  Jastconsistency.readonly prog;
  (prog, newTask)
