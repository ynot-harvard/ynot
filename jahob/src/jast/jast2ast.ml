(** Transforming {!Jast} abstract syntax tree to {!Ast} abstract syntax tree:
     - adding explicit preconditions
     - replacing expressions with form
     - receiver parameter translation
     - unique naming of identifeirs
     - transforming compound updates using update expressions
*)

open Form
open FormUtil
open Jast
open JastUtil
open Specs

(** Mapping types *)

let p_name ns = String.concat "." (List.map Syntax.id_string ns)

let rec c_typ (t : Syntax.typ) : typeForm = match t with
  | Syntax.TypeName [n] -> 
      let ns = Syntax.id_string n in
      if ns="int" then mk_int_type
      else if ns="boolean" then mk_bool_type
      else mk_class_type (Syntax.id_string n)
  | Syntax.TypeName [] -> Util.fail 
      ("jast2ast.c_typ: invalid empty type name, did you forget to specify type?")
  | Syntax.TypeName ns -> Util.fail 
      ("jast2ast.c_typ: invalid type name '" ^ p_name ns ^ "'.")
  | Syntax.ArrayType t1 -> mk_class_type arrayName

let rec c_class_typ (t : Syntax.typ) : string = match t with
  | Syntax.ArrayType t1 -> arrayName
  | Syntax.TypeName [n] ->
      let ns = Syntax.id_string n in
	if (ns="int" || ns="boolean" || ns="char" || ns="double" || ns="float")
	then (Util.warn ("jast2ast.c_class_typ: class name expected as type, but got " ^ ns);
	      objectName)
	else ns
  | _ -> (Util.warn "jast2ast.c_class_typ: class name expected as type";
	  objectName)

let rec c_opt_class_typ (t : Syntax.typ) : string option = match t with
  | Syntax.ArrayType t1 -> Some arrayName
  | Syntax.TypeName [n] ->
      let ns = Syntax.id_string n in
	if (ns="int" || ns="boolean" || ns="char" || ns="double" || ns="float")
	then None
	else Some ns
  | _ -> None

let clname2set (n : string) = n

(** Mapping variable and method names to identifier names *)

let c_name (base : string) (name : string) : string = 
  base ^ "." ^ name

let c_method_name (base : string) (name : string) = name
let c_field_name = c_name
let c_static_name = c_name

let c_local_name (name : string) = name

let c_formal_name (name : string) = name

let field2var (f : field) : string = c_field_name f.f_cl f.f_var.vd_name

(** Translating variable declarations *)

let lift_field_type (base : string) (t : typeForm) =
  mk_field_type t

let lift_init (init : form option) : form option =
  match init with
    | None -> None
    | Some f -> Some (Binder(Lambda,[Ast.this_tv],f))

let get_init (t : typ) : form option =
  match t with
    | Syntax.TypeName [n] -> 
	let ns = Syntax.id_string n in
	  if ns="int" then Some (mk_int 0)
	  else if ns="boolean" then Some mk_false
	  else Some mk_null
    | _ -> None

let c_literal lit = 
  match lit with
    | IntLiteral x -> mk_int x
    | BoolLiteral b -> mk_bool b
    | StringLiteral s -> mk_string s
    | NullLiteral -> mk_null
    | OtherLiteral s -> mk_var ("string__" ^ s) 

let get_init_opt (vd : var_decl) (t : typ) : form option = 
  match vd.vd_init with
    | None -> get_init t
    | Some lit -> Some (c_literal lit)
	    
let c_abstfield (modname : string) (avd : avar_decl) : Ast.var_decl = {
  Ast.vd_name = c_field_name modname avd.avd_name;
  Ast.vd_type = lift_field_type modname avd.avd_type;
  Ast.vd_init = lift_init avd.avd_init;
  Ast.vd_abstract = true;
  Ast.vd_def = None;
  Ast.vd_field = true;
  Ast.vd_ghost = avd.avd_ghost;
  Ast.vd_owner = None;
}

let c_abstglobal (modname : string) (avd : avar_decl) : Ast.var_decl = {
  Ast.vd_name = c_static_name modname avd.avd_name;
  Ast.vd_type = avd.avd_type;
  Ast.vd_init = avd.avd_init;
  Ast.vd_abstract = true;
  Ast.vd_def = None;
  Ast.vd_field = false;
  Ast.vd_ghost = avd.avd_ghost;
  Ast.vd_owner = None;
}

let c_field (cl : class_decl) (vd : var_decl) : Ast.var_decl = {
  Ast.vd_name = c_field_name cl.cl_name vd.vd_name;
  Ast.vd_type = lift_field_type cl.cl_name (c_typ vd.vd_type);
  Ast.vd_init = lift_init (get_init_opt vd vd.vd_type);
  Ast.vd_abstract = false;
  Ast.vd_def = None;
  Ast.vd_field = true;
  Ast.vd_ghost = false;
  Ast.vd_owner = if vd.vd_readonly then Some cl.cl_name else None;
}

let c_public_field_impl (cl : class_decl) (vd : var_decl) : Ast.var_decl = {
  Ast.vd_name = c_field_name cl.cl_name vd.vd_name;
  Ast.vd_type = lift_field_type cl.cl_name (c_typ vd.vd_type);
  Ast.vd_init = lift_init (get_init_opt vd vd.vd_type);
  Ast.vd_abstract = false;
  Ast.vd_def = None;
  Ast.vd_field = true;
  Ast.vd_ghost = false;
  Ast.vd_owner = if vd.vd_readonly then Some cl.cl_name else None;
}

(** used in get_global *)
let cf_global (cl : class_decl) (vd : var_decl) : Ast.global_def list = 
  match vd.vd_type with
    | Syntax.TypeName [n] -> 
	let ns = Syntax.id_string n in
	  if ns="int" then []
	  else if ns="boolean" then []
	  else [{
	    Ast.global_name = c_field_name cl.cl_name vd.vd_name;
	    Ast.global_type = c_class_typ vd.vd_type;
	  }]
    | _ -> []

(** used in get_ref_fields *)
let cf_public_field (cl : class_decl) (vd : var_decl) : Ast.field_def list = 
  match vd.vd_type with
    | Syntax.TypeName [n] -> 
	let ns = Syntax.id_string n in
	  if ns="int" then []
	  else if ns="boolean" then []
	  else [{
	    Ast.field_name = c_field_name cl.cl_name vd.vd_name;
	    Ast.field_from = cl.cl_name;
	    Ast.field_to = c_class_typ vd.vd_type;
	  }]
    | _ -> []

(** used in get_ref_fields *)
let cf_prim_field (cl : class_decl) (vd : var_decl) : Ast.field_def list = 
  match vd.vd_type with
    | Syntax.TypeName [n] -> 
	let ns = Syntax.id_string n in
	  if ns="int" then [{
	    Ast.field_name = c_field_name cl.cl_name vd.vd_name;
	    Ast.field_from = cl.cl_name;
	    Ast.field_to = "int";
	  }]
	  else if ns="boolean" then [{
	    Ast.field_name = c_field_name cl.cl_name vd.vd_name;
	    Ast.field_from = cl.cl_name;
	    Ast.field_to = "boolean";
	  }]
	  else []
    | _ -> []

let c_private_field (cl : class_decl) (vd : var_decl) : Ast.var_decl = {
  Ast.vd_name = c_field_name cl.cl_name vd.vd_name;
  Ast.vd_type = lift_field_type cl.cl_name (c_typ vd.vd_type);
  Ast.vd_init = lift_init (get_init_opt vd vd.vd_type);
  Ast.vd_abstract = false;
  Ast.vd_def = None;
  Ast.vd_field = true;
  Ast.vd_ghost = false;
  Ast.vd_owner = Some cl.cl_name;
}

let cf_private_field = cf_public_field

let c_claimed (cl : class_decl) ((vd,cm) : var_decl * string) : Ast.var_decl = {
  Ast.vd_name = c_field_name cl.cl_name vd.vd_name;
  Ast.vd_type = lift_field_type cl.cl_name (c_typ vd.vd_type);
  Ast.vd_init = lift_init (get_init_opt vd vd.vd_type);
  Ast.vd_abstract = false;
  Ast.vd_def = None;
  Ast.vd_field = true;
  Ast.vd_ghost = false;
  Ast.vd_owner = Some cm;
}

let cf_claimed (cl : class_decl) ((vd,cm) : var_decl * string) : Ast.field_def list =
  cf_public_field cl vd

let cf_prim_claimed (cl : class_decl) ((vd,cm) : var_decl * string) : Ast.field_def list =
  cf_prim_field cl vd

let c_static (cl : class_decl) (vd : var_decl) : Ast.var_decl = {
  Ast.vd_name = c_static_name cl.cl_name vd.vd_name;
  Ast.vd_type = c_typ vd.vd_type;
  Ast.vd_init = get_init_opt vd vd.vd_type;
  Ast.vd_abstract = false;
  Ast.vd_ghost = false;
  Ast.vd_def = None;
  Ast.vd_field = false;
  Ast.vd_owner = if vd.vd_readonly then Some cl.cl_name else None;
}

let c_public_static_impl (cl : class_decl) (vd : var_decl) : Ast.var_decl = {
  Ast.vd_name = c_static_name cl.cl_name vd.vd_name;
  Ast.vd_type = c_typ vd.vd_type;
  Ast.vd_init = get_init_opt vd vd.vd_type;
  Ast.vd_abstract = false;
  Ast.vd_ghost = false;
  Ast.vd_def = None;
  Ast.vd_field = false;
  Ast.vd_owner = if vd.vd_readonly then Some cl.cl_name else None;
}

let c_private_static (cl : class_decl) (vd : var_decl) : Ast.var_decl = {
  Ast.vd_name = c_static_name cl.cl_name vd.vd_name;
  Ast.vd_type = c_typ vd.vd_type;
  Ast.vd_init = get_init_opt vd vd.vd_type;
  Ast.vd_abstract = false;
  Ast.vd_ghost = false;
  Ast.vd_def = None;
  Ast.vd_field = false;
  Ast.vd_owner = Some cl.cl_name;
}

let c_speclocal (avd : avar_decl) : Ast.var_decl = {
  Ast.vd_name = avd.avd_name;
  Ast.vd_type = avd.avd_type;
  Ast.vd_init = avd.avd_init;
  Ast.vd_abstract = true;
  Ast.vd_ghost = avd.avd_ghost;
  Ast.vd_def = None;
  Ast.vd_field = false;
  Ast.vd_owner = None;
}

let c_local (vd : var_decl) : Ast.var_decl = {
  Ast.vd_name = c_local_name vd.vd_name;
  Ast.vd_type = c_typ vd.vd_type;
  Ast.vd_init = None;
  Ast.vd_abstract = false;
  Ast.vd_ghost = false;
  Ast.vd_def = None;
  Ast.vd_field = false;
  Ast.vd_owner = None;
}

let c_formal (vd : var_decl) : Ast.var_decl = {
  Ast.vd_name = c_formal_name vd.vd_name;
  Ast.vd_type = c_typ vd.vd_type;
  Ast.vd_init = None;
  Ast.vd_abstract = false;
  Ast.vd_ghost = false;
  Ast.vd_def = None;
  Ast.vd_field = false;
  Ast.vd_owner = None;
}

(*
let extract_globals (cl : class_decl) : Ast.var_decl list =   
  let add_global (vd : var_decl) (vds : Ast.var_decl list) = {
    Ast.vd_name = c_static_name cl.cl_name vd.vd_name;
    Ast.vd_type = c_typ vd.vd_type;
    Ast.vd_init = None;
  } :: vds 
  in
  let add_field (vd : var_decl) (vds : Ast.var_decl list) = {
    Ast.vd_name = c_field_name cl.cl_name vd.vd_name;
    Ast.vd_type = lift_field_type cl.cl_name (c_typ vd.vd_type);
    Ast.vd_init = None;
  } :: vds 
  in 
    List.fold_right add_field cl.cl_public_fields       
      (List.fold_right add_global cl.cl_public_globals [])
*)
  
let none_to_true (fo : form option) : form = match fo with
  | None -> mk_true
  | Some f -> f

let this_param (clname : string) : Ast.var_decl = {
  Ast.vd_name = "this";
  Ast.vd_type = mk_class_type clname;
  Ast.vd_init = None;
  Ast.vd_abstract = false;
  Ast.vd_ghost = false;
  Ast.vd_def = None;
  Ast.vd_field = false;
  Ast.vd_owner = None;
}

let translate_vardef (classn : string) ((v,f) : var_def) : var_def = 
  (c_name classn v,f)

let translate_proc_vardef ((v,f) : var_def) : var_def = 
  (* no qualification when translating procedures *)
  (v,f)

let c_method_spec 
    (context : string)  (* context is class or interface name *)
    (ml : method_decl) : Ast.proc_header = {
  Ast.p_name = c_method_name context ml.m_name;
  Ast.p_formals = 
    (let explicit = List.map c_formal ml.m_formals in
       if ml.m_static then explicit
       else this_param context :: explicit);
  Ast.p_restype =
    (let t = ml.m_result in
       if (Jtype.is_void t || ml.m_constructor) then mk_unit_type
       else c_typ t);
  Ast.p_contract = {
    Ast.co_pre = none_to_true ml.m_pre;
    Ast.co_mod = ml.m_modifies;
    Ast.co_post = none_to_true ml.m_post;
    Ast.co_resolved = false;
  };
  Ast.p_public = ml.m_public;
}

let c_public_method_spec
    (context : string)
    (ml : method_decl) : Ast.proc_header list =
  if ml.m_public then [c_method_spec context ml] else []

let block (sts0 : Ast.command list) : Ast.command =
  let rec collect sts acc = match sts with
    | [] -> acc
    | (Ast.Seq nsts)::sts1 -> collect sts1 (collect nsts acc)
    | st::sts1 -> collect sts1 (st::acc) in
  Ast.Seq (List.rev (collect sts0 []))

let c_lval (lv : lval) : string = match lv with
  | Jast.LocalVar vd -> c_local_name vd.vd_name
  | Jast.StaticVar cv -> c_static_name cv.cv_cl cv.cv_var.vd_name

let c_simpval (sv : simpval) : form = match sv with
  | Jast.LiteralVal s -> c_literal s
  | Jast.VarVal lv -> mk_var (c_lval lv)
  | Jast.ParamVar vd -> mk_var (c_formal_name vd.vd_name)

let c_method 
    (prog : program)
    (cl : class_decl)
    (ml : method_decl) : Ast.proc_def = 
  let clname = cl.cl_name in
  let c_olval olv = match olv with
    | None -> None
    | Some lv -> Some (c_lval lv) in
  let c_osimpval (osv : simpval option) = match osv with
    | None -> None
    | Some sv -> Some (c_simpval sv) in

  let no_pre f = (f,mk_true,"") in

  let c_postfix (x: form) (op : string) =
    Util.fail ("jast2ast: Don't know how to handle postfix op " ^ op) in

  let c_prefix (op : string) (x : form) = 
    if op="-" then no_pre (mk_uminus x)
    else if (op="!" || op="not") then no_pre (mk_not x)
    else Util.fail ("jast2ast: Don't know how to handle prefix op " ^ op) in

  let c_infix (x : form) (op : string) (y : form) : 
      (form * form * string) =
    if op="==" then no_pre (mk_eq(x,y))
    else if op="!=" then no_pre (mk_neq(x,y))
    else if op="<" then no_pre (mk_lt(x,y))
    else if op=">" then no_pre (mk_gt(x,y))
    else if op="<=" then no_pre (mk_lteq(x,y))
    else if op=">=" then no_pre (mk_gteq(x,y))
    else if op="+" then no_pre (mk_plus(x,y))
    else if op="-" then no_pre (mk_minus(x,y))
    else if op="*" then no_pre (mk_mult(x,y))
    else if op="/" then 
      let pre = mk_neq(y,mk_int 0) in
	(mk_div(x,y), pre, "division by zero")
    else if op="%" then no_pre (mk_mod(x,y))
    else if op="&&" then no_pre (mk_and [x;y])
    else if op="and" then no_pre (mk_and [x;y])
    else if op="||" then no_pre (mk_or [x;y])
    else if op="or" then no_pre (mk_or [x;y])
    else Util.fail ("Don't know how to type infix operator " ^ op) in

  let c_expr (e : expr) : (form * form * string) 
      (* (res,pre,pre_msg) *) = 
    match e with
      | Val x -> no_pre (c_simpval x)
      | Cast(t,x) ->
	  let x_f = c_simpval x in
	  let tn = c_class_typ t in
	  let t_f = mk_var (Ast.obj_var tn) in
	  let pre = mk_and[mk_neq(x_f,mk_null);
			   mk_elem(x_f, t_f)] in
	  let pre_msg = "typecast into" ^ tn in
	    (x_f,pre,pre_msg)
      | InstanceOf(x,t) ->
	  let x_f = c_simpval x in
	  let tn = c_class_typ t in
	  let t_f = mk_var (clname2set tn) in
	  let res = mk_and[mk_neq(x_f,mk_null);
			   mk_elem(x_f, t_f)] in
	    no_pre res
      | FieldDeref(x,f) ->
	  let x_f = c_simpval x in
	  let f_f = mk_var (field2var f) in
	  let res = mk_fieldRead f_f x_f in
	  let (pre,pre_msg) = 
	    if is_this_val x then (mk_true,"")
	    else (mk_neq(x_f,mk_null),"null dereference") in
	    (res,pre,pre_msg)
      | ArrayAccess(a,i) ->
	  let a_f = c_simpval a in
	  let i_f = c_simpval i in
	  let pre = mk_and [mk_lteq(mk_int 0, i_f);
			    mk_lt(i_f,mk_arrayLength a_f)] in
	  let pre_msg = "array read bounds check" in
	  let res = mk_arrayRead1 a_f i_f in
	    (res,pre,pre_msg)
      | Postfix(x,op) -> c_postfix (c_simpval x) op
      | Prefix(op,x) -> c_prefix op (c_simpval x)
      | Infix(x,op,y) -> c_infix (c_simpval x) op (c_simpval y)
  in

  let mkbasic = AstUtil.mkbasic in

  let mk_annot_form (omsg : string option) (f : form) = {
    Ast.annot_form = f;    
    Ast.annot_msg = (match omsg with
		       | None -> ""
		       | Some m -> m);
  } in
  let mk_assume = AstUtil.mk_assume and mk_assert = AstUtil.mk_assert and
      mk_assign = AstUtil.mk_assign
  in

  (** Expand incorporate operation into guarded command language 

      incorporate(o1):
       assert o1.owner = NoOwner
       o1.owner :=  C (the class where statement is executed)

  *)
  let expand_incorporate_no_check_op (cname : string) (o1 : form) : Ast.command =     
    let updated_field = mk_fieldWrite Ast.owner_field o1 (AstUtil.mk_class_token cname) in
      mk_assign Ast.owner_field_name updated_field
  in
  let expand_incorporate_op (cname : string) (o1 : form) : Ast.command =     
    let pre = mk_eq(AstUtil.mk_owner_of o1, AstUtil.no_owner_token) in
      block [mk_assert pre ("IncorporatedObjectCannotHaveOwner" ^ cname);
	     expand_incorporate_no_check_op cname o1]
  in

  (** Expand release operation into guarded command language 

     release(o1):
       assert o1.owner = C (the class where statement is executed)
       o1.owner :=  NoOwner

  *)
  let expand_release_op (cname : string) (o1 : form) : Ast.command =
    let pre = mk_eq(AstUtil.mk_owner_of o1, AstUtil.mk_class_token cname) in
    let updated_field = mk_fieldWrite Ast.owner_field o1 AstUtil.no_owner_token in
      block [mk_assert pre ("mustOwnReleasedObjectIn" ^ cname);
	     mk_assign Ast.owner_field_name updated_field]
  in

    (** make assume statement that given variable has given type and is allocated,
    unless it is of primitive type *)
  let local_assumption (vd : var_decl) : Ast.command list =
    let id = vd.vd_name in
    let clname_opt = c_opt_class_typ vd.vd_type in
      match clname_opt with
	| None -> []
	| Some clname -> 
	    (let idf = mk_var id in
	       [mk_assume (mk_and [mk_elem(idf,mk_var (Ast.obj_var clname));
				  mk_elem(idf,Ast.all_alloc_objsf)]) (id ^ "_type")])
  in

  let is_object_type (vd : var_decl) =  
    let clname_opt = c_opt_class_typ vd.vd_type in
      match clname_opt with
	| None -> false
	| Some clname -> true
  in

  let is_object_type_lval : lval -> bool = function
      | LocalVar vd -> is_object_type vd
      | StaticVar {cv_var=vd} -> is_object_type vd
  
  in

    (** make assume statement that given variable is not hidden, unless it is of primitive type *)
  let non_hidden_assumption (vd : var_decl) : Ast.command list =
    let id = vd.vd_name in
    let idf = Var id in
      if is_object_type vd then [JastUtil.mk_assume_not_hidden idf] else []
  in
  
 let non_hidden_assertion (vd : var_decl) : Ast.command list =
    let id = vd.vd_name in
    let idf = Var id in
      if is_object_type vd then [JastUtil.mk_assume_not_hidden idf] else []
  in

  let local_assumption_lval (olv : lval option) : Ast.command list =
    match olv with
      | None -> []
      | Some (LocalVar vd) -> local_assumption vd
      | Some (StaticVar {cv_var=vd}) -> local_assumption vd
  in

 let non_hidden_assumption_lval (olv : lval option) : Ast.command list =
   match olv with
      | None -> []
      | Some (LocalVar vd) -> non_hidden_assumption vd
      | Some (StaticVar {cv_var=vd}) -> non_hidden_assumption vd
 in

 let non_hidden_assertion_lval (olv : lval option) : Ast.command list =
   match olv with
      | None -> []
      | Some (LocalVar vd) -> non_hidden_assertion vd
      | Some (StaticVar {cv_var=vd}) -> non_hidden_assertion vd
 in

 let non_hidden_assertion_simpval (sv : simpval) : Ast.command list =
   match sv with
     | VarVal lval -> non_hidden_assertion_lval (Some lval)
     | ParamVar vdecl -> non_hidden_assertion vdecl
     | LiteralVal _ -> [] (* basetype *)

in
    (** assumption about the receiver within each method *)
  let this_assumption (clname : string) = 
    let not_null = mk_assume (mk_neq(mk_var this_id,mk_null)) "thisNotNull" in
    let this_type = mk_assume (mk_and [mk_elem(mk_var this_id,mk_var (Ast.obj_var clname));
				       mk_elem(mk_var this_id,Ast.all_alloc_objsf)]) "thisType" in
      block [not_null; this_type] in

  let c_dyn_call (pc : dyn_proc_call) : Ast.command = 
    let this_arg = c_simpval pc.dcall_obj in
    let newargs0 = List.map c_simpval pc.dcall_args in
    let newargs = this_arg :: newargs0 in
    let receiver_cl_name (* statically known class *) = 
      get_simpval_typ_name pc.dcall_obj in 
    let this_not_null : Ast.command = mk_assert (mk_neq(this_arg,mk_null)) "receiverNotNull" in
    let the_call : Ast.command =
      mkbasic 
	(Ast.ProcCall {
	   Ast.callee_res = c_olval pc.dcall_res;
	   Ast.callee_module = find_declared_class_for pc.dcall_method receiver_cl_name prog;
	   Ast.callee_name = c_method_name receiver_cl_name pc.dcall_method;
	   Ast.callee_hdr = None;
	   Ast.callee_args = newargs;
	   Ast.call_is_external = true;
	 }) in
    let res_asm = local_assumption_lval pc.dcall_res in
    let not_hidden_res :  Ast.command list = 
      if !CmdLine.checkHidden then non_hidden_assumption_lval pc.dcall_res else [] in
    let not_hidden_arg : Ast.command list = 
      if !CmdLine.checkHidden then List.concat (List.map non_hidden_assertion_simpval pc.dcall_args) else [] in
    block ([this_not_null] @ not_hidden_arg @ [the_call] @ res_asm @ not_hidden_res)
 in

  let c_stat_call (pc : stat_proc_call) : Ast.command =
    let call_is_internal = 
      (pc.scall_class = cl.cl_name) && 
	is_private_method cl pc.scall_method in
    let the_call = mkbasic 
      (Ast.ProcCall {
	 Ast.callee_res = c_olval pc.scall_res;
	 Ast.callee_module = pc.scall_class;
	 Ast.callee_name = c_method_name pc.scall_class pc.scall_method;
	 Ast.callee_hdr = None;
	 Ast.callee_args = List.map c_simpval pc.scall_args;
	 Ast.call_is_external = not call_is_internal;
       }) in

    let not_hidden_res = 
      if !CmdLine.checkHidden then non_hidden_assumption_lval pc.scall_res else [] in
    let not_hidden_arg = 
      if !CmdLine.checkHidden then List.concat (List.map non_hidden_assertion_simpval pc.scall_args) else [] in

    
    let res_asm = local_assumption_lval pc.scall_res in
      block (not_hidden_arg @ [the_call] @ res_asm @ not_hidden_res)
    in
  let c_constructor_call (pc : constructor_call) : Ast.command = 
    let res = match pc.con_res with
      | None -> Util.fail 
	  "jast2ast.c_constructor_call: No constructor result"
      | Some r -> c_lval r in
    let newclass = pc.con_class in
    let alloc = mkbasic (Ast.Alloc { 
			   Ast.alloc_lhs = res;
			   Ast.alloc_tlhs = (res,TypeUniverse);
			   Ast.alloc_type = newclass }) in
      (** x.owner := CurrentClassName *)
    let set_owner = 
      if !CmdLine.tokens then 
	[expand_incorporate_no_check_op clname (mk_var res)]
      else [] 
    in
    let init_proc = 
      if pc.con_is_default then []
      else 
	(let the_call =
	   mkbasic (Ast.ProcCall {
	 	      Ast.callee_res = None;
	 	      Ast.callee_module = pc.con_class;
	 	      Ast.callee_name = pc.con_class;
	 	      Ast.callee_hdr = None;
	 	      Ast.callee_args = 
			mk_var res :: List.map c_simpval pc.con_args;
		      Ast.call_is_external = true;
       		    }) in
	 let res_asm = local_assumption_lval pc.con_res 
	 in 
	   the_call :: res_asm)
    in
      block (alloc :: (set_owner @ init_proc)) in

  let c_bstmt (st : basic_stmt) : Ast.command = 
    let scanning_f id = function 
      |{vd_name=x} when x=id -> true 
      | _ -> false
    in
      match st with
      | Empty -> mkbasic Ast.Skip
      | VarAssign(lv,e) ->
	  let is_lhs_local = not (JastUtil.is_lval_static lv) in
	  let lv_name = JastUtil.id_of_lvar lv in
	  let is_private =  ListLabels.exists ~f:(scanning_f lv_name) cl.cl_private_globals in
	  let is_public =  ListLabels.exists ~f:(scanning_f lv_name) cl.cl_public_globals in
	    assert (is_lhs_local || is_private || is_public); (* just in case. You never know...*)
	    
	    let (res,pre,pre_msg) = c_expr e in

	    let hiding_condition = if is_public && !CmdLine.checkHidden && is_object_type_lval lv then 
	      [JastUtil.mk_assert_not_hidden res]
	    else [] 
	    in
	    let assign_st = mk_assign (c_lval lv) res in
	    let possible_check = if pre=mk_true then [] else [mk_assert pre pre_msg] in
	    block (hiding_condition @ possible_check @ [assign_st])

    | FieldAssign(x,f,y) -> 
	let x_f = c_simpval x in
	let y_f = c_simpval y in
	let f_v = field2var f in	  
	let null_check_form = mk_neq(x_f, mk_null) in
	let rhs = mk_fieldWrite (mk_var f_v) x_f y_f in  

	let is_x_this = is_this_val x in

	let is_field_public = 
	  if is_x_this then 
	    ListLabels.exists ~f:(scanning_f f.f_var.vd_name) cl.cl_public_fields
	  else true (* ensured by the Java type system ! *)
	in
	  
	let is_field_object = is_object_type f.f_var in

	let hiding_cond = if is_field_public && !CmdLine.checkHidden && is_field_object then 
	  [AstUtil.mk_assert 
	     (FormUtil.mk_impl (FormUtil.mk_elem (y_f, Var Jast.hidden_set_name), 
				FormUtil.mk_elem (x_f, Var Jast.hidden_set_name)))
	     "object is hidden in non-private field assignment"] 
	else 
	  [] in
	let assign_st = mk_assign f_v rhs in
	let null_check = if is_x_this then [] else [mk_assert null_check_form "null check"] in
	  block (hiding_cond @ null_check @ [assign_st] )
		      
    | ArrayAssign(a,i,v) ->
	let a_f = c_simpval a in
	let i_f = c_simpval i in
	let v_f = c_simpval v in
        let null_check_form = mk_neq(a_f, mk_null) in
	let bounds_check_form =
	  mk_and [mk_lteq(mk_int 0, i_f);
                  mk_lt(i_f,mk_arrayLength a_f)] in
	let rhs = mk_arrayWrite1 a_f i_f v_f in

	let hiding_cond = if !CmdLine.checkHidden then 
	  [AstUtil.mk_assert 
	     (FormUtil.mk_impl (FormUtil.mk_elem (v_f, Var Jast.hidden_set_name), 
				FormUtil.mk_elem (a_f, Var Jast.hidden_set_name)))
	     "object is hidden in array[i] assignment"] else [] in

	  block (mk_assert null_check_form "array non-null check" :: (
		   hiding_cond @ [
		     mk_assert bounds_check_form "array write bounds check";
		     mk_assign arrayStateId rhs
		   ]))
    | ConstructorCall cc ->
	c_constructor_call cc
    | NewArray(lv,t,dims) -> 
	let lvv = c_lval lv in
	  mkbasic (Ast.ArrayAlloc {
		     Ast.arr_alloc_lhs = lvv;
		     Ast.arr_alloc_tlhs = (lvv,TypeUniverse);
		     Ast.arr_alloc_type = t;
		     Ast.arr_alloc_dims = List.map c_simpval dims})
    | DynProcCall pc -> c_dyn_call pc
    | StatProcCall pc -> c_stat_call pc
    | Jast.Havoc fs -> 
	mkbasic (Ast.Havoc {
		   Ast.havoc_regions = fs})
    | Jast.Assert(omsg,f) -> mkbasic (Ast.Assert (mk_annot_form omsg f))
    | Jast.NoteThat(omsg,f) -> mkbasic (Ast.NoteThat (mk_annot_form omsg f))
    | Jast.Assume(omsg,f) -> mkbasic (Ast.Assume (mk_annot_form omsg f))
    | Jast.Split(omsg,f) -> mkbasic (Ast.Split (mk_annot_form omsg f))

    | Jast.AbstAssign(f_l,f_r) -> 
	(match f_l with
	   | Var id -> 
	       let scanning_f = function 
		 |{Specs.avd_name=x} when x=id -> true 
		 | _ -> false
	       in
		 if ListLabels.exists ~f:scanning_f cl.cl_abst_globals then
		   (* it's an abtract static variable *)
		   mk_assign id f_r
		 else
		   if ListLabels.exists ~f:scanning_f cl.cl_abst_fields then
		     (* it's an abstract field of this *)
		     mk_assign id (mk_fieldWrite (Var id) (Var "this") f_r)
		   else
		     (* it's a local abstract variable *)
		     mk_assign id f_r		     


	   | App (Const FieldRead, [Var field ; obj]) -> 
	       (* it's an abtrsact field of another object*)
	       mk_assign field (mk_fieldWrite (Var field) obj f_r)

	   | _ -> failwith "jast2ast : lhs of abtract assignment too complicated (or wrong)"
      )

    | Jast.AbstOperation {ao_name=name; ao_args=args} ->
	let cname = cl.cl_name in
	if name = release_op_name then
	  (match args with
	     | [f] -> expand_release_op cname f
	     | _ -> Util.fail "Jast2ast: Wrong number of arguments to release")
	else if name = incorporate_op_name then
	  (match args with
	     | [f] -> expand_incorporate_op cname f
	     | _ -> Util.fail "Jast2ast: Wrong number of arguments to incorporate")
	else if name = track_specvar_op_name then
	  (match args with
	     | [Var id] -> mkbasic (AstUtil.mk_track_specvar id)
	     | _ -> Util.fail ("Jast2ast: Wrong arguments to " ^ 
		 track_specvar_op_name))
	else
	  Util.fail ("Jast2ast: Unknown abstract operation " ^ name)
  in
  let rec c_stmt (st : stmt) : Ast.command = match st with
    | Basic(bst,cfgn) -> c_bstmt bst
    | Block sts -> block (List.map c_stmt sts)
    | If(sv,st1,st2) -> 
	Ast.If {
	  Ast.if_condition = c_simpval sv;
	  Ast.if_then = c_stmt st1;
	  Ast.if_else = c_stmt st2
	}
    | Loop(oinv,st1,sv,st2) -> 
	Ast.Loop {
	  Ast.loop_inv = oinv;
	  Ast.loop_prebody = c_stmt st1;
	  Ast.loop_test = c_simpval sv;
	  Ast.loop_postbody = c_stmt st2;
	}
    | Return sv -> Ast.Return {Ast.return_exp = c_osimpval sv} 

in

(* c_method body *)
    { Ast.p_header = c_method_spec (cl.cl_name) ml;     
      Ast.p_locals = List.map c_speclocal ml.m_speclocals @ List.map c_local ml.m_locals;
      Ast.p_vardefs = List.map translate_proc_vardef ml.m_vardefs;
      Ast.p_body =
	(let formals_not_hidden = if !CmdLine.checkHidden then 
	  (* FIXME : is it a real problem if base type are declared non-hidden ? 
	     Answer : yes : it breaks types 
	     LOCATE-ME : ??? *)
	  List.map non_hidden_assumption ml.m_formals
	else [] in
	let b0 = c_stmt ml.m_body in
	 let b1 = block 
	   (List.concat 
	      (List.map local_assumption (ml.m_formals @ ml.m_locals) 
	       @ formals_not_hidden
	       @ [[b0]])
	   ) in
	   if ml.m_static then b1
	   else block (this_assumption clname :: [b1])
	);
      Ast.p_simple_body = None;
    }

(** Check whether a variable definition in a class
    is defining a public variable (as opposed to defining
    a private variable and thus being used as a private
    shorthand). *)
let is_abstfun_def
    (cl : class_decl) 
    ((v,d) : var_def) : bool =
  let cn = cl.cl_name in
  let v1 = Util.qualify_if_needed cn v in
  let rec check (avds : avar_decl list) : bool = 
    match avds with
      | [] -> false
      | avd::avds1 ->
	  if (Util.qualify_if_needed cn avd.avd_name) = v1 then
	    avd.avd_public
	  else
	    check avds1
  in
    check (cl.cl_abst_fields @ cl.cl_abst_globals)

let is_not_abstfun_def 
    (cl : class_decl) 
    ((v,d) : var_def) : bool =
  not (is_abstfun_def cl (v,d))

let is_public (avd : abstract_var_decl) : bool = avd.avd_public
let is_not_public (avd : abstract_var_decl) : bool = not avd.avd_public

(** get types of global variables, because they are lost in
    Isabelle types *)
let get_globals (cl : class_decl) : Ast.global_def list =
  List.concat 
    (List.map (cf_global cl) (cl.cl_public_globals @ cl.cl_private_globals))

(** get reference field descriptions, because they are lost in
    Isabelle types *)
let get_ref_fields (cl : class_decl) : Ast.field_def list =
  List.concat 
    (List.map (cf_claimed cl) cl.cl_claimed_fields @
       List.map (cf_public_field cl) cl.cl_public_fields @
       List.map (cf_private_field cl) cl.cl_private_fields)

(** get primitive field descriptions, because the source information is lost in
    Isabelle types *)
let get_prim_fields (cl : class_decl) : Ast.field_def list =
  List.concat 
    (List.map (cf_prim_claimed cl) cl.cl_claimed_fields @
       List.map (cf_prim_field cl) cl.cl_public_fields @
       List.map (cf_prim_field cl) cl.cl_private_fields)

let c_lemma (lm : Specs.lemma_desc) : string * form =
  (lm.Specs.lemma_name, lm.Specs.lemma_form)

(** generates the var declaration for the abstract "hidden" set-valued field containing hidden objects of the class *)
let generate_hidden_field (modname : string) : Ast.var_decl = {
  Ast.vd_name = modname ^ "." ^ Jast.hidden_set_name; 
  Ast.vd_type = (FormUtil.mk_set_type mk_object_type);
  Ast.vd_init = Some (FormUtil.mk_emptyset);
  Ast.vd_abstract = true;
  Ast.vd_def = None;
  Ast.vd_field = false;
  Ast.vd_ghost = true;
  Ast.vd_owner = None;
}


(** Convert class with body *)
let c_class (prog : program) (cl : class_decl) : Ast.impl_module = {
  Ast.im_name = cl.cl_name;
  Ast.im_owner = cl.cl_owner;
    (* all non-specification variables *)
  Ast.im_vars = generate_hidden_field (cl.cl_name) ::  (
    List.map (c_claimed cl) cl.cl_claimed_fields @
    List.map (c_public_field_impl cl) cl.cl_public_fields @
    List.map (c_private_field cl) cl.cl_private_fields @
    List.map (c_public_static_impl cl) cl.cl_private_globals @
    List.map (c_private_static cl) cl.cl_public_globals @
    (List.map (c_abstglobal cl.cl_name) 
       (List.filter is_not_public cl.cl_abst_globals)) @
    (List.map (c_abstfield cl.cl_name) 
       (List.filter is_not_public cl.cl_abst_fields)));

  Ast.im_vardefs = List.map (translate_vardef cl.cl_name) 
    (List.filter (is_not_abstfun_def cl) cl.cl_vardefs);
  Ast.im_constdefs = List.map (translate_vardef cl.cl_name) cl.cl_constdefs;
  Ast.im_invs = cl.cl_invariants;
  Ast.im_procs = List.map (c_method prog cl) cl.cl_methods;
  Ast.im_lemmas = List.map c_lemma cl.cl_lemmas;
}

let c_interface (ifc : interface) : Ast.spec_module = {
  Ast.sm_name = ifc.if_name;
  Ast.sm_spec_vars = 
    List.map (c_abstfield ifc.if_name) ifc.if_abst_fields @
      List.map (c_abstglobal ifc.if_name) ifc.if_abst_globals;
  Ast.sm_vardefs = List.map (translate_vardef ifc.if_name) ifc.if_vardefs;
  Ast.sm_constdefs = List.map (translate_vardef ifc.if_name) ifc.if_constdefs;
  Ast.sm_invs = ifc.if_invariants; (* free_inv will be populated by ResolveAst.ml *)
  Ast.sm_free_invs = [];
  Ast.sm_proc_specs = 
    List.concat (List.map (c_public_method_spec ifc.if_name) ifc.if_method_specs)
}


let c_class_spec (cl : class_decl) : Ast.spec_module = {
  Ast.sm_name = cl.cl_name;
  Ast.sm_spec_vars = 
    List.map (c_field cl) cl.cl_public_fields @
      List.map (c_static cl) cl.cl_public_globals @
      (List.map (c_abstfield cl.cl_name) 
         (List.filter is_public cl.cl_abst_fields)) @
      (List.map (c_abstglobal cl.cl_name) 
         (List.filter is_public cl.cl_abst_globals)) @
      List.map (c_claimed cl) cl.cl_claimed_fields; 
  Ast.sm_vardefs = List.map (translate_vardef cl.cl_name) cl.cl_pubvardefs;
  Ast.sm_constdefs = List.map (translate_vardef cl.cl_name) cl.cl_pubconstdefs;
  Ast.sm_invs = ListLabels.filter ~f:(function {Specs.inv_public=x} -> x) cl.cl_invariants;
  Ast.sm_free_invs = []; (* they are going to be assigned in ResolveAst.ml *)
  Ast.sm_proc_specs = 
    List.concat (List.map (c_public_method_spec cl.cl_name) cl.cl_methods);
}

let extract_map (p : Ast.program) (cl : class_decl) : Ast.mapping list = 
  let classn = cl.cl_name in
  let defs = List.filter (is_abstfun_def cl) cl.cl_vardefs in    
    [{
       Ast.map_impl = AstUtil.must_find_im classn p;
       Ast.map_spec = AstUtil.must_find_sm classn p;
       Ast.map_abst = List.map (translate_vardef classn) defs;
     }]

(** Convert a {!Jast} program into {!Ast} program. *)
let c_program (p : Jast.program) : Ast.program = 
  let p1 = {
    Ast.p_types = [];
    Ast.p_impls = List.map (c_class p) p.classes;
    Ast.p_specs = 
      List.map c_interface p.interfaces @
	List.map c_class_spec p.classes;
    Ast.p_maps = [];

    Ast.p_globals = List.concat (List.map get_globals p.classes);
    Ast.p_ref_fields = List.concat (List.map get_ref_fields p.classes);
    Ast.p_prim_fields = List.concat (List.map get_prim_fields p.classes);
  } in 
  let p2 = { 
    p1 with Ast.p_maps = 
      List.concat (List.map (extract_map p1) p.classes)
  } in
  let _ = ResolveAst.init_resolver() in
  let add_class_setid (cl : class_decl) =
    ResolveAst.resolver_add (cl.cl_name,mk_set_type mk_object_type) in
  let _ = List.iter add_class_setid p.classes in
  let add_interface_setid (ifc : interface) =
    ResolveAst.resolver_add (ifc.if_name,mk_set_type mk_object_type) in
  let _ = List.iter add_interface_setid p.interfaces in
  let _ = ResolveAst.resolve_program p2 in
    p2
