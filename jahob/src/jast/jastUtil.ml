(** Utility functions for searching and manipulating {!Jast} tree. *)

open Jast

(* ------------------------------------------------------------ *)
(**                    Class inheritance hierarchy              *)
(* ------------------------------------------------------------ *)

type inherit_edges = (string * string option) list
type inheritance = {
  nodes : string list;
  superclass : inherit_edges;
}

let get_superclass (cl : class_decl) : string * string option =
  (cl.cl_name, cl.cl_owner)

let get_domain (inh : inherit_edges) : string list =
  Util.remove_dups (List.map fst inh)

let get_inheritance (p : program) : inheritance =
  let sup = List.map get_superclass p.classes in
    {nodes = get_domain sup;
     superclass = sup}

let check_acyclic (inh : inheritance) : unit = () (* !!! FINISH *)

(* ------------------------------------------------------------ *)
(**                    Looking up constructs in ast             *)
(* ------------------------------------------------------------ *)

let pr_name n = String.concat "." (List.map Syntax.id_string n)

let mkbasic (b : basic_stmt) : stmt = 
  Basic(b,{cfg_pos=0; cfg_name="generated"})

let slval_asgn (lv : lval) (rhs : simpval) =
  mkbasic (VarAssign(lv, Val rhs))

let local_asgn (vd : var_decl) (rhs : simpval) =
  slval_asgn (LocalVar vd) rhs

let slocal_asgn (vd : var_decl) (rhs : simpval) =
  local_asgn vd rhs

let sglobal_asgn (cn : class_name) (vd : var_decl) (rhs : simpval) =
  mkbasic (VarAssign(StaticVar {cv_cl=cn; cv_var=vd},Val rhs))

let mk_assert (f : Form.form) : stmt = 
  mkbasic (Assert(None,f))

let mk_noteThat (f : Form.form) : stmt = 
  mkbasic (NoteThat(None,f))

let mk_assume (f : Form.form) : stmt = 
  mkbasic (Assume(None,f))

let mk_split (f : Form.form) : stmt = 
  mkbasic (Split(None,f))

let mk_havoc (fs : Form.form list) : stmt = 
  mkbasic (Havoc fs)

let mk_aassign (lhs : Form.form) (rhs : Form.form) : stmt = 
  mkbasic (AbstAssign(lhs,rhs))

let mk_aoperation (ao : Specs.abstract_operation) : stmt = 
  mkbasic (AbstOperation ao)

let get_class (p : program) (cln : class_name) : class_decl option =
  let rec search (cls : class_decl list) : class_decl option =
    match cls with
    | [] -> None
    | cl::cls0 -> 
        if cl.cl_name=cln then Some cl
        else search cls0
  in search p.classes

let get_interface (p : program) (ifn : class_name) : interface option =
  let rec search (ifss : interface list) : interface option =
    match ifss with
    | [] -> None
    | ifs::ifss0 -> 
        if ifs.if_name=ifn then Some ifs
        else search ifss0
  in search p.interfaces

let must_get_class (p :program) (cln: class_name) : class_decl =
  match get_class p cln with
    | None -> Util.fail ("Failed to retrieve definition of class " ^ cln)
    | Some cl -> cl

let rec find_var (vds : var_decl list) (vn : var_name) : var_decl option =
  match vds with
    | [] -> None
    | vd::vds1 -> if vd.vd_name=vn then Some vd else find_var vds1 vn

let find_static_var (c : class_decl) (vn : var_name) : var_decl option =
  find_var (c.cl_public_globals @ c.cl_private_globals) vn

let find_field (c : class_decl) (fn : field_name) : field option =
  match find_var (c.cl_public_fields @ c.cl_private_fields @ 
		    (List.map fst c.cl_claimed_fields)) fn with
    | None -> None
    | Some vd -> Some { f_cl=c.cl_name; f_var=vd }

let rec get_field (prog : program) (cl : class_decl) (fn : field_name) : field option =
  match find_field cl fn with
    | Some vd -> Some vd
    | None ->
	(match cl.cl_super with
	   | Some cn -> get_field prog (must_get_class prog cn) fn
	   | None -> None)

let must_get_field (prog : program) (cl : class_decl) (fn : field_name) : field =
  match get_field prog cl fn with
    | None -> Util.fail ("jastUtil.get_field: Could not find field " ^ fn ^ " in class " ^
			   cl.cl_name)
    | Some vd -> vd

(** Get the type of the literal *)
let get_literal_type (lt : literal) : typ =
  match lt with
  | IntLiteral _ -> Jtype.int_type
  | BoolLiteral _ -> Jtype.boolean_type
  | StringLiteral _ -> Jtype.string_type
  | NullLiteral -> Jtype.object_type
  | OtherLiteral s -> Util.fail 
        ("Jtype.get_literal_type: Unknown type of literal " ^ s)

let get_simpval_typ (v : simpval) : typ = 
  match v with      
  | VarVal (LocalVar vd) -> vd.vd_type
  | VarVal (StaticVar { cv_var=vd }) -> vd.vd_type
  | ParamVar vd -> vd.vd_type
  | LiteralVal lit -> get_literal_type lit

(** Printing pieces of Jasthis_val xt abstract syntax tree. *)

let rec print_typ (t : Syntax.typ) = match t with
  | Syntax.TypeName ns -> pr_name ns
  | Syntax.ArrayType t1 -> print_typ t1 ^ "[]"

let print_vd (vd : var_decl) =
  "(" ^ vd.vd_name ^ "::" ^ print_typ vd.vd_type ^ ")"

let print_lval (lv : lval) = match lv with
  | LocalVar vd -> "local var " ^ print_vd vd
  | StaticVar {cv_cl=clname; cv_var=vd} 
    -> "static var in class " ^ clname ^ print_vd vd

let print_lit (lit : literal) = match lit with
  | IntLiteral i -> string_of_int i
  | BoolLiteral b -> string_of_bool b
  | StringLiteral s -> "\"" ^ s ^ "\""
  | NullLiteral -> "null"
  | OtherLiteral s -> s  

let print_simpval (v : simpval) = match v with
  | LiteralVal lit -> print_lit lit
  | VarVal lv -> print_lval lv
  | ParamVar vd -> print_vd vd

(** end of printing *)

let get_simpval_typ_name 
    (v : simpval) : string 
    (* result is class_name or interface_name *) = 
  match (get_simpval_typ v) with
    | Syntax.TypeName [n] -> Syntax.id_string n
    | Syntax.TypeName ns ->
	Util.fail ("Unexpected type '" ^ pr_name ns ^
		    "' A simple named type expected.")
    | Syntax.ArrayType _ -> array_std_class_name

let get_simpval_class (env : program) (v : simpval) : class_decl =
  must_get_class env (get_simpval_typ_name v)

let field_asgn (x : simpval) (fd : field) (y : simpval) =
  mkbasic (FieldAssign(x,fd,y))

let field_asgn_n 
    (env : program)
    (x : simpval) 
    (fn : string) 
    (y : simpval) =
  let cl_x = get_simpval_class env x in
  let fd = must_get_field env cl_x fn in
    field_asgn x fd y



let some_asgn
    (c : class_decl) 
    (locals : var_decl list)
    (vn : var_name)
    (rhs : simpval) : stmt = (* create appropriate assignment *)
  match find_var locals vn with
    | Some vd -> slocal_asgn vd rhs
    | None -> 
	(match find_static_var c vn with
	   | Some vd -> sglobal_asgn c.cl_name vd rhs
	   | None -> 
	       (match find_field c vn with
		  | Some fd ->
		      field_asgn (this_val c.cl_name) fd rhs
		  | None -> 
		      Util.fail ("Uknown assignable variable '" ^ vn ^ 
				  "' in a method of class " ^ c.cl_name)))

(** create appropriate qualified assignment unless 
     this.x.f = y, in which case return None. **)
let qasgn
    (p : program)
    (c : class_decl) 
    (m : method_decl)
    (locals : var_decl list)
    (x : string)
    (f : string)
    (y : simpval) : stmt option = 
  match find_var locals x with
    | Some vd -> Some (field_asgn_n p (VarVal (LocalVar vd)) f y)
    | None ->
	(match find_var m.m_formals x with
	   | Some vd -> Some (field_asgn_n p (ParamVar vd) f y)
	   | None ->
	       (match get_class p x with
		  | Some cl -> 
		      (match find_static_var cl f with
			 | Some vd -> Some (sglobal_asgn x vd y)
			 | None -> Util.fail 
			     ("jastUtil.qasgn: Could not find static variable" ^ x ^ "." ^ f))
		  | None -> None)) (* this.x.f = y *)


let load_stmt
    (x : lval)
    (y : simpval)
    (fd : field) = mkbasic (VarAssign(x,FieldDeref(y,fd)))

let load_stmt_n
    (env : program)
    (x : lval)
    (y : simpval)
    (fn : field_name) =
  let n_y = get_simpval_typ_name y in
  let cl_y = must_get_class env n_y in
  let fd = must_get_field env cl_y fn in
    load_stmt x y fd

let array_asgn
    (a : simpval) 
    (i : simpval) 
    (rhs : simpval) =
  mkbasic (ArrayAssign(a,i,rhs))

let array_load
    (lv : lval)
    (a : simpval) 
    (i : simpval) =
  mkbasic (VarAssign(lv,ArrayAccess(a,i)))

let is_static_call (cl : class_decl) (mn : method_name) =
  let p (m : method_decl) = (m.m_name = mn && m.m_static) in
  List.exists p cl.cl_methods

let mk_stat_proc_call res clname mthname args =
  mkbasic (StatProcCall { 
	     scall_res = res; 
	     scall_class = clname;
	     scall_method = mthname;
	     scall_args = args; })	     

let mk_dyn_proc_call res obj mthname args =
  mkbasic (DynProcCall { 
	     dcall_res = res; 
	     dcall_obj = obj;
	     dcall_method = mthname;
	     dcall_args = args; })

let mk_constructor_call res clname args is_default =
  mkbasic (ConstructorCall {
	     con_res = res;
	     con_class = clname;
	     con_args = args;
	     con_is_default = is_default;
	   })

let mk_newarray (lv : lval) (t : string) (dims : simpval list) = 
  mkbasic (NewArray(lv,t,dims))

let mk_postfix 
    (lv : lval)
    (x : simpval) 
    (op : string) : stmt  = 
  mkbasic (VarAssign(lv,Postfix(x,op)))

let mk_infix (lv : lval) (x : simpval) (op : string) (y : simpval) =
  mkbasic (VarAssign(lv,Infix(x,op,y)))

let mk_prefix (lv : lval) (op : string) (x : simpval) = 
  mkbasic (VarAssign(lv,Prefix(op,x)))

let mk_cast (lv : lval) (t : typ) (x : simpval) = 
  mkbasic (VarAssign(lv,Cast(t,x)))

let mk_instanceOf (lv : lval) (x : simpval) (t : typ) =
  mkbasic (VarAssign(lv,InstanceOf(x,t)))

let field_result_type (fd : field) : typ = fd.f_var.vd_type

let rec find_method (m : method_name) (mls : method_decl list) : method_decl option =
  match mls with
    | [] -> None
    | ml::mls0 -> 
        if ml.m_name=m then Some ml
        else find_method m mls0

let rec get_method (prog : program) (cl : class_decl) (m : method_name) : method_decl option =
  match find_method m cl.cl_methods with
    | Some md -> Some md
    | None ->
	(match cl.cl_super with
	   | Some cn -> get_method prog (must_get_class prog cn) m
	   | None -> None)

let rec find_declared_class_for (m : method_name) (cn : class_name) (prog : program) : class_name =
  let cl = must_get_class prog cn in
  match find_method m cl.cl_methods with
    | Some md -> cl.cl_name
    | None ->
	(match cl.cl_super with
	   | Some cn -> find_declared_class_for m cn prog
	   | None -> Util.fail ("jastUtil.find_declared_class_for: Could not find class for " ^ m))

let is_private_method (cl : class_decl) (mn : method_name) : bool =
  match find_method mn cl.cl_methods with
    | None -> Util.fail ("jastUtil.is_private_method: Could not find method " ^ 
			   cl.cl_name ^ "." ^ mn ^
			   "while searching for .")
    | Some m -> not m.m_public

let has_defined_constructor (clname : string) (prog : program) =
  let cl = must_get_class prog clname in
    get_method prog cl clname != None

let method_result_type (prog : program) (cl : class_decl) (m : method_name) : typ =
  match get_method prog cl m with
    | None -> Util.fail ("Could not find method " ^ m ^ " in class " ^
			  cl.cl_name)
    | Some ml -> ml.m_result

let iget_method (ifc : interface) (m : method_name) : method_decl option =
  find_method m ifc.if_method_specs

let imethod_result_type (ifc : interface) (m : method_name) : typ =
  match iget_method ifc m with
    | None -> Util.fail ("Could not find method " ^ m ^ " in class " ^
			  ifc.if_name)
    | Some ml -> ml.m_result

(** Add a method to a list of methods, ensuring that the name of the
    method is distinct from the existing methods.  This prevents overloading. 
*)
let add_distinct (clname : string) (m : method_decl) (ms : method_decl list) : method_decl list =
  match find_method m.m_name ms with
    | None -> m::ms
    | Some _ -> Util.fail ("Overloaded method " ^ clname ^ "." ^ m.m_name)

let mk_true_val : simpval = LiteralVal (BoolLiteral true);;

let mk_false_val : simpval = LiteralVal (BoolLiteral false);;


open Form;;

(** add a variable to the set of hidden objects of the class *)
let mk_add_hidden (var : var_name) : stmt = 
  mk_aassign 
    (Var Jast.hidden_set_name) 
    (App (Const Cup, [Var Jast.hidden_set_name ;
		       App (Const FiniteSetConst, [Var var])]))

let mk_assert_hidden (e : form) : Ast.command = 
  AstUtil.mk_assert
    (FormUtil.mk_elem (e, Var Jast.hidden_set_name))
    "obj should be hidden"

let mk_assert_not_hidden (e : form) : Ast.command = 
  AstUtil.mk_assert 
    (FormUtil.mk_not (FormUtil.mk_elem (e, Var Jast.hidden_set_name)))
    "obj should not be hidden"

let mk_assume_not_hidden (e : form) : Ast.command = 
  AstUtil.mk_assume 
    (FormUtil.mk_not (FormUtil.mk_elem (e, Var Jast.hidden_set_name)))
    "obj should not be hidden"

let is_lval_static (lv:lval) = match lv with
  | LocalVar _ -> false
  | StaticVar _ -> true

let id_of_lvar (lv:lval) = match lv with
  | LocalVar v_decl -> v_decl.vd_name
  | StaticVar cv_decl -> cv_decl.cv_var.vd_name
  
