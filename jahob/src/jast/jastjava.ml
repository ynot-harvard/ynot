(** Convert from {!Jast} abstract syntax tree 
   back to Joust ({!Syntax}) abstract syntax tree. *)

open Jast

let str2id = Syntax.synth_id
let str2name s = [Syntax.synth_id s]
let nameof x = Syntax.Name [x]
let asgn lhs rhs = Syntax.Expr (Syntax.Assignment(lhs, "=", rhs))
let true_expr = Syntax.Literal "true"

let (choose : ident) = str2id "choose"

let c_vd (vd : var_decl) : Syntax.expr = 
  Syntax.Name [Syntax.synth_id vd.vd_name]

let c_lval (lv : lval) : Syntax.expr = match lv with
  | LocalVar vd -> c_vd vd
  | StaticVar { cv_cl=cl; cv_var=vd } ->
      Syntax.Name [str2id cl; str2id vd.vd_name]

let c_literal (lit : literal) : string = 
  match lit with
  | IntLiteral s -> string_of_int s
  | BoolLiteral b -> string_of_bool b
  | StringLiteral s -> "\"" ^ s ^ "\""
  | NullLiteral -> "null"
  | OtherLiteral s -> s

let c_simpval (v : simpval) : Syntax.expr = match v with
  | LiteralVal lit -> Syntax.Literal (c_literal lit)
  | VarVal lv -> c_lval lv
  | ParamVar vd -> c_vd vd

let c_field (f : field) : Syntax.ident = str2id f.f_var.vd_name

let c_expr (e : expr) : Syntax.expr = match e with
  | Val v -> c_simpval v
  | Cast(t,v) -> Syntax.Cast(t,c_simpval v)
  | InstanceOf (x,t) -> Syntax.InstanceOf(c_simpval x, t)
  | FieldDeref (x,f) -> Syntax.Dot(c_simpval x, c_field f)
  | ArrayAccess (x,i) -> Syntax.ArrayAccess(c_simpval x, c_simpval i)
  | Postfix (x,op) -> Syntax.Postfix(c_simpval x, op)
  | Prefix (op,x) -> Syntax.Prefix(op,c_simpval x)
  | Infix (x,op,y) -> Syntax.Infix(c_simpval x,op,c_simpval y)

let block (sts0 : Syntax.stmt list) : Syntax.stmt =
  let rec collect sts acc = match sts with
    | [] -> acc
    | (Syntax.Block nsts)::sts1 -> collect sts1 (collect nsts acc)
    | st::sts1 -> collect sts1 (st::acc) in
  Syntax.Block (List.rev (collect sts0 []))

let c_basic_stmt (s : basic_stmt) : Syntax.stmt = match s with
  | Empty -> Syntax.Empty
  | VarAssign(x,e) -> asgn (c_lval x) (c_expr e)
  | FieldAssign(x,f,y) -> 
      asgn (Syntax.Dot(c_simpval x,c_field f)) (c_simpval y)
  | ArrayAssign(x,i,y) -> 
      asgn (Syntax.ArrayAccess(c_simpval x, c_simpval i)) (c_simpval y)
  (*| New(x,t) -> asgn (c_lval x) (Syntax.NewClass(t,[],None))*)
  | ConstructorCall {
      con_res = res;
      con_class = cn;
      con_args = args; 
    } -> let rhs = Syntax.NewClass(Syntax.TypeName([str2id cn]),
                                   List.map c_simpval args,None, None) in
      (* in the above line, the second None correspond to the hidden statement *)
      (match res with
         | None -> Syntax.Expr rhs
         | Some lv -> asgn (c_lval lv) rhs)
  | NewArray(x,t,dims) -> 
      let tt = Syntax.TypeName [str2id t] in
        asgn (c_lval x)
          (Syntax.NewArray(tt,List.map c_simpval dims,List.length dims - 1,None,None))
  | DynProcCall {dcall_res = res;
                 dcall_obj = obj;
                 dcall_method = mth;
                 dcall_args = args} ->
      let rhs = Syntax.Call(Syntax.Dot(c_simpval obj, 
                                       Syntax.synth_id mth), 
                            List.map c_simpval args) in
        (match res with
          | None -> Syntax.Expr rhs
          | Some lv -> asgn (c_lval lv) rhs)

  | StatProcCall {scall_res = res;
                  scall_class = cn;
                  scall_method = mth;
                  scall_args = args} ->
      let rhs = Syntax.Call(Syntax.Dot(nameof (str2id cn), 
                                       Syntax.synth_id mth),
                            List.map c_simpval args) in
        (match res with
          | None -> Syntax.Expr rhs
          | Some lv -> asgn (c_lval lv) rhs)
  | Havoc fs -> Syntax.AnnotationStmt ("assert " ^ 
                                               String.concat ", " (List.map PrintForm.quoted_form fs) ^ ";")
  | Assert(omsg,f) -> Syntax.AnnotationStmt ("assert " ^ 
                                               PrintForm.quoted_form f ^ ";")
  | NoteThat(omsg,f) -> Syntax.AnnotationStmt ("noteThat " ^ 
                                               PrintForm.quoted_form f ^ ";")
  | Assume(omsg,f) -> Syntax.AnnotationStmt ("assume " ^ 
                                               PrintForm.quoted_form f ^ ";")
  | Split(omsg,f) -> Syntax.AnnotationStmt ("split " ^ 
                                              PrintForm.quoted_form f ^ ";")
(*  | AbstAssign(id,f) -> Syntax.AnnotationStmt (c_lval id ^ " := " ^ 
                                              PrintForm.quoted_form f ^ ";")  *)
  | AbstAssign(id,f) ->  Syntax.AnnotationStmt (PrintForm.string_of_form id ^ " := " ^ PrintForm.quoted_form f);

  | AbstOperation ao -> Syntax.AnnotationStmt (PrintSpec.p_aoperation ao ^ ";")

let c_loop_inv (oinv : Form.form option) : string option =
  match oinv with
    | None -> None 
    | Some f -> 
        Some ("inv " ^ PrintForm.quoted_form f)

let rec c_stmt (s : stmt) : Syntax.stmt = match s with
  | Basic(bs,_) -> c_basic_stmt bs
  | Block ss -> block (List.map c_stmt ss)
  | If(c,s1,s2) -> Syntax.If(c_simpval c, c_stmt s1, 
                             if s2=Block [] then 
                               None 
                             else Some (c_stmt s2))
  | Loop(oinv,s1,c,s2) ->
      Syntax.While(
        c_loop_inv oinv,
        true_expr,
        block 
          [c_stmt s1;
           Syntax.If(Syntax.Prefix("!",c_simpval c), Syntax.Break None, None);
           c_stmt s2])

  | Return ox ->
      Syntax.Return 
        (match ox with Some x -> 
           Some (c_simpval x)
	   | None -> None)
        
let mkvar (mods : Syntax.modifier list) (t : Syntax.typ) (n : string) : Syntax.var = 
  {Syntax.v_mods = mods; Syntax.v_type = t; Syntax.v_name=str2id n}

let pub_mod b = if b then [Syntax.Public] else [Syntax.Private]

let c_claimed_field ((vd,s) : var_decl * string) = 
  let s1 = "claimedby " ^ s in
    { Syntax.f_var = mkvar [Syntax.Public;
                            Syntax.AnnotationModifier s1] vd.vd_type vd.vd_name;
      Syntax.f_init = None}

let add_readonly vd = 
  if vd.vd_readonly then 
    [Syntax.AnnotationModifier "readonly"] 
  else []

let c_pub_field (vd : var_decl) = 
  { Syntax.f_var = mkvar (Syntax.Public::add_readonly vd) vd.vd_type vd.vd_name;
    Syntax.f_init = None }

let c_priv_field (vd : var_decl) = 
  { Syntax.f_var = mkvar [Syntax.Private] vd.vd_type vd.vd_name;
    Syntax.f_init = None }

let c_pub_global (vd : var_decl) = 
  { Syntax.f_var = mkvar (Syntax.Public::Syntax.Static::add_readonly vd) vd.vd_type vd.vd_name;
    Syntax.f_init = None }

let c_priv_global (vd : var_decl) = 
  { Syntax.f_var = mkvar [Syntax.Private; Syntax.Static] vd.vd_type vd.vd_name;
    Syntax.f_init = None }

let c_inv : Specs.invariant_desc -> Syntax.annotation = PrintSpec.p_invariant

(*  let publicness = if i.Specs.inv_public then "public " else "private " in
  let ensured = if i.Specs.inv_ensured then "ensured " else "" in
  let name = if i.Specs.inv_name <> "" then "\"" ^ i.Specs.inv_name ^ "\" " else "" in
  
  Printf.sprintf "%s%sinvariant %s%s" publicness ensured name (PrintForm.quoted_form i.Specs.inv_form)
*)

let mk_inv inv = Syntax.AnnotationDecl (c_inv inv)

let varof (vd : var_decl) : Syntax.var =
  { Syntax.v_mods = []; 
    Syntax.v_type = vd.vd_type;
    Syntax.v_name = str2id vd.vd_name }

let mk_local (vd : var_decl) : Syntax.stmt =
  Syntax.LocalVar { Syntax.f_var = varof vd; Syntax.f_init = None }

let mk_speclocal (avd : avar_decl) : Syntax.stmt = 
  Syntax.AnnotationStmt (PrintSpec.p_specvar avd)

let annot1 f xs = match xs with
  | [] -> []
  | _ -> [Syntax.AnnotationDecl (f xs)]
let annot is = List.map (fun x -> Syntax.AnnotationDecl x) is 
let oannot prf fo = match fo with
  | None -> []
  | Some f -> [Syntax.AnnotationDecl (prf f)]

let mk_proc_vardef (vds : Specs.var_def list) : Syntax.stmt list =
  match vds with
    | [] -> []
    | _ -> [Syntax.AnnotationStmt (PrintSpec.p_vardefs vds)]

let c_method (m : method_decl) = 
  { Syntax.m_var = mkvar (pub_mod m.m_public) m.m_result m.m_name;
    Syntax.m_formals = List.map varof m.m_formals;
    Syntax.m_throws = [];
    Syntax.m_annotation = PrintSpec.print_contract m;
    Syntax.m_body =
      block
        ((List.map mk_local m.m_locals) @ 
	   (List.map mk_speclocal m.m_speclocals) @
	   mk_proc_vardef m.m_vardefs @
	   [c_stmt m.m_body])
  }

let fdecl fs = List.map (fun x -> Syntax.Field x) fs 
let constrs cs = List.map (fun x -> Syntax.Constructor x) cs 
let methods ms = List.map (fun x -> Syntax.Method x) ms 

let c_class (cl : class_decl) : Syntax.decl =
  Syntax.Class { 
    Syntax.cl_mods = [];
    Syntax.cl_name = str2id cl.cl_name;
    Syntax.cl_super = (match cl.cl_super with None -> None | Some str -> Some [str2id str]);
    Syntax.cl_impls = List.map str2name cl.cl_impls;
    Syntax.cl_body = 
      fdecl (List.map c_pub_field cl.cl_public_fields) @
        fdecl (List.map c_claimed_field cl.cl_claimed_fields) @
        fdecl (List.map c_priv_field cl.cl_private_fields) @
        fdecl (List.map c_pub_global cl.cl_public_globals) @
        fdecl (List.map c_priv_global cl.cl_private_globals) @
        annot (List.map PrintSpec.p_abst_field cl.cl_abst_fields) @
        annot (List.map PrintSpec.p_abst_global cl.cl_abst_globals) @
        annot1 PrintSpec.p_vardefs cl.cl_vardefs @
        annot1 PrintSpec.p_pubvardefs cl.cl_pubvardefs @
        annot1 PrintSpec.p_constdefs cl.cl_constdefs @
        annot1 PrintSpec.p_pubconstdefs cl.cl_pubconstdefs @
(*
        annot (List.map PrintSpec.p_hide_objs cl.cl_hide_objs) @
        annot (List.map PrintSpec.p_claim_locs cl.cl_claim_locs) @
*)
        List.map mk_inv cl.cl_invariants @
        methods (List.map c_method cl.cl_methods)
  }

let c_interface (ifc : interface) : Syntax.decl = 
  Syntax.Interface { Syntax.if_mods = [];
                     Syntax.if_name = str2id ifc.if_name;
                     Syntax.if_exts = List.map str2name ifc.if_exts;
                     Syntax.if_body =
                       annot (List.map PrintSpec.p_abst_field ifc.if_abst_fields) @
                       annot (List.map PrintSpec.p_abst_global ifc.if_abst_globals) @
                       annot1 PrintSpec.p_vardefs ifc.if_vardefs @
                       annot1 PrintSpec.p_constdefs ifc.if_constdefs @
                       List.map mk_inv (List.filter (fun i -> i.Specs.inv_public) ifc.if_invariants) @
                       methods (List.map c_method ifc.if_method_specs) }

let jast2joust (p : program) : Syntax.compilation_unit =
  { Syntax.package = None;
    Syntax.imports = [];
    Syntax.decls = (List.map c_class p.classes) @ 
                   (List.map c_interface p.interfaces);
    Syntax.comments = [] }
