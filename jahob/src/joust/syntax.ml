(** Joust abstract syntax. *)

(* Joust: a Java lexer, parser, and pretty-printer written in OCaml
   Copyright (C) 2001  Eric C. Cooper <ecc@cmu.edu>
   Released under the GNU General Public License *)

type ident = { id : string; pos : int }

let ident s n = { id = s; pos = n }

let id_string ident = ident.id

let id_pos ident = ident.pos

let synth_id s = { id = s; pos = -1 }

let star_ident = synth_id "*"

let this_ident = synth_id "this"

let super_ident = synth_id "super"

type name = ident list

type names = name list

type typ =
  | TypeName of name
  | ArrayType of typ

let named_type str = TypeName [synth_id str]

let no_type = TypeName []

let void_type = named_type "void"

type modifier =
  | AnnotationModifier of string
  | Public
  | Protected
  | Private
  | Abstract
  | Static
  | Final
  | StrictFP
  | Transient
  | Volatile
  | Synchronized
  | Native

type modifiers = modifier list

type annotation = string

type var_decl_id =
  | IdentDecl of ident
  | ArrayDecl of var_decl_id

type op = string

type compilation_unit =
  { package : name option;
    imports : names;
    decls : decls;
    comments : Source.comments }

and decls = decl list

and decl =
  | Class of class_decl
  | Interface of interface
  | Field of field
  | Method of method_decl
  | InstanceInit of stmt
  | StaticInit of stmt
  | Constructor of method_decl
  | AnnotationDecl of annotation

and class_decl =
  { cl_mods : modifiers;
    cl_name : ident;
    cl_super : name option;
    cl_impls : names;
    cl_body : decls }

and interface =
  { if_mods : modifiers;
    if_name : ident;
    if_exts : names;
    if_body : decls }

and field =
  { f_var : var;
    f_init : init option }

and method_decl =
  { m_var : var;
    m_formals : vars;
    m_throws : names;
    m_annotation : annotation option;
    m_body : stmt }

and vars = var list

and var =
  { v_mods : modifiers;
    v_type : typ;
    v_name : ident }

and init =
  | ExprInit of expr
  | ArrayInit of init list

and stmt =
  | Block of stmts
  | LocalVar of field
  | LocalClass of class_decl
  | Empty
  | Label of ident * stmt
  | Expr of expr
  | If of expr * stmt * stmt option
  | Switch of expr * (cases * stmts) list
  | While of string option * expr * stmt
  | Do of stmt * expr
  | For of stmts * expr option * stmts * stmt
  | Break of ident option
  | Continue of ident option
  | Return of expr option
  | Throw of expr
  | Sync of expr * stmt
  | Try of stmt * catches * stmt option
  | AnnotationStmt of annotation

and stmts = stmt list

and case =
  | Case of expr
  | Default

and cases = case list

and catches = catch list

and catch = var * stmt

and expr =
  | Literal of string
  | ClassLiteral of typ
  | NewClass of typ * exprs * decls option * annotation option
  | NewQualifiedClass of expr * ident * exprs * decls option
  | NewArray of typ * exprs * int * init option * annotation option
  | Dot of expr * ident
  | Call of expr * exprs
  | ArrayAccess of expr * expr
  | Postfix of expr * op
  | Prefix of op * expr
  | Cast of typ * expr
  | Infix of expr * op * expr
  | InstanceOf of expr * typ
  | Conditional of expr * expr * expr
  | Assignment of expr * op * expr
  | Name of name

and exprs = expr list

type mdeclarator = var_decl_id * vars

type var_decls = (var_decl_id * init option) list

let add_comments comp =
  { comp with comments = Source.comments () }

let compilation_unit pkg ims dcls =
  { package = pkg; imports = ims; decls = dcls; comments = [] }

let class_decl mods name super ifs body =
  { cl_mods = mods; cl_name = name; cl_super = super;
    cl_impls = ifs; cl_body = body }

let method_decl hdr body =
  { hdr with m_body = body }

let interface_decl mods name extends body =
  { if_mods = mods; if_name = name; if_exts = extends; if_body = body }

(* Move array dimensions from variable name to type. *)

let rec canon_var mods t v =
  match v with
  | IdentDecl str -> { v_mods = mods; v_type = t; v_name = str }
  | ArrayDecl v' -> canon_var mods (ArrayType t) v'

let method_header mods mtype (v, formals) throws annotation =
  { m_var = canon_var mods mtype v; m_formals = formals;
    m_throws = throws; m_annotation = annotation; m_body = Empty }

(* Return a list of field declarations in canonical form. *)

let decls f mods vtype vars =
  let dcl (v, init) =
    f { f_var = canon_var mods vtype v; f_init = init }
  in
  List.map dcl vars

let field_decls = decls (fun x -> Field x)

let var_decls = decls (fun x -> LocalVar x)

let formal_decl mods t v = canon_var mods t v

let constructor mods (id, formals) throws annotation body =
  let var = { v_mods = mods; v_type = no_type; v_name = id } in
  Constructor { m_var = var; m_formals = formals; m_throws = throws;
                m_annotation = annotation;
		m_body = body }

let constructor_invocation name args =
  Expr (Call (Name name, args))

let expr_super_invocation expr args =
  Expr (Call (Dot (expr, super_ident), args))

(* Convert an expression, which must be a name, into a named type. *)

let type_name exp =
  match exp with
  | Name name -> TypeName name
  | _ -> raise Parsing.Parse_error

(* Find the position of a syntactic structure, or -1 if undefined. *)

let opt_id_pos opt =
  match opt with
  | Some id -> id_pos id
  | None -> -1

let var_pos var = id_pos var.v_name

let rec type_pos t =
  match t with
  | TypeName name -> id_pos (List.hd name)
  | ArrayType t' -> type_pos t'

let rec stmt_pos stmt =
  match stmt with
  | Block [] -> -1
  | Block stmts -> stmts_pos stmts
  | LocalVar fld -> var_pos fld.f_var
  | LocalClass c -> id_pos c.cl_name
  | Empty -> -1
  | Label (lbl, _) -> id_pos lbl
  | Expr e -> expr_pos e
  | If (e, s1, opt) ->
      let n = expr_pos e in
      if n <> -1 then n
      else
	let n = stmt_pos s1 in
	if n <> -1 then n
	else
	  (match opt with
	  | Some s2 -> stmt_pos s2
	  | None -> -1)
  | Switch (e, sw) ->
      let n = expr_pos e in
      if n <> -1 then n
      else switch_pos sw
  | While (_, e, st) ->
      let n = expr_pos e in
      if n <> -1 then n
      else stmt_pos st
  | Do (st, e) ->
      let n = stmt_pos st in
      if n <> -1 then n
      else expr_pos e
  | For (init, test, update, st) ->
      let n = stmts_pos init in
      if n <> -1 then n
      else
	let n = (match test with Some e -> expr_pos e | None -> -1) in
	if n <> -1 then n
	else stmts_pos (update @ [st])
  | Break opt -> opt_id_pos opt
  | Continue opt -> opt_id_pos opt
  | Return opt ->
      (match opt with Some e -> expr_pos e | None -> -1)
  | Throw e -> expr_pos e
  | Sync (e, st) ->
      let n = expr_pos e in
      if n <> -1 then n
      else stmt_pos st
  | Try (st, catches, Some f) ->
      let n = stmt_pos st in
      if n <> -1 then n
      else
	let n = catches_pos catches in
	if n <> -1 then n
	else stmt_pos f
  | Try (st, catches, None) ->
      let n = stmt_pos st in
      if n <> -1 then n
      else catches_pos catches
  | AnnotationStmt _ -> -1

and stmts_pos list =
  match list with
  | s :: rest ->
      let n = stmt_pos s in
      if n <> -1 then n
      else stmts_pos rest
  | [] -> -1

and expr_stmt_pos e s =
  let n = expr_pos e in
  if n <> -1 then n
  else stmt_pos s

and switch_pos list =
  match list with
  | (cases, stmts) :: rest ->
      let n = cases_pos cases in
      if n <> -1 then n
      else
	let n = stmts_pos stmts in
	if n <> -1 then n
	else switch_pos rest
  | [] -> -1

and cases_pos list =
  match list with
  | Case e :: rest ->
      let n = expr_pos e in
      if n <> -1 then n
      else cases_pos rest
  | Default :: rest -> cases_pos rest
  | [] -> -1

and expr_pos e =
  match e with
  | Literal _ -> -1
  | ClassLiteral t -> type_pos t
  | NewClass (t, _, _, _) -> type_pos t
  | NewQualifiedClass (e, id, _, _) ->
      let n = expr_pos e in
      if n <> -1 then n
      else id_pos id
  | NewArray (t, dims, _, opt, _) ->
      let n = type_pos t in
      if n <> -1 then n
      else
	let n = exprs_pos dims in
	if n <> -1 then n
	else
	  (match opt with
	  | Some init -> init_pos init
	  | None -> -1)
  | Dot (e, id) ->
      let n = expr_pos e in
      if n <> -1 then n
      else id_pos id
  | Call (e, args) ->
      let n = expr_pos e in
      if n <> -1 then n
      else exprs_pos args
  | ArrayAccess (e1, e2) ->
      let n = expr_pos e1 in
      if n <> -1 then n
      else expr_pos e2
  | Postfix (e, _) -> expr_pos e
  | Prefix (_, e) -> expr_pos e
  | Cast (t, e) ->
      let n = type_pos t in
      if n <> -1 then n
      else expr_pos e
  | Infix (e1, op, e2) ->
      let n = expr_pos e1 in
      if n <> -1 then n
      else expr_pos e2
  | InstanceOf (e, t) ->
      let n = expr_pos e in
      if n <> -1 then n
      else type_pos t
  | Conditional (e1, e2, e3) ->
      let n = expr_pos e1 in
      if n <> -1 then n
      else
	let n = expr_pos e2 in
	if n <> -1 then n
	else expr_pos e3
  | Assignment (e1, _, e2) ->
      let n = expr_pos e1 in
      if n <> -1 then n
      else expr_pos e2
  | Name name ->
      id_pos (List.hd name)

and exprs_pos list =
  match list with
  | e :: rest ->
      let n = expr_pos e in
      if n <> -1 then n
      else exprs_pos rest
  | [] -> -1

and init_pos init =
  match init with
  | ExprInit e -> expr_pos e
  | ArrayInit inits -> inits_pos inits

and inits_pos list =
  match list with
  | init :: rest ->
      let n = init_pos init in
      if n <> -1 then n
      else inits_pos rest
  | [] -> -1

and catches_pos list =
  match list with
  | (var, stmt) :: rest ->
      let n = var_pos var in
      if n <> -1 then n
      else
	let n = stmt_pos stmt in
	if n <> -1 then n
	else catches_pos rest
  | [] -> -1

