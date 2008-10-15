(** Joust abstract syntax. *)

(* Joust: a Java lexer, parser, and pretty-printer written in OCaml
   Copyright (C) 2001  Eric C. Cooper <ecc@cmu.edu>
   Released under the GNU General Public License *)

type ident

val ident : string -> int -> ident

val synth_id : string -> ident

val id_string : ident -> string

val star_ident : ident

val this_ident : ident

val super_ident : ident

type name = ident list

type names = name list

type typ =
  | TypeName of name
  | ArrayType of typ

val no_type : typ

val void_type : typ

val named_type : string -> typ

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

type annotation = string

type modifiers = modifier list

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

val add_comments : compilation_unit -> compilation_unit

val compilation_unit : name option -> names -> decls -> compilation_unit

val class_decl : modifiers -> ident -> name option -> names -> decls -> class_decl

val method_decl : method_decl -> stmt -> method_decl

val interface_decl : modifiers -> ident -> names -> decls -> interface

val method_header : modifiers -> typ -> mdeclarator -> names -> 
  annotation option -> method_decl

val field_decls : modifiers -> typ -> var_decls -> decls

val var_decls : modifiers -> typ -> var_decls -> stmts

val formal_decl : modifiers -> typ -> var_decl_id -> var

val constructor : modifiers -> (ident * vars) -> names -> annotation option 
  -> stmt -> decl

val constructor_invocation : name -> exprs -> stmt

val expr_super_invocation : expr -> exprs -> stmt

val type_name : expr -> typ

val id_pos : ident -> int

val stmt_pos : stmt -> int
