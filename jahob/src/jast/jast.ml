(** Abstract Syntax Tree for a Java subset: tree definitions and some utility functions.
   Features:
   - expressions and statements are flat (like three-address code)
   - simple control flow
   - no exceptions
*)

(** Types used from Joust *)

type ident = Syntax.ident
type typ = Syntax.typ
type op = Syntax.op

(** Type synonyms that clarify the intended purpose. *)

(** Description of a set of modified locations. *)
type mod_item = Form.form

(** Name of a variable. *)
type var_name = string

(** Name of a field. *)
type field_name = var_name

(** Name of a method. *)
type method_name = string

(** Name of a class. *)
type class_name = string

(** Name of an inteface. *)
type if_name = string

(** Name of the hidden set of objects (global variable of each class) *)
let hidden_set_name = "hidden"

(** Literal constants, somewhat parsed. *)
type literal =
  | IntLiteral of int (** integer literal *)
  | BoolLiteral of bool (** boolean literal *)
  | StringLiteral of string (** string in quotes *)
  | NullLiteral (** 'null' reference *)
  | OtherLiteral of string (** other literals, e.g. float *)

(** Variable declarations in various parts of code. *)
type var_decl =
  { vd_name : var_name; (** variable name *)
    vd_type : typ; (** variable type *)
    vd_init : literal option; (** initial value *)
    vd_readonly	: bool (** whether the variable is a public readonly variable *)
  }

(** Abstract variable declaration. *)
type avar_decl = Specs.abstract_var_decl

(** Local variable. *)
type local_var = var_decl

(** Static (class) variable. *)
type class_var = 
    { cv_cl  : class_name; (** class where it is declared *)
      cv_var : var_decl; (** variable declaration *) }

(** Field declaration. *)
type field =
    { f_cl  : class_name; (** class where the field is declared *)
      f_var : var_decl (** variable declaration *) }

(** A simple assignable variable (left-value).
    Assigning to {!Jast.lval} requires no precondition, unlike
    assigning to a field. *)
type lval = 
  | LocalVar of local_var   (** local variable *)
  | StaticVar of class_var  (** class variable *)

(** A value, which requires no further evaluation. *)
type simpval = 
  | LiteralVal of literal (** literal constant *)
  | VarVal of lval        (** reference to a simple assignable variable *)
  | ParamVar of local_var (** reference to a parameter (not assignable) *)

let this_id = "this"

(** The variable representing the receiver parameter "this". *)
let this_var (clname : string) : var_decl = { 
  vd_name=this_id;
  vd_type = Syntax.TypeName [Syntax.synth_id clname];
  vd_init = None;
  vd_readonly = false}

(** The value for {!this_var}. *)
let this_val (clname : string) : simpval = ParamVar (this_var clname)

(** Check if the variable is "this" parameter.  
    Uses only the name for comparison. *)
let is_this_val (sv : simpval) = match sv with
| ParamVar vd when vd.vd_name = this_id -> true
| _ -> false

(** Side-effect free expressions
   involving partial operations, like FieldDeref.
   Hence, they may imply some preconditions, but
   will not modify the state. *)
type expr =
  | Val of simpval                      (** simple value, no evaluation needed *)
  | Cast of typ * simpval               (** cast: (T)y *)
  | InstanceOf of simpval * typ         (** x instanceof t *)
  | FieldDeref of simpval * field       (** x.f *)
  | ArrayAccess of simpval * simpval    (** x[i] *)
  | Postfix of simpval * op             (** x op *)
  | Prefix of op * simpval              (** op x *)
  | Infix of simpval * op * simpval     (** x op y *)
     
(** Procedure call with dynamic dispatch. *)
type dyn_proc_call = {
  dcall_res    : lval option; (** variable storing call result *)
  dcall_obj    : simpval; (** receiver object *)
  dcall_method : method_name; (** callee method *)
  dcall_args   : simpval list; (** call arguments *)
}

(** Statically resolved procedure call.  *)
type stat_proc_call = {
  scall_res    : lval option; (** variable storing call result *)
  scall_class  : class_name; (** class where the method is declared *)
  scall_method : method_name; (** method name *)
  scall_args   : simpval list; (** call arguments *)
}

(** Constructor invocation. *)
type constructor_call = {
  con_res    : lval option; (** variable storing call result *)
  con_class  : class_name; (** class of object constructed *)
  con_args   : simpval list; (** constructor arguments *)
  con_is_default : bool; (** whether a call to default constructor *)
}

(** Basic statement, invoke one action. *)
type basic_stmt =
  | Empty                                      (** nop *)
  | VarAssign of lval * expr                   (** v = e *)
  | FieldAssign of simpval * field * simpval   (** x.f = e *)
  | ArrayAssign of simpval * simpval * simpval (** x[i] = e *)
  | ConstructorCall of constructor_call        (** constructor call *)
  | NewArray of lval * string * simpval list   (** x = new T[n_1,...,n_k] *)
  | DynProcCall of dyn_proc_call               (** method call *)
  | StatProcCall of stat_proc_call             (** static method call *)
  | Havoc of mod_item list                     (** non-deterministic asgn *)
  | Assert of string option * Form.form        (** assert statement *)
  | NoteThat of string option * Form.form      (** assert followed by assume *)
  | Assume of string option * Form.form        (** assume statement *)
  | AbstAssign of Form.form * Form.form        (** abstract assignment *)
  | Split of string option * Form.form         (** split statement *)
  | AbstOperation of Specs.abstract_operation  (** abstract operation *)

let release_op_name = "release"
let incorporate_op_name = "incorporate"
let track_specvar_op_name = "track"

type cfg_node = {  
    cfg_pos : int;      (** position in code; currently not maintained *)
    cfg_name : string;  (** assign identity to statements (for later control-flow graphs) *)
  }

(** General statement constructed by applying control-flow operators to basic statements. *)
type stmt =
  | Basic of basic_stmt * cfg_node   (** basic statement *)
  | Block of stmt list               (** statement sequence, sequential composition. *)
  | If of simpval * stmt * stmt      (** If statement. *)
  | Loop of Form.form option * stmt * simpval * stmt    
      (** loop with loop invariant and exit in the middle *)
  | Return of simpval option         (** return from a method *)

(** Definition of an abstract variable. *)
type var_def = Specs.var_def


(** Method declaration. *)
type method_decl = { 
  m_name    : method_name; (** method name *)
  
  m_public  : bool; (** is the method public *)
  m_static  : bool; (** is the method static *)
  m_constructor : bool; (** is the method constructor *)
  
  m_result  : typ; (** method return type *)
  m_formals : var_decl list; (** formal parameters *)
  m_pre      : Form.form option; (** requires clause *)
  m_modifies : mod_item list option; (** modifies clause *)
  m_post     : Form.form option; (** ensures clause *)
  m_locals : var_decl list; (** local variables *)
  m_vardefs : var_def list; (** definitions for specvars *)
  m_speclocals : avar_decl list; (** local specification variables *)
  m_body   : stmt; (** method body *)
}

(** Class definition. *)
type class_decl = { 
  cl_name   : class_name; (** class name *)
  cl_super  : class_name option; (** superclass name *)
  cl_owner  : class_name option; (** owner of this class *)
  cl_impls  : if_name list; (** interfaces that the class implements *)
  
  cl_lemmas : Specs.lemma_desc list; (** list of lemmas declared in current class *)

  cl_claimed_fields : (var_decl * class_name) list; (** field of this class claimed by other classes *)
  cl_public_fields    : var_decl list; (** public fields *)
  cl_private_fields   : var_decl list; (** private fields *)
  cl_public_globals   : var_decl list; (** public static fields *)
  cl_private_globals  : var_decl list; (** private static fields *)
  cl_abst_fields  : avar_decl list; (** abstract fields *)
  cl_abst_globals : avar_decl list; (** abstract globals *)
  
  cl_vardefs   : var_def list; (** private definitions of abstract variables *)
  cl_pubvardefs : var_def list; (** private definitions of abstract variables *)
  cl_constdefs : var_def list; (** definitions of constants *)
  cl_pubconstdefs : var_def list; (** definitions of public constants *)
  cl_invariants : Specs.invariant_desc list; (** class invariants *)
  cl_methods   : method_decl list; (** methods *)
}

(** Interface definition. *)
type interface = { 
  if_name : if_name; (** interface name *)
  if_exts : if_name list;  (** interfaces that this interface extends *)
  if_abst_fields  : avar_decl list; (** specification interface field variables *)
  if_abst_globals : avar_decl list; (** specification interface static variables *)
  if_constants : var_decl list; (** constants *)
  if_vardefs : var_def list; (** shorthand definitions *)
  if_constdefs : var_def list; (** state-free shorthand definitions *)
  if_invariants : Specs.invariant_desc list; (** invariants on interface variables *)
  if_method_specs : method_decl list; (** interface method specifications *)
}

type program = 
  { classes    : class_decl list;
    interfaces : interface list; }

(* ------------------------------------------------------------ *)
(** Predefined classes in Jast *)
(* ------------------------------------------------------------ *)

let owner_std_field = { 
  vd_name = "owner"; 
  vd_type = Jtype.object_type;
  vd_init = None;
  vd_readonly = false;
}
let alloc_initial_value = FormUtil.mk_singleton FormUtil.mk_null
let alloc_std_var = { 
  Specs.avd_name = "alloc";
  Specs.avd_type = FormUtil.mk_set_type FormUtil.mk_object_type;
  Specs.avd_init = Some alloc_initial_value;
  Specs.avd_public = true;
  Specs.avd_field = false;
  Specs.avd_ghost = true;
}

let objectName = "Object"
let object_std_class = {
  cl_name = objectName;
  cl_super = None;
  cl_owner = None;
  cl_impls = [];
  cl_lemmas = [];
  cl_claimed_fields = [];
  cl_public_fields = if !CmdLine.tokens then [owner_std_field] else [];
  cl_private_fields = [];
  cl_public_globals = [];
  cl_private_globals = [];
  cl_abst_fields = [];
  cl_abst_globals = [alloc_std_var];
  cl_vardefs = [];
  cl_pubvardefs = [];
  cl_constdefs = [];
  cl_pubconstdefs = [];
  cl_invariants = [];
  cl_methods = [];
}
let length_std_field = {
  vd_name = FormUtil.shortArrayLengthId;
  vd_type = Jtype.int_type;
  vd_init = None;
  vd_readonly = true
}
let arrayState_std_field = { 
  Specs.avd_name = FormUtil.shortArrayStateId;
  Specs.avd_type = FormUtil.mk_array FormUtil.mk_object_type;
  Specs.avd_init = None;
  Specs.avd_public = true;
  Specs.avd_field = true;
  Specs.avd_ghost = true;
}
let array_std_class_name = "Array"
let array_std_class = {
  object_std_class with
    cl_name = array_std_class_name;
    cl_public_fields = [length_std_field];
    cl_abst_fields = [arrayState_std_field];
    cl_abst_globals = [] (* remove alloc *)
}

let standard_classes = [object_std_class; array_std_class]
