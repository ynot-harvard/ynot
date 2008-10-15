(**

   Program is a set of specification and implementation modules, along with
   a set of conformance obligations (mappings). 
*)

open Form
open FormUtil

(** Name of the the special variable used in ensures clause to
    denote the returned value of the procedure. *)
let result_var = "result"

(** Formula corresponding to result variable. *)
let result_f = Var result_var

(** Prefix for variables denoting currently allocated objects. *)
let alloc_objs_var = "alloc"

(* Create a variable for objects of given type name. *)
let obj_var (t : string) : string = t

(** Create a variable for allocated objects of given type name. *)
let all_alloc_objs = Jast.objectName ^ "." ^ alloc_objs_var
let all_alloc_objsf = mk_var all_alloc_objs

(** Ownership variables *)

let owner_field_name = "Object.owner"
let owner_field = mk_var owner_field_name
let old_owner_field = mk_var (oldname owner_field_name)
let token_name = "token"
let no_owner_name = "NoOwner"

(** Variable denoting receiver parameter *)
let this_id = "this"
let (this_tv : typedIdent) = (this_id,mk_object_type)

(** Message used in annotations. *)
type msg = string

(** Identification of the current program point. *)
type program_point = {
  pp_file : string;
  pp_line : int;
  pp_class : string;
  pp_proc : string;
  pp_id : int;
}

(** Procedure contract. *)
type contract = {
  mutable co_pre  : form;  (** precondition (requires clause) *)
  mutable co_mod  : form list option; (** modifies clause *)
  mutable co_post : form; (** postcondition (ensures clause) *)
  mutable co_resolved : bool; (** have formulas been resolved? *)
}

(** Concrete or abstract variable. *)
type var_decl = {
  vd_name : ident; (** variable name *)
  vd_type : typeForm; (** variable type *)
  vd_init : form option; (** initial value, if any *)
  vd_abstract : bool; (** whether the variable is abstract *)
  vd_ghost : bool; (** whether the variable is ghost *)
  mutable vd_def : form option; (** definition of an abstract variable *)
  vd_field : bool; (** whether the variable was declared as a field, 
		       used 1) to add implicit 'this' 
		            2) extract field names for background axioms etc. *)
  vd_owner : ident option; (** name of the module that claims this variable, if any; 
			       emulates Hob 'formats' *)
}

(** Procedure header. *)
and proc_header = {
  p_name     : ident; (** procedure name *)
  p_formals  : var_decl list; (** formal parameter list *)
  p_restype  : typeForm; (** resulting return type *)
  p_contract : contract; (** procedure contract *)
  p_public : bool;
}

(** Commands *)

(** Assignment, x := e. *)
and assign_command = {
  mutable assign_lhs : ident;
  mutable assign_tlhs : typedIdent;
  mutable assign_rhs : form;
}

(** Allocation, x := new T(), but no constructor called. *)
and alloc_command = {
  alloc_lhs : ident;
  mutable alloc_tlhs : typedIdent;
  alloc_type : ident;
}

(** k-dimensional array allocation, x := new T[n1,...,nk]. *)
and array_alloc_command = {
  arr_alloc_lhs : ident;
  mutable arr_alloc_tlhs : typedIdent;
  arr_alloc_type : ident;
  mutable arr_alloc_dims : form list;
}

(** Statements assert, assume, or split *)
and annot_form_command = {
  mutable annot_form : form;
  annot_msg : msg;
}

(** Non-deterministically change the value of locations. *)
and havoc_command = {
  mutable havoc_regions : form list
}

(** Procedure call, x := M.p(arg1,...,arg_m) *)
and proc_call = {
  mutable callee_res  : ident option;  (** x *)
  callee_module : ident; (** M *)
  callee_name : ident; (** p *)
  mutable callee_hdr : proc_header option; (** header of p *)
  callee_args : form list; (** arg1,...,arg_m *)
  call_is_external : bool; (** whether to check class invariants *)
}

(** Atomic commands. *)
and basic_command =
  | Skip
  | VarAssign of assign_command
  | Alloc of alloc_command
  | ArrayAlloc of array_alloc_command
  | Assert of annot_form_command
  | NoteThat of annot_form_command
  | Assume of annot_form_command
  | Split of annot_form_command
  | Havoc of havoc_command
  | ProcCall of proc_call
  | Hint of hint

and hint =
  | TrackSpecvar of track_specvar

and track_specvar = {
  mutable track_var : ident;
}

(** Cell storing a basic command and extra information associated with it. *)
and basic_cell = {
  bcell_cmd : basic_command; (** the command itself *)
  bcell_point : program_point; (** program point identification *)
  mutable bcell_known_before : form list; (** facts known to hold before command *)
  mutable bcell_known_after : form list; (** facts known to hold after command *)
}

(** If statement.  Could be eliminated using choice + assume.

if if_condition then if_then else if_else *)
and if_command = {
  mutable if_condition : form;
  if_then : command;
  if_else : command;
}

(** General looping construct with exit in the middle.

loop invariant loop_inv; loop_prebody; if loop_test then exit; loop_postbody endloop *)
and loop_command = {
  mutable loop_inv : form option;
  loop_prebody : command;
  mutable loop_test : form;
  loop_postbody : command;
}

(** Return from procedure *)
and return_command = {
  mutable return_exp : form option;
}

(** Structured commands. *)
and command = 
  | Basic of basic_cell
  | Seq of command list
  | Choice of command list
  | If of if_command
  | Loop of loop_command
  | Return of return_command

(** Specification variable definition. *)
type specvar_def = ident * form

and simple_body = {
  sb_body : command;
}

(** Procedure definition *)
and proc_def = {
  p_header  : proc_header;   (** procedure header *)
  p_locals  : var_decl list; (** all local variables of procedure *)
  mutable p_vardefs : specvar_def list; (** vardefs for non-ghost abstract locals *)
  mutable p_body    : command;       (** procedure body *)
  mutable p_simple_body : simple_body option; (** desugared version of procedure *)
}

(** Implementation module. *)
and impl_module = {  
  im_name   : ident;              (** module name *)
  im_owner : ident option;        (** owner of this module *)
  im_vars   : var_decl list;      (** implementation variables,
				  qualified with (im_name ^ ".") *)
  mutable im_vardefs : specvar_def list; (** shorthand definitions *)
  mutable im_constdefs : specvar_def list; (** shorthand state-free definitions *)
  mutable im_invs   : Specs.invariant_desc list;  (** invariants *)
  im_procs  : proc_def list;      (** procedures *)
  im_lemmas : (ident * form) list;  (** names and statements of lemmas *)
}

(** Specification module. *)
and spec_module = {
  sm_name       : ident;         (** module name *)
  sm_spec_vars  : var_decl list; (** specification (and public) variables,
				      qualified with (sm_name ^ ".") *)
  mutable sm_constdefs : specvar_def list; (** shorthand state-free definitions *)
  mutable sm_vardefs : specvar_def list; (** shorthand definitions *)
  mutable sm_free_invs : Specs.invariant_desc list;(** non-free invariants on public variables *)
  mutable sm_invs : Specs.invariant_desc list;(** non-free invariants on public variables *)
  sm_proc_specs : proc_header list; (** procedure interfaces *)
}

(** Mapping of an implementation module to a specification module.
This mapping induces a conformance requirement. *)
type mapping = {
  map_impl : impl_module;
  map_spec : spec_module;
  mutable map_abst : specvar_def list; (** mapping of specification variables *)
}

type global_def = {
  global_name : ident;
  global_type : ident;
}

type field_def = {
  field_name : ident;
  field_from : ident;
  field_to : ident;
}

(** The entire program. *)  
type program = {
  p_types : typeDef list;     (** user-defined {!Form} types; currently unused *)
  p_impls : impl_module list; (** implementation modules *)
  p_specs : spec_module list; (** specification modules *)
  p_maps  : mapping list;     (** mappings from implementations to specifications *)

  p_globals : global_def list; (** type information about globals (static variables) *)
  p_ref_fields : field_def list; (** reference field type information *)
  p_prim_fields : field_def list; (** primitive field type information *)
}
