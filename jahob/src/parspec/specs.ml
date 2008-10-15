(** Abstract syntax tree for Jahob specifications. *)

open Form

type contract_def =
    { c_pre  : form option;
      c_mod  : form list option;
      c_post : form option }

type abstract_var_decl = { 
  avd_name : string;
  avd_type : Form.typeForm;
  avd_init : Form.form option;
  avd_public : bool;
  avd_field : bool;
  avd_ghost : bool;
}

type abstract_assign = {
  aa_lhs : form;
  aa_rhs : form;
}

type var_def = ident * form

type mod_kind =
	| Readonly
	| ClaimedBy of string
	| Hidden

type publicness = 
  | PubPublic
  | PubPrivate
  | PubDefault

type staticness =
  | StatStatic
  | StatInstance

type ghostness =
  | GhostVar
  | NonGhostVar

type abstract_operation = {
  ao_name : string;
  ao_args : form list;
}

type lemma_desc = {
  lemma_name : string;
  lemma_form : form;
}

type invariant_desc = {
  inv_name : string;
  inv_ensured : bool;
  inv_public : bool;
  inv_form : form;
}

type spec = 
  | Lemma of lemma_desc
  | Invariant of invariant_desc
  | Contract of contract_def
  | SpecField of abstract_var_decl
  | SpecStatic of abstract_var_decl
  | SpecVar of abstract_var_decl
  | Constdefs of var_def list
  | PubConstdefs of var_def list
  | Vardefs of var_def list
  | PubVardefs of var_def list
  | Modifier of mod_kind
  | Assert of form
  | NoteThat of form
  | Assume of form
  | Split of form
  | Havoc of form list
  | Have of form
  | Assign of abstract_assign
  | Operation of abstract_operation

let mk_contract pre md post = 
  Contract { c_pre = pre; c_mod = md; c_post = post }

(*
let mk_spec_field n t i = SpecField { 
  avd_name=n; 
  avd_type=t; 
  avd_init=i;
  avd_public = true;
  avd_field = true;  
}

let mk_spec_static n t i = SpecStatic { 
  avd_name=n; 
  avd_type=t; 
  avd_init=i;
  avd_public = true;
  avd_field = false;
}
*)

let warn_deprecated_specfield() = 
  Util.warn "specfield deprecated, use specvar instead"

let warn_deprecated_specstatic() = 
  Util.warn "specstatic deprecated, use specvar instead"

let mk_specvar 
    (pns : publicness)
    (sns : staticness)
    (gns : ghostness)
    (id  : ident)
    (t   : typeForm)
    (oi  : form option) : spec = 
  SpecVar {
    avd_name = id;
    avd_type = t;
    avd_init = oi;
    avd_public = (pns = PubPublic);
    avd_field = (sns != StatStatic);
    avd_ghost = (gns = GhostVar)
  }

let mk_def (f : form) : ident * form = match f with
  | App(Const MetaEq, [Var v;rhs]) -> (v,rhs)
  | _ -> failwith ("Expected a definition of form 'varName == formula'" ^
		     "while parsing " ^ PrintForm.string_of_form f)

let mk_constdefs (pns : publicness) (vds : var_def list) = 
  if pns = PubPublic then PubConstdefs vds
  else Constdefs vds

let mk_vardefs (pns : publicness) (vds : var_def list) = 
  if pns = PubPublic then PubVardefs vds
  else Vardefs vds

let mk_modifier (m : mod_kind) = Modifier m

let mk_aassign (lhs : form) (rhs : form) =
  Assign {aa_lhs=lhs; aa_rhs=rhs}

let mk_aoperation (name : string) (args : form list) =
  Operation {ao_name=name; ao_args=args}

let mk_lemma (name : string) (f : form) =
  Lemma {lemma_name = name; lemma_form = f}

let mk_invariant (pub:publicness) (ensured:bool) (name:string) (f:form) : spec = 
  Invariant  {
    inv_name = name;
    inv_public = (pub =PubPublic);
    inv_ensured = ensured;
    inv_form = f
  }
  
(** get the formula associated with an invariant, along with a comment stating its name *)
let good_looking_inv ?(msg = "") (inv : invariant_desc) : Form.form = 
  FormUtil.mk_comment (msg ^ " " ^ inv.inv_name) inv.inv_form
