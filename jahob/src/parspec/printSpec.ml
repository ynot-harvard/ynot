(** Printing of {!Specs} specifications. *)

open Jast
open Specs

let p_mod_item (mi : mod_item) : string = 
  PrintForm.string_of_form mi

let quote s = "\"" ^ s ^ "\""

let pqform (f : Form.form) : string =
  quote (PrintForm.string_of_form f)

let poform (kw : string) (optf : Form.form option) : string list =
  match optf with
  | None -> []
  | Some f -> [kw ^ pqform f]

let poforms (kw : string) (optf : Form.form list option) : string list =
  match optf with
  | None -> []
  | Some fs -> [kw ^ String.concat ", " (List.map pqform fs)]

let print_contract (m : method_decl) : string option =
  match (m.m_pre,m.m_modifies,m.m_post) with
  | (None,None,None) -> None
  | _ -> 
      (let res = 
        String.concat "\n"
          (List.concat
             [poform  "  requires " m.m_pre;
              poforms "  modifies " m.m_modifies;
              poform  "  ensures " m.m_post]) in
      Some (res ^ ";\n"))

let p_typ (t : Form.typeForm) = PrintForm.wr_type t
let p_optinit (optf : Form.form option) = match optf with
| None -> ""
| Some f -> " = \"" ^ PrintForm.string_of_form f ^ "\""

let p_specvar (avd : avar_decl) : Syntax.annotation = 
  (if avd.avd_public then "public " else "private ") ^
  (if avd.avd_field then "" else "static ") ^
  "specvar " ^
  avd.avd_name ^ " :: \"" ^ p_typ avd.avd_type ^ "\"" ^
  p_optinit avd.avd_init ^ ";"

let p_abst_field (avd : avar_decl) : Syntax.annotation =
  p_specvar avd

let p_abst_global (avd : avar_decl) : Syntax.annotation =
  p_specvar avd

let p_vd ((v,f) : var_def) : string =
  "\"" ^ v ^ " == " ^ PrintForm.string_of_form f ^ "\"" ^ ";"

let p_vardefs (vds : var_def list) : Syntax.annotation =
  "private vardefs " ^ (String.concat "\n" (List.map p_vd vds))

let p_pubvardefs (vds : var_def list) : Syntax.annotation =
  "public vardefs " ^ (String.concat "" (List.map p_vd vds))

let p_constdefs (vds : var_def list) : Syntax.annotation =
  "private constdefs " ^ (String.concat "" (List.map p_vd vds))

let p_pubconstdefs (vds : var_def list) : Syntax.annotation =
  "public constdefs " ^ (String.concat "" (List.map p_vd vds))

let p_hide_objs f = "hide objects " ^ pqform f
let p_claim_locs f = "claim locations " ^ pqform f

let p_aoperation (ao : abstract_operation) : Syntax.annotation =
  ao.ao_name ^ "(" ^ 
    String.concat ", " (List.map PrintForm.string_of_form ao.ao_args) ^ ")"

let p_invariant (i : invariant_desc) : string =
  let publicness = if i.Specs.inv_public then "public " else "private " in
  let ensured = if i.Specs.inv_ensured then "ensured " else "" in
  let name = if i.Specs.inv_name <> "" then "\"" ^ i.Specs.inv_name ^ "\" " else "" in
    Printf.sprintf "%s%sinvariant %s%s" publicness ensured name (PrintForm.quoted_form i.Specs.inv_form)
