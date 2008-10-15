(** Print {!Ast} tree to a string. *)

open Common
open Ast
open Form
open FormUtil

let pf = PrintForm.string_of_form 

(** Print variable declaration. *)
let pr_var_decl (vd : var_decl) =
  vd.vd_name ^ " : " ^ PrintForm.string_of_type vd.vd_type ^
    (match vd.vd_init with 
       | None -> "" 
       | Some f -> " == " ^ pf f) ^    
    (let mod_abstract =
       if vd.vd_abstract then ["abstract"] else [] in
     let mod_ghost =
       if vd.vd_ghost then ["ghost"] else [] in
     let mod_field =
       if vd.vd_field then ["field"] else [] in       
     let mod_owner =
       match vd.vd_owner with
	 | None -> []
	 | Some cl -> ["claimedby " ^ cl] in
     let mods = List.concat 
       [mod_abstract;
	mod_ghost;
	mod_field;		
	mod_owner]
     in 
       match mods with 
	 | [] -> ""
	 | _ -> " [" ^ String.concat ", " mods ^ "]")

(** Print global variable declaration, including var keyword. *)
let pr_gvar_decl (vd : var_decl) = "var " ^ pr_var_decl vd ^ ";\n"

(** Print procedure contract. *)
let pr_contract (c : contract) =
  if c.co_resolved then
    "requires " ^ pf c.co_pre  ^ "\n" ^
    (match c.co_mod with
       | None -> ""
       | Some m -> "modifies " ^ 
	   String.concat ", " (List.map pf m) ^ "\n") ^
    "ensures " ^ pf c.co_post ^ "\n"
  else "(* SPEC UNRESOLVED *)"

(** Print procedure header. *)
let pr_proc_header (mname : ident) (ph : proc_header) =
  (if ph.p_public then "public " else "private ") ^
  "proc " ^ mname ^ "." ^ ph.p_name ^ 
  "(" ^ String.concat ", " (List.map pr_var_decl ph.p_formals) ^ ")" ^
  " : " ^ PrintForm.string_of_type ph.p_restype ^ "\n" ^
  pr_contract ph.p_contract

(** Increment padding (indentation string). *)
let incpad pad = "  " ^ pad 

let rec pr_basic_command (bc : basic_command) = pr_basic bc
and pr_var_assign (vac : assign_command) =
  vac.assign_lhs ^ " := " ^ pf vac.assign_rhs ^ ";\n"
and pr_alloc (alc : alloc_command) =
  alc.alloc_lhs ^ " := " ^ "new " ^ alc.alloc_type ^ ";\n"
and pr_array_alloc (aalc : array_alloc_command) =
  aalc.arr_alloc_lhs ^ " := " ^ "newarray " ^ 
    aalc.arr_alloc_type ^ "[" ^
    String.concat ", " (List.map pf aalc.arr_alloc_dims) ^ "];\n"
and pr_annot_cmd (cmdname : string) (ac : annot_form_command) =
  cmdname ^ " \"" ^ ac.annot_msg ^ "\": " ^ pf ac.annot_form ^ ";\n"
and pr_havoc (hc : havoc_command) =
  "havoc " ^ String.concat ", " (List.map pf hc.havoc_regions) ^ ";\n"
and pr_call (pc : proc_call) =
  let external_str = 
    if pc.call_is_external then " [external]" 
    else " [internal]" in
    (match pc.callee_res with
       | None -> ""
       | Some id -> id ^ " := ") ^
      pc.callee_module ^ "." ^ pc.callee_name ^ 
      "(" ^ String.concat ", " (List.map pf pc.callee_args) ^ ")" ^ external_str ^ ";\n"
and pr_basic (bc : basic_command) = match bc with
  | Skip -> "skip;\n"
  | VarAssign vac -> pr_var_assign vac
  | Alloc alc -> pr_alloc alc
  | ArrayAlloc aalc -> pr_array_alloc aalc
  | Assert ac -> pr_annot_cmd "assert" ac
  | NoteThat ac -> pr_annot_cmd "noteThat" ac
  | Assume ac -> pr_annot_cmd "assume" ac
  | Split ac -> pr_annot_cmd "split" ac
  | Havoc hc -> pr_havoc hc
  | ProcCall pc -> pr_call pc
  | Hint h -> pr_hint h

and pr_hint (h : hint) = 
  match h with
    | TrackSpecvar {track_var=id} -> "track(" ^ id ^ ");\n"

let rec pr_command (c : command) = prc "  " c
and pr_basic_cell (pad : string) (c : basic_cell) =
  (if c.bcell_known_before=[] then "" else
     pad ^ "[before: " ^ pf (mk_and c.bcell_known_before) ^ "]\n") ^
  pad ^ pr_basic_command c.bcell_cmd ^
  (if c.bcell_known_after=[] then "" else
     pad ^ "[after: " ^ pf (mk_and c.bcell_known_after) ^ "]\n")
and pr_if (pad : string) (ifc : if_command) =  
  "if " ^ pf ifc.if_condition ^ " then\n" ^ 
    prc (incpad pad) ifc.if_then ^
    "else\n" ^ 
    prc (incpad pad) ifc.if_else ^
    "endif;\n"
and pr_loop (pad : string) (looc : loop_command) =
  "loop\n" ^
    (match looc.loop_inv with
       | None -> ""
       | Some f -> "  invariant " ^ pf f ^ ";\n") ^
    prc (incpad pad) looc.loop_prebody ^
    "exitunless " ^ pf looc.loop_test ^ ";\n" ^
    prc (incpad pad) looc.loop_postbody ^
    "endloop;\n"
and pr_return (ret : return_command) = 
  "return " ^
    (match ret.return_exp with
       | None -> ""
       | Some f -> pf f) ^ ";\n"
and prc (pad : string) (c : command) = match c with
  | Basic c -> pr_basic_cell pad c
  | Seq cs -> 
      "{" ^ String.concat "" (List.map (prc pad) cs) ^ "}"
  | Choice cs ->
      "choose " ^
	String.concat "orchoose\n" (List.map (prc (incpad pad)) cs) ^
	"endchoose;"
  | If ifc -> pr_if pad ifc
  | Loop looc -> pr_loop pad looc
  | Return ret -> pr_return ret

(** Print variable definition in a mapping. *)
let pr_vardef ((v,f) : specvar_def) = 
  "    " ^ v ^ " == " ^ pf f ^ ";\n"

(** Print vardefs. *)
let pr_vardefs (svs : specvar_def list) =
  match svs with
    | [] -> ""
    | _ -> "vardefs\n" ^
        String.concat "" (List.map pr_vardef svs)

(** Print constdefs. *)
let pr_constdefs (svs : specvar_def list) =
  match svs with
    | [] -> ""
    | _ -> "constdefs\n" ^
        String.concat "" (List.map pr_vardef svs)


(** Print procedure. *)
let pr_proc_def (mname : ident) (p : proc_def) =
  pr_proc_header mname p.p_header ^
  String.concat "" (List.map pr_gvar_decl p.p_locals) ^
  pr_vardefs p.p_vardefs ^ "\n" ^
  "{\n" ^
    pr_command p.p_body ^
  "}\n"

(** Print invariant list. *)
let pr_invs = function
  | [] -> ""
  | invs -> (String.concat "" (List.map PrintSpec.p_invariant invs)) ^ "\n"

(* 
   let pr_hide (f : form) = 
   "hide objects " ^ PrintForm.string_of_form f ^ ";\n"
   
   let pr_hides (hides : form list) = match hides with
   | [] -> ""
   | _ -> (String.concat "" (List.map pr_hide hides)) ^ "\n"
   
   let pr_claim (f : form) = 
   "claim locations " ^ PrintForm.string_of_form f ^ ";\n"
   
   let pr_claims (claims : form list) = match claims with
   | [] -> ""
   | _ -> (String.concat "" (List.map pr_claim claims)) ^ "\n"
*)

let pr_owner (owner : ident option) =
  match owner with
    | None -> ""
    | Some id -> "claimedby " ^ id ^ "\n"

(** Print implementation module. *)
let pr_impl (im : impl_module) =
  "impl module " ^ im.im_name ^ "\n" ^
  pr_owner im.im_owner ^
  String.concat "" (List.map pr_gvar_decl im.im_vars) ^ "\n" ^
  pr_constdefs im.im_constdefs ^
  pr_vardefs im.im_vardefs ^
  pr_invs im.im_invs ^
    (*
      pr_hides im.im_hide ^
      pr_claims im.im_claim ^
    *)
    String.concat "\n" (List.map (pr_proc_def im.im_name) im.im_procs) ^
  "\nend impl module " ^ im.im_name ^ ".\n"

(** Print specification module. *)
let pr_spec_module (sm : spec_module) =
  "spec module " ^ sm.sm_name ^ "\n" ^
    String.concat "" (List.map pr_gvar_decl sm.sm_spec_vars) ^
  pr_constdefs sm.sm_constdefs ^
  pr_vardefs sm.sm_vardefs ^
  pr_invs sm.sm_invs ^
  pr_invs sm.sm_free_invs ^
  String.concat "\n" (List.map (pr_proc_header sm.sm_name) sm.sm_proc_specs) ^
  "\nend spec module " ^ sm.sm_name ^ ".\n"

(** Print type definition. *)
let pr_typeDef (td : typeDef) = PrintForm.string_of_typedef td

(** Print mapping. *)
let pr_map (m : mapping) =
  "refinement\n" ^ 
  "impl " ^ m.map_impl.im_name ^ "\n" ^
  "spec " ^ m.map_spec.sm_name ^ "\n\n" ^
  pr_vardefs m.map_abst ^ "\n" ^
  "end refinement.\n"

(** Print program. *)
let pr_program (p : program) : string =
  "(*************************************************************)\n"^
  "(*                         BEGINPROGRAM                      *)\n"^
  "(*************************************************************)\n"^
  "(*                          Types                            *)\n"^
  "(*************************************************************)\n"^
   String.concat "\n" (List.map pr_typeDef p.p_types) ^ "\n" ^
  "(*************************************************************)\n"^
  "(*                   Implementation Modules                  *)\n"^
  "(*************************************************************)\n"^
   String.concat "\n" (List.map pr_impl p.p_impls) ^ "\n" ^
  "(*************************************************************)\n"^
  "(*                   Specification Modules                   *)\n"^
  "(*************************************************************)\n"^
   String.concat "\n" (List.map pr_spec_module p.p_specs) ^ "\n" ^
  "(*************************************************************)\n"^
  "(*                      Refinement Conditions                *)\n"^
  "(*************************************************************)\n"^
   String.concat "\n" (List.map pr_map p.p_maps) ^
  "\n\n(* ENDPROGRAM *)\n" ^
  "(*************************************************************)\n"

(** Top-level function, prints the entire program. *)
let string_of_program (p : program) : string = pr_program p


(* -------------------------------------------------- *)
(** Printing simplified (normalized) ast *)
(* -------------------------------------------------- *)


let spr_impl (im : impl_module) : string =
  let mname = im.im_name in
  let spr_proc_header (ph : proc_header) =
    (if ph.p_public then "public " else "private ") ^
    "proc " ^ mname ^ "." ^ ph.p_name ^ 
      "(" ^ String.concat ", " (List.map pr_var_decl ph.p_formals) ^ ")" ^
      " : " ^ PrintForm.string_of_type ph.p_restype ^ "\n" in
  let spr_proc (proc : proc_def) : string =
    match proc.p_simple_body with
      | None -> ""
      | Some b -> 
	  if List.mem (mname,proc.p_header.p_name) !CmdLine.methods_to_analyze then
	    spr_proc_header proc.p_header ^
	      pr_command b.sb_body
	  else ""
  in
    String.concat "" (List.map spr_proc im.im_procs)

let simplified_program (p : program) : string = 
  String.concat "" (List.map (spr_impl ) p.p_impls)
