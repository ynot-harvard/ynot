(** Interface to Isabelle theorem prover as a decision procedure. *)

open Common
open Form
open FormUtil

type coqOutput = Ok | Error of string

let default_opts () : options_t = 
  let foo = [("TimeOut", string_of_int !CmdLine.timeout);
	     ("Tactic", "eauto ; intros ; intuition ; subst ; eauto 100 ; firstorder.")
	    ] in
    map_of_list foo

(* form -> string list *)
let rec free_types_var_tform = function
  | TypeUniverse -> []
  | TypeVar s -> s::[]
  | TypeApp (TypeDefined s, l) -> s::(List.concat (List.map free_types_var_tform l))
  | TypeApp (_, l) -> List.concat (List.map free_types_var_tform l)
  | TypeFun (args, res) -> List.concat (List.map free_types_var_tform (res::args))
  | TypeProd l -> List.concat (List.map free_types_var_tform l)


(** get the names of the free types variable inn a given formula. form -> string List *)
let rec free_type_variables = function
  | TypedForm (_, t) -> free_types_var_tform t
  | Binder (_, bound, f) -> 
      (free_type_variables f) 
      @ (List.concat (List.map (fun (_,t) -> free_types_var_tform t) bound))
  | App (x, l) -> List.concat (List.map free_type_variables (x::l))
  | _ -> []
			      
let uniquify l = 
  let l' = List.sort compare l in
  let rec foo= function
    | x::y::suite when x=y -> foo (y::suite)
    | x::suite -> x::(foo suite)
    | [] -> []
  in foo l'

let reparse formula = 
  let formula_string = 
    PrintForm.string_of_form formula in
    (formula_string, ParseForm.parse_formula formula_string)

let pending_file_name name = Util.tmp_name "pending_" ^ name ^ ".v"
let proven_file_name name = "already_proven_" ^ name

let total_proof_obligations = ref 0

let created_pending_file_name = ref ""
let current_name = ref ""
let pending_file = ref None
let write_pending str = 
  match !pending_file with
  | None -> ()
  | Some chn -> output_string chn str

(** try to open the pending file, to output the pending lemmas in it. *)
let open_pending name = 
  try (let chn = open_out (pending_file_name name) in
	 pending_file := Some chn;
	 created_pending_file_name := pending_file_name name;
         output_string chn "(* This is just the beginning *)\n\n" ;
	 current_name := name )
  with Sys_error s -> Util.warn s


let close_pending () = 
  match !pending_file with
  | None -> ()
  | Some chn -> (close_out chn; pending_file := None)


let rtrancl_name = "rtrancl_pt"

let no_rtrancl (f : form) : bool =
  not (List.mem rtrancl_name (fv f))

let string_of_sequent_coq (sq:sequent) : string = 
  PrintFormCoq.string_of_form (form_of_sequent sq)

let header () = 
   (* We need the set library, as sets are not built-in *)
  let required_libraries = "Require Import Finite_sets_facts.\n Require Import Jahob.\n Require Import Omega.\n" in
  
  (* Then we check wether a proved lemma files exist *)
  let already_proven_lemmas = 
    let fn_no_ext = proven_file_name !current_name in
    if Sys.file_exists (fn_no_ext ^ ".vo") then (
"Require Import "^ fn_no_ext ^ ".\n") else "" 
  in
  required_libraries ^ "\n" ^ already_proven_lemmas ^ "\n"


(** main procedure *)
let decide_sq ~(options:options_t) (sqob : sq_obligation) (sqno:int) : bool =
  let options = merge_opts (default_opts ()) options in

  let sq = (* (List.filter no_rtrancl (fst sqob.sqob_sq),
	    snd sqob.sqob_sq) *) sqob.sqob_sq in
  let sq_form = TypeReconstruct.disambiguate (form_of_sequent sq) in
  let vc_string = PrintFormCoq.string_of_form sq_form in
  let lemma_name = identlike_pos sqob.sqob_pos ^ "_" ^ sqob.sqob_purpose in
    (* let's be optimistic. Auto will try the lemmas in the databse *)
  let proof = StringMap.find "Tactic" options in
  let coqName = "coqc" in


(* ----------------------- *)

  let write_input_redir () : unit =
    ()
  in

  (** generate the input for coq *)

  let generate_parm_def env = function (* of the variable name *) 
    | x when x = "tree" -> ""
    | x when x =  rtrancl_name -> ""
    | var -> let v_type = List.assoc var env in
	"(" ^ PrintFormCoq.coq_ident var ^ " : " ^ PrintFormCoq.string_of_type v_type ^ ")"
  in
  
  let coq_input () =
    (* we quantify over all the free variables *)
    let f, env = TypeReconstruct.reconstruct_types [] sq_form in
    let fv_stuff = match FormUtil.fv f with 
	| [] -> ""
	| fvs -> 
	  let free_type_vars = uniquify (free_type_variables f) in
	  let type_variables = String.concat " " (List.map (fun x -> "(" ^ x ^ ":Set)") free_type_vars) in
	  let normal_variables = String.concat " " (List.map (generate_parm_def env) fvs) in
	  
	  "forall " ^ type_variables ^ " " ^ normal_variables ^ ", " 
      in
      
      String.concat "\n" [
	"Lemma " ^ lemma_name ^ " : " ^ fv_stuff ^ "\n";
	vc_string ^ "."; 
	"Proof." ;
	proof ; 
	"Qed."] in

(** print message *)
  let pmsg str =
    if sqno = 0 then () 
    else 
      (if !Util.verbose then Util.msg str 
       else Util.amsg ".")
  in

  let lemma_string = coq_input () in

  let run (f : form) : bool =
    let _ = write_input_redir () in
      incr total_proof_obligations ;
      let vc_in = Util.tmp_name (Printf.sprintf "vc_%d_in.v" !total_proof_obligations) in 
      let vc_out = Util.tmp_name (Printf.sprintf "vc_%d_out.v" !total_proof_obligations) in
      let chn = open_out vc_in in
	output_string chn (header ());
	output_string chn lemma_string;
	close_out chn; flush_all ();
	(try Sys.remove (vc_in ^ "o") with _ -> ());
	let timeout = int_of_string (StringMap.find "TimeOut" options) in
	let command_line = coqName ^ " -I " ^ Util.lib_name "" ^ " " ^ vc_in ^ " > " ^ vc_out ^ " 2>&1" in
	let _ = Util.run_with_timeout command_line timeout (* Sys.command command_line *) in
      	  match Sys.file_exists (vc_in ^ "o") with
	    | true -> pmsg "Proof obligation proved valid.\n"; true
	    | false -> pmsg "Failed to show proof obligation valid.\n"; false
  in
    begin

(* the ACTUAL main code is here *)
    let ok = if !CmdLine.nocoq then false else run sq_form in
    if ok then true
    else
      let cs = extract_comments (snd sq) in
	(if cs <> "" then Util.msg ("Failed proof obligation in Coq interface talks about: " ^ cs ^ "\n") else ();      	 
	 Util.msg ("(See file " ^ !created_pending_file_name ^ 
		     " for failed proof obligation.)\n");
	 write_pending (lemma_string ^ "\nHint Resolve " ^ lemma_name ^ ".\n\n");
	 false)
  end
    
(* let typecheck (f : form) : bool =
  decide_sq (form_to_sqob f) 0 ~ *)

(* is there any kind of automatic eta-reduction available ??? *) 
let start name =
  open_pending name ; total_proof_obligations := 0; 
  write_pending (header ())
  

let stop () =
  close_pending ()
