(** Interface to Isabelle theorem prover as a decision procedure. *)

open Common
open Form
open FormUtil

type isabelleOutput = Ok | Error of string

let default_opts () : options_t =
  let isabelle_defaults = [("TimeOut", string_of_int !CmdLine.timeout)
	                  ] in        
    map_of_list isabelle_defaults

let debug_id : int = Debug.register_debug_module "Isabelle"
let debug_msg : (string -> unit) = Debug.debug_msg debug_id
let debug_is_on () : bool = Debug.debug_is_on debug_id

let reparse formula = 
  let formula_string = 
    PrintForm.string_of_form formula in
    (formula_string, ParseForm.parse_formula formula_string)

let parseIsabelleOutput (fn : string) : isabelleOutput = 
  let okString = "val it = () : unit" in
  let errorString = "***" in
  let isErrorLine s = Str.string_match (Str.regexp_string errorString) s 0 in
  let foundOk = ref false in
  let foundError = ref false in
  let errorOutput = ref "" in
  let line = ref "" in
  let chn = open_in fn in
  begin
    (try line := input_line chn;
    while true do
      if !line = okString then foundOk := true else ();
      if isErrorLine !line then begin
        errorOutput := !errorOutput ^ !line ^ "\n";
        foundError := true
      end else ();
      line := input_line chn
    done with End_of_file -> ());
    close_in chn;
    if !foundOk & not (!foundError) then Ok
    else Error !errorOutput
  end

let total_proof_obligations = ref 0

let pending_file_name name = Util.tmp_name "pending_" ^ name ^ ".thy"
let created_pending_file_name = ref ""
let pending_file = ref None
let write_pending str = 
  match !pending_file with
  | None -> ()
  | Some chn -> output_string chn str
let open_pending name = 
  try (let chn = open_out (pending_file_name name) in
	 pending_file := Some chn;
	 created_pending_file_name := pending_file_name name;
         output_string chn "theory PendingVC = Jahob:\n\n")
  with Sys_error s -> Util.warn s

let close_pending () = 
  match !pending_file with
  | None -> ()
  | Some chn -> (close_out chn; pending_file := None)

let rtrancl_name = "rtrancl_pt"

let no_rtrancl (f : form) : bool =
  not (List.mem rtrancl_name (fv f))

let vc_theory_counter : int ref = ref 0
let incr_vc_theory () : unit =
  vc_theory_counter := !vc_theory_counter + 1  
let incr_vc_theory_if_debug () : unit =
  if (debug_is_on ()) then incr_vc_theory ()
let next_vc_theory () : string =
  "vc" ^ (string_of_int !vc_theory_counter)

let vc_out_counter : int ref = ref 0
let incr_vc_out () : unit =
  vc_out_counter := !vc_out_counter + 1
let incr_vc_out_if_debug () : unit =
  if (debug_is_on ()) then incr_vc_out ()
let next_vc_out () : string =
  "vc" ^ (string_of_int !vc_out_counter) ^ ".out"

let decide_sq (sqob : sq_obligation) (sqno:int) ~(options:options_t): bool =
  let options = merge_opts (default_opts ()) options in
  let sq = (List.filter no_rtrancl (fst sqob.sqob_sq),
	    snd sqob.sqob_sq) in
  let default_simps = "cardeq1_def cardleq1_def " in
  let proof0 = "" in
  let proof = "by (auto simp add: " ^ default_simps ^ proof0 ^ ")" in
  let isabelleName = "isabelle-process" in
  let theory_name = next_vc_theory () in
  let vc_theory = Util.tmp_name theory_name in
  let vc_file = vc_theory ^ ".thy" in
  let semantics_lib = Util.lib_name "Jahob" in
  let vc_in = Util.tmp_name "vc.in" in
  let vc_out = Util.tmp_name (next_vc_out ()) in

  let vc_string = string_of_sequent sq in

  let write_input_redir () : unit =
    let chn = open_out vc_in in
      (output_string chn ("use_thy \"" ^ vc_theory ^ "\";");
       output_string chn "exit 0;";
      close_out chn)
  in

  let isabelle_input () =
    "theory " ^ theory_name ^ "\n" ^ 
    "imports \"" ^ semantics_lib ^ "\"\nbegin\n" ^
      "lemma \"" ^ vc_string ^ "\"\n" ^ proof ^ "\nend\n" in

  let pmsg str =
    if sqno = 0 then () 
    else 
      (if !Util.verbose then Util.msg str 
       else Util.amsg ".")
  in

  let run (f : form) : bool =
    incr total_proof_obligations ;
    let _ = write_input_redir () in
    let lemma_string = isabelle_input () in
    let timeout = int_of_string (StringMap.find "TimeOut" options) in
    let chn = open_out vc_file in
      output_string chn lemma_string;
      close_out chn; flush_all ();
      let _ = Util.run_with_timeout
        (isabelleName ^ " < " ^ vc_in ^ " > " ^ vc_out ^ " 2> /dev/null")
        timeout in
	flush_all();
	(match parseIsabelleOutput vc_out with
	   | Ok -> 
	       (pmsg "Proof obligation proved valid.\n"; true)
	   | Error msg ->
	       (pmsg "Failed to show proof obligation valid.\n";
		incr_vc_theory_if_debug ();
                incr_vc_out_if_debug ();
		Util.msg msg; Util.msg "\n"; 
		false))
  in
    begin
      let f = form_of_sequent sq in
	if Vclemmas.known_fact (reparse f) then 
	  (debug_msg ("Proof obligation previously proved in lemma file.\n"); true)
	else
	  let ok = if !CmdLine.noisabelle then false else run f in
	    if ok then true
	    else
	      let cs = extract_comments (snd sq) in
		(if cs <> "" then Util.msg ("Failed proof obligation in Isabelle interface talks about: " ^ cs ^ "\n") else ();
		 Util.msg ("(See file " ^ !created_pending_file_name ^ 
			     " for failed proof obligation.)\n");
		 let lemma_name = identlike_pos sqob.sqob_pos ^ "_" ^ sqob.sqob_purpose in
		   (write_pending ("lemma " ^ lemma_name ^ ": \"" ^
				     string_of_sequent (strip_sq_types sqob.sqob_sq) ^ "\"\nsorry\n\n");
		    false))
    end
      
(* let typecheck (f : form) : bool =
  decide_sq (form_to_sqob f) 0 *)

let start name =
  (Vclemmas.init name; open_pending name)

let stop () =
  write_pending "\nend\n"; close_pending ()
