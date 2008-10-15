(** Main analysis loop. *)

open Ast
open AstUtil
open Form
open FormUtil
open Common
open PrintForm

(** Debug messages **)
let debug_lmsg = Debug.debug_lmsg (Debug.register_debug_module "Analyze")

let process_obligations 
    (name : string)
    (obs : obligation list) : bool =
  let _ = Decider.start name in
  let _ = Util.msg (Printf.sprintf "Generated %d proof obligations.\n"
		       (List.length obs)) in
  let proc_ok = ref true in
  let p_oblig (ob : obligation) : unit =
    if !proc_ok || not !CmdLine.failfast then
      (let obstr = string_of_oblig ob in
       let obname = name_of_oblig ob in
       let _ = debug_lmsg 0 (fun () -> "\nVERIFICATION CONDITION:\n" ^ obstr ^"\n") in
       let res = Decider.ob_valid ob in
	 if res then debug_lmsg 0 (fun () -> "\nVERIFICATION CONDITION " ^ 
				     obname ^ " is VALID.\n")
	 else (debug_lmsg 0 (fun () -> ("\nVERIFICATION CONDITION " ^ obname ^ " is INVALID.\n"));
	       proc_ok := false))
    else () in
  let _ = List.iter p_oblig obs in
    (Decider.stop(); !proc_ok)

(** Analyze that procedure conforms to a give specification. *)
let analyze_proc_to_spec (prog : program) (im : impl_module)
    (p : proc_def) (spec : proc_header) (m : specvar_def list) : bool = 
  let classn = im.im_name in
  let name = p.p_header.p_name ^ "_" ^ classn in
  let p' = 
    if not (!CmdLine.callbohne) then p else
      (let res = BohneInterface.analyze_proc prog im p spec m in
       let _ = if !CmdLine.printSAst or !CmdLine.printAst then
	 (print_string ("Ast after annotation:\n");
	  print_string (PrintAst.pr_command res.p_body))
       in
	 res)
  in
  let res = 
    if (!CmdLine.inferLoopInvs) then
      LoopInvariantInference.infer_loop_invariants prog im p' spec m;
    let _ = Util.msg "Generating VCs...\n" in
    let obs = Vcgen.vcs_of_procedure prog im p' spec m (not !CmdLine.callbohne) in
    let _ = Util.msg "Done generating VCs.\n" in
    let _ = Util.msg "Processing VCs..." in
    process_obligations name obs 
  in res

(** Check that invariants hold in the initial state of the module. *)
let check_invariants_initially_map
    (prog : program)
    (map : mapping) : bool =
  let classn = map.map_impl.im_name in
  let _ = Util.msg ("Checking initial state of class " ^ 
		      classn ^ "\n") in    
  let obs = Vcgen.vcs_of_initial_state prog map in
  let name = classn ^ "_INIT" in
    process_obligations name obs

(** Check that representation invariants and variables are preserved by the outside
    of the module. *)
let check_invariants_rep_map
    (prog : program)
    (map : mapping) : bool =
  let classn = map.map_impl.im_name in
  let _ = Util.msg ("Checking rep of class " ^ 
		      classn ^ "\n") in    
  let obs = Vcgen.vcs_of_rep prog map in
  let name = classn ^ "_REP" in
    process_obligations name obs

let check_invariants_initially
    (prog : program)
    (im : impl_module) : bool =
  let ok = ref true in
  let rec check_all (maps : mapping list) : unit =
    match maps with
      | [] -> ()
      | map::maps1 ->
	  (if map.map_impl = im then
	     ok := !ok && check_invariants_initially_map prog map
	   else ());
	  check_all maps1
  in
    check_all prog.p_maps;
    !ok

let check_invariants_rep
    (prog : program)
    (im : impl_module) : bool =
  let ok = ref true in
  let rec check_all (maps : mapping list) : unit =
    match maps with
      | [] -> ()
      | map::maps1 ->
	  (if map.map_impl = im then
	     ok := !ok && check_invariants_rep_map prog map
	   else ());
	  check_all maps1
  in
    check_all prog.p_maps;
    !ok

(** Analyze that procedure conforms to specifications of
   all procedures in specification modules for which
   there exists a mapping. *)
let analyze_proc (prog : program) (im : impl_module)
    (p : proc_def) : bool = 
  let trivial = ref true in
  let pname = im.im_name ^ "." ^ p.p_header.p_name in
  let _ = 
    if !Util.verbose then Util.msg ("\nNow analyzing: ==== Procedure " ^ pname ^ " ====\n") 
    else Util.amsg("\n[" ^ pname )
  in
  let analyze_map (m : mapping) : bool =
    if m.map_impl = im then
      match find_proc_header p.p_header.p_name m.map_spec with
	| None -> 
	    (trivial := false;
	     Util.msg("Procedure " ^ pname ^ 
			" is not a public procedure.\n");
	     analyze_proc_to_spec prog im p p.p_header m.map_abst)
	| Some ph ->
	    (trivial := false;
	     analyze_proc_to_spec prog im p ph m.map_abst)
    else true
  in
  let res = List.for_all analyze_map prog.p_maps in
  let _ = 
    if !Util.verbose then Util.msg ("\nDone analyzing Procedure " ^ pname ^ ".\n") 
    else Util.amsg(pname ^ "]")
  in    
    if !trivial then 
      (Debug.msg("Could not find refinement conditions to analyze spec for procedure " ^
		  pname ^ "\n");
       false)
    else res

let analyze_proc_named 
    (prog : program) 
    ((classn,methodn) : (string * string)) : bool =
  let clasmethod = classn ^ "." ^ methodn in
    match find_im classn prog with
      | None -> (Util.warn ("Could not find class to analyze: " ^ 
			      classn); 
		 false)
      | Some im ->
	  let procn = Jast2ast.c_method_name classn methodn in
	    if procn = CmdLine.initialization_name then
	      check_invariants_initially prog im
	    else if procn = CmdLine.repcheck_name then
	      check_invariants_rep prog im
	    else 
	      (match find_proc procn im with
		 | None -> (Util.warn
			      ("Could not find method to analyze: " 
			       ^ clasmethod);			  
			    false)
		 | Some p -> analyze_proc prog im p)

let prove_lemma (clname : string) (lmname : string) (f : form) : bool =
  process_obligations (clname ^ "_" ^ lmname) [{
    ob_pos = {pos_class = clname; pos_method = ""; pos_place=""};
    ob_purpose = "lemma_" ^ lmname;
    ob_form = f;
  }]

let prove_lemma_named
    (prog : program)
    ((classn,lemman) : (string * string)) : bool =
  let fullname = classn ^ "." ^ lemman in
    match find_im classn prog with
      | None -> (Util.warn ("Could not find class for lemma : " ^ 
			      classn);
		 false)
      | Some im ->
	  (match find_lemma lemman im with
	     | None -> (Util.warn
			  ("Could not find lemma to analyze: " 
			   ^ fullname);			  
			false)
	     | Some f -> prove_lemma classn lemman f)

let rec check_all (fs : (unit -> bool) list) : bool =
  match fs with
    | [] -> true
    | f::fs1 -> 
	if f() then check_all fs1
	else
	  if !CmdLine.failfast then false
	  else (check_all fs1; false)
	    
let analyze_class_named
    (prog : program)
    (classn : string) : bool =
  Util.amsg ("\nAnalyzing class " ^ classn ^ ".\n");
  match find_im classn prog with
    | None -> Util.fail ("Could not find class to analyze: " ^ 
			   classn)
    | Some im ->
	let init () = check_invariants_initially prog im in
	let rep () = check_invariants_rep prog im in
	let procs = List.map (fun pd () -> analyze_proc prog im pd) im.im_procs in
	  check_all (init::rep::procs)

(** Main method: analyze that given methods and classes satisfy
    their specifications. *)
let rec analyze 
    (prog : program)
    (task : analysis_task) : bool =
  List.for_all (fun x -> x)
    (List.map (prove_lemma_named prog) task.task_lemmas @
       List.map (analyze_proc_named prog) task.task_methods @
       List.map (analyze_class_named prog) task.task_classes)
