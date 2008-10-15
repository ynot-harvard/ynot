(** Command line processing and invocation options. *)

open Common

let printAst = ref false
let printSAst = ref false
let printJast = ref false
let typecheck = ref true

let verify = ref true
let sastVC = ref false
let tokens = ref false
let failfast = ref false
let noisabelle = ref false
let nocoq = ref false
let notptp = ref false
let callbohne = ref false
let inferLoopInvs = ref false
let usedps = ref []
let excludedps = ref []
let checkHidden = ref false

let background = ref true
let minasm = ref false
let default_timeout = 10
let timeout = ref default_timeout

let useslicing = ref true
let usecaching = ref true

(** Flags for Bohne *)

(** derive predicates automatically *)
let derive_preds = ref true

(** use abstraction refinement *)
let refine = ref false

(** use more precise abstraction *)
let extra_precise = ref false

(** use quantifier instantiation for context formulas *)
let useinstantiation = ref true
let usecontext = ref true

(** compute invariant for return points *)
let abstract_final = ref false

let jahob_unsound = ref false
let bounded_loop_unroll = ref false
let unroll_factor = ref 1
let simple_call_site_frames = ref false


let (lemmas_to_prove : (string * string) list ref) = ref []
let add_lemmas (new_lemmas : (string * string) list) : unit =
  (lemmas_to_prove :=
     new_lemmas @ !lemmas_to_prove)

let (methods_to_analyze : (string * string) list ref) = ref []
let add_methods (new_methods : (string * string) list) : unit =
  (methods_to_analyze :=
     new_methods @ !methods_to_analyze)

let (classes_to_analyze : string list ref) = ref []
let add_class (s : string) : unit =
  (classes_to_analyze := s :: !classes_to_analyze)

let get_task () = {
  task_lemmas = !lemmas_to_prove;
  task_methods = !methods_to_analyze;
  task_classes = !classes_to_analyze;
}

let (javaFiles : string list ref) = ref []
let add_javaFile (file : string) : unit = 
  javaFiles := file :: !javaFiles

let initialization_name = "_INIT"
let repcheck_name = "_REP"

let split_equal (o:options_t) (s:string) = 
  match Str.split (Str.regexp "=") s with
    | [a] -> StringMap.add a "" o
    | [a;b] -> StringMap.add a b o
    | _ -> failwith "expected : opt or opt=value"

let add_excludedp id = excludedps := id::!excludedps
let add_usedp id = 
  match Str.split (Str.regexp ":") id with
    | [] -> assert false
    | name::options -> 
	let opts = ListLabels.fold_left ~f:split_equal ~init:(StringMap.empty) options in
	  usedps := (name, opts)::!usedps


let rec cmd_options = 
  [("-v", Arg.Set Util.verbose,
    "Display verbose messages");
   ("-verbose", Arg.Set Util.verbose,
    "Display verbose messages");
   ("-debug", Arg.Set Debug.debugOn,
    "Display debugging messages");
   ("-debuglevel", Arg.Int Debug.set_debug_level,
    "<int> Adjust amount of debug messages, default " ^ Printf.sprintf "%d" !Debug.debug_level);
   ("-debugmodules", Arg.String Debug.set_debug_modules,
    "<modules> Turn on debug messages for a specific module (e.g. smtPrint)");
   ("-jast", Arg.Set printJast,
    "Display intermediate Jast representation");
   ("-ast", Arg.Set printAst,
    "Display intermediate Ast representation");
   ("-sast", Arg.Set printSAst,
    "Display simplified Ast representation");
   ("-sastvc", Arg.Set sastVC,
    "Generate verification conditions from simplified Ast");
   ("-hidden", Arg.Set checkHidden,
    "enforce the policy with regard to hidden objects");
   ("-notypecheck", Arg.Clear typecheck,
    "Do not typecheck formulas");
   ("-failfast", Arg.Set failfast,
    "Fail as soon as one proof obligation fails");
   ("-resilient", Arg.Set Util.resilient,
    "Continue even if a warning is emitted");
   ("-minasm", Arg.Set minasm,
    "Try to find minimal set of assumptions needed to prove valid obligations");
   ("-noverify", Arg.Clear verify,
    "No verification, just transform to intermediate form");
   ("-noisabelle", Arg.Set noisabelle,
    "Turn off Isabelle invocation");
   ("-nocoq", Arg.Set nocoq,
    "Turn off Coq invocation");
   ("-novampire", Arg.Set notptp,
    "Turn off Vampire invocation"); 
   ("-nobackground", Arg.Clear background,
    "Do not generate verification condition background formula");
   ("-nopreddicovery", Arg.Clear derive_preds,
    "Do not discover predicates automatically in Bohne");
   ("-refine", Arg.Set refine,
    "Use abstraction refinement");
   ("-abstractfinal", Arg.Set abstract_final,
    "Include final transitions in Bohne's fixed point computation");
   ("-nocaching", Arg.Clear usecaching,
    "Do not use caching");
   ("-noinstantiation", Arg.Clear useinstantiation,
    "Do not use quantifier instantiation heuristics");
   ("-nocontext", Arg.Clear usecontext,
    "Do not use context");
   ("-extraprecise", Arg.Set extra_precise,
    "Use more precise abstraction in Bohne");
   ("-method", Arg.String add_class_method,
    "Analyze the given class.method\n" ^ 
      "    " ^ initialization_name ^ " checks initial condition\n" ^
      "    " ^ repcheck_name ^ " checks representation preservation");
   ("-class", Arg.String add_class,
    "Analyze the given class");
   ("-lemma", Arg.String add_lemma,
    "Prove given named lemma");
   ("-bohne", Arg.Set callbohne,
    "Infer loop invariants using Bohne");
   ("-infer", Arg.Set inferLoopInvs,
    "Infer loop invariants using other techniques");
   ("-unroll", Arg.Set bounded_loop_unroll,
    "Use bounded loop unrolling");
   ("-unrollfactor", Arg.Set_int unroll_factor,
    "Number of times to unroll loops");
   ("-simpcall", Arg.Set simple_call_site_frames,
    "Simplified call site frame conditions");
   ("-timeout", Arg.Int set_timeout,
    "<int> Set decision timeout (in seconds) for each decision procedure, default " ^ Printf.sprintf "%d" default_timeout);
   ("-usedp", Arg.Rest add_usedp,
    "<IDs> specify the list of used decision procedures (cvcl|mona|isa|coq|vampire|e)");
   ("-excludedp", Arg.Rest add_excludedp,
    "<IDs> specify the list of excluded decision procedures (cvcl|mona|isa)");
  ]

and usage_msg =
  ("Usage:\n  " ^ Sys.argv.(0) ^ 
     " [-v] [-jast] [-ast] [-isatype] [-noverify] [-nobackground] [-method class.method] [-class class] " ^
     "<inputJavaFiles> [(-usedp | -excludedp) <IDs>]\n")
and print_usage() : unit =
  print_string usage_msg

and get_class_ident (s : string) : (string * string) list = 
  match Util.split_by "." s with
    | [cn;mn] -> [(cn,mn)]
    | _ -> 
	Util.warn ("Error parsing class.ident specification.");
	Arg.usage cmd_options usage_msg;
	[]
and add_class_method (s : string) : unit =
  add_methods (get_class_ident s)
and add_lemma (s : string) : unit =
  add_lemmas (get_class_ident s)
and set_timeout (t : int) : unit =
  (timeout := t)


(** Check if the set of current options preserves soundness *)
let check_soundness () : unit =
  let soundness_list = [(!bounded_loop_unroll, "bounded loop unrolling");
			(!simple_call_site_frames, "simplified call site frame conditions")] in
  let _ = (jahob_unsound := false) in
  let rec check lst =
    match lst with
      | [] -> ()
      | (unsound_opt_on,description)::lst1 ->
	  ((if unsound_opt_on then 
	    (Util.msg("(!) Unsound option turned on: '" ^ description ^ "'\n");
	     jahob_unsound := true)
	    else ());
	   check lst1) in
  let _ = check soundness_list in
    if !jahob_unsound then 
      Util.amsg("Jahob results are unsound due to selected verification parameters.\n")
    else ()

(** Process command line and set global variables. *)
let process() : unit =
  Arg.parse cmd_options add_javaFile usage_msg;
  check_soundness ()
