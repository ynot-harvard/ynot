(** Decision procedure dispatcher. *)

open Common
open Form
open FormUtil
open PrintForm
open SmtPrint
open TermRewrite
open MonaConvert
open TypeReconstruct
open Slice
open TptpPrettyPrinter

(** Debug messages **)
let debug_lmsg = Debug.debug_lmsg (Debug.register_debug_module "Decider")

let stats = Hashtbl.create 10
let incr_prover_stat (prover : string) (successful : bool) : unit = 
  let total, success = try Hashtbl.find stats prover with Not_found -> 0,0 in
    Hashtbl.replace stats prover (total+1, success + if successful then 1 else 0)

let start (name : string) : unit = 
  Isabelle.start name ;
  Coq.start name ;
  TptpPrettyPrinter.start name

(* This procedure returns true if the proof obligation is found among the assumptions. *)
let trivially_true ((assumptions, po) : sequent) : bool =
  let rec trivially_true_rec (al0 : form list) (po0 : form) : bool =
    match al0 with
      | [] -> false
      | a0 :: arest -> 
	  let a1 = FormUtil.remove_comments (FormUtil.remove_typedform a0) in
	  let trivial = (a1 = po0) in
	    if trivial then
	      Util.msg "Trivially true.\n";
	    trivial || (trivially_true_rec arest po0)
  in
  let po0 = FormUtil.remove_comments (FormUtil.remove_typedform po) in
    (trivially_true_rec assumptions po0)

(* Simple syntactic validity checker *)
let test_valid ((asms, conc) : sequent) : bool =
  let rec le f1 f2 =
    match (f1, f2) with
    (* Reachability *)
    (* f1 --> rtrancl_pt r t t *)
    | (_, App (Var "rtrancl_pt", [_; t1; t2])) 
      when equal t1 t2 -> true
    | (App (Const Eq, [t1'; t2']), App (Var "rtrancl_pt", [_; t1; t2])) 
      when (equal t1 t1' && equal t2 t2' || equal t1 t2' && equal t2 t1') -> 
	true 
    | (App (Const Eq, [t1'; t2']), App (Var "rtrancl_pt", [r; t1; t2])) ->
	(match r with
	| Binder (Lambda, [(v1, _); (v2, _)], f) ->
	    le f1 (subst [(v1, t1); (v2, t2)] f)
	| _ -> false)
    | (App (Var "rtrancl_pt", [r; t1; t2]), App (Var "rtrancl_pt", [r'; t1'; t2'])) ->
	equal r r' && equal t2 t2' && (equal t1 t1' ||
	match r' with 
	| Binder (Lambda, [(v1, _); (v2, _)], f) ->
	    le (mk_eq (t1, mk_var v2)) (subst [(v1, t1')] f)
	| _ -> false)
    (* Equality *)
    | (App (Const Eq, _), App (Const GtEq, [t21;t22])) 
    | (App (Const Eq, _), App (Const LtEq, [t21;t22])) 
    | (App (Const Eq, _), App (Const Not, [App (Const Lt, [t21;t22])])) 
    | (App (Const Eq, _), App (Const Not, [App (Const Gt, [t21;t22])])) ->
	le f1 (App (Const Eq, [t21;t22]))
    | (App (Const Lt, [t21;t22]), App (Const Not, [App (Const Eq, _) as f2']))
    | (App (Const Gt, [t21;t22]), App (Const Not, [App (Const Eq, _) as f2'])) ->
	le f2' (App (Const Eq, [t21;t22]))	      
    | (App (Const Eq, [t11;t12]), App (Const Eq, [t21;t22])) ->
	(equal t21 t22 || equal t11 t21 && equal t12 t22 || equal t11 t22 && equal t12 t21) || 
	begin
	  match (t11, t12, t21, t22) with
	  | (App (f1, [t1]), App (f2, [t2]), _, _) when equal f1 f2 ->
	      le (App (Const Eq, [t1;t2])) f2
	  | (_, _, App (f1, [t1]), App (f2, [t2])) when equal f1 f2 ->
	      le (App (Const Eq, [t1;t2])) f1
	  |	_ -> false
	end
      | (_, App (Const Eq, [t1; t2])) 
      | (_, App (Const GtEq, [t1; t2])) 
      | (_, App (Const LtEq, [t1; t2])) -> equal t1 t2
      (* Boolean operators *)
      | (Const (BoolConst false), _) -> true
      | (_, Const (BoolConst true)) -> true
      | (App (Const And, conj), _) ->
	  List.exists (fun c -> le c f2) conj
      | (_, App (Const And, conj)) ->
	  List.for_all (fun c -> le f1 c) conj
      | (_, App (Const Not, [App (Const And, conj)])) ->
	  List.exists (fun d -> le f1 (mk_not d)) conj
      | (_, App (Const Or, disj)) ->
	  List.exists (fun d -> le f1 d) disj
      |  (App (Const Not, [f1']), App (Const Not, [f2'])) ->
	  le f2' f1'
      (* Quantifiers *)
      | (Binder (Exists, _, f1'), _) -> le f1' f2
      | (_, Binder (Forall, _, f2')) -> le f1 f2'
      | (Binder (b1, [(v1, t1)], f1'), Binder (b2, [(v2, t2)], f2'))
	when b1 = b2 && normalize_type t1 = normalize_type t2 && v1 = v2 -> le f1' f2'
      | _ -> equal f1 f2	   
  in
    (trivially_true (asms, conc)) ||
      (let asms, conc = elim_fv_in_seq false (asms, conc) in
       let asms = negation_normal_form (unlambda (normalize (-1) (mk_and asms))) in
       let conc = negation_normal_form (unlambda (normalize (-1) conc)) in
       le asms conc)

let provers = 
  [("test_valid",
    ("Built-in validity checker",
    fun _ _ sqob _ -> test_valid sqob.sqob_sq));
   ("mona", 
    ("MONA",
     fun env _ sqob _ ->
	slice_and_prove 
	 [slice_default; slice_obj_vars; slice_obj_sets] 
	 env (Mona.prove_sequent env) sqob.sqob_sq));
   ("e", 
    ("E", 
     fun _ k sqob options -> TptpPrettyPrinter.decide_sq sqob ~prover:E ~options)) ;  
   ("vampire", 
    ("Vampire", 
     fun _ k sqob options -> TptpPrettyPrinter.decide_sq sqob ~prover:Vampire ~options)) ;
   ("spass", 
    ("SPASS", 
     fun _ k sqob options -> SpassPrettyPrinter.decide_sq sqob ~options)) ;
   ("cvcl", 
    ("CVC Lite", 
     fun _ _ sqob options -> cvcl_prove false sqob.sqob_sq options));
   ("cvclHack", 
    ("CVC Lite (with TPTP's FOL translation)", 
     fun _ _ sqob options -> cvcl_prove false (FolTranslation.awful_hack ~options sqob.sqob_sq) options));
   ("isa", 
    ("Isabelle", 
     fun _ k sqob options -> Isabelle.decide_sq sqob k ~options));
   ("coq", 
    ("Coq", 
     fun _ k sqob options -> Coq.decide_sq sqob k ~options)) ;
   ("paradox", 
    ("Paradox - A first-order model finder (for debugging only)", 
     fun _ k sqob options -> TptpPrettyPrinter.decide_sq sqob ~prover:Paradox ~options))
  ]

let default_prover_choice = 
  ListLabels.map ~f:(fun (name, _) -> (name, StringMap.empty)) provers

(*
let _ = if (List.map fst provers) != CmdLine.prover_names then
  Util.fail "Error in decider.ml: prover names in command line are not up to date."
*)

let used_provers () : (string * options_t) list =
  let usedps = !CmdLine.usedps in
    if usedps = [] then
      default_prover_choice
    else
      ("test_valid", StringMap.empty) :: (List.rev usedps)

let print_stats () = 
  let acc_s = ref 0 in
  let total = try fst (Hashtbl.find stats "Built-in validity checker") with Not_found -> 0 in
  if total > 0 then begin  
    print_string "\n=======================================\n";
    List.iter (fun (prover, _) -> 
		 let prover_name, _ = List.assoc prover provers in
		 let (total, success) = try Hashtbl.find stats prover_name with Not_found -> (0, 0) in
		   Printf.printf "%s proved %d out of %d sequents.\n" prover_name success total;
		   acc_s := !acc_s + success) (used_provers ());
    Printf.printf "=======================================\n\nA total of %d sequents out of %d proved.\n" !acc_s total
  end

let stop () : unit = 
  Isabelle.stop () ;
  Coq.stop () ;
(*  TptpPrettyPrinter.stop () *)
  print_stats () 

(** Print and parse formula again.
    Used for debugging; should not be necessary. *)
let reparse (f : form) : form = 
  let formula_string = 
    PrintForm.string_of_form f in
    ParseForm.parse_formula formula_string

let generate_sequents (env:typeEnv) (f:form) : sequentenv list =
  let rec add (hyps : (form * string) list) (asms : form list) = match hyps with
    | [] -> asms
    | (App(Const And,fs),c)::hyps1 -> add ((List.map (fun f -> (f,c)) fs) @ hyps1) asms
    | (App(Const MetaAnd,fs),c)::hyps1 -> add ((App(Const And,fs),c)::hyps1) asms
    | (App(Const Comment,[Const (StringConst c);h]),c0)::hyps1 -> 
	add ((h,c ^ c0)::hyps1) asms
    | (hyp,c)::hyps1 -> add hyps1 (mk_comment c hyp::asms)
  and add_one hyp asms = add [(hyp,"")] asms
  in
  let rec gen comments env asms f acc = match f with
  | App(Const Comment,[Const (StringConst c);f1]) -> gen (c::comments) env asms f1 acc
  | App(Const Impl,[f1;f2]) -> gen comments env (add_one f1 asms) f2 acc
  | App(Const MetaImpl,[f1;f2]) -> gen comments env (add_one f1 asms) f2 acc
  | App(Const And,fs) -> gens comments env asms fs acc
  | App(Const MetaAnd,fs) -> gens comments env asms fs acc
  | Binder(Forall,vts,f1) -> gen comments (vts @ env) asms f1 acc
  | _ -> 
      let cf = mk_comment (String.concat "_" comments) f in
      ((List.rev asms,cf), env)::acc
  and gens comments env asms fs acc = List.fold_right (gen comments env asms) fs acc
  in 
  let res = gen [] env [] f [] in
  res

let exc_to_bool (prover : string) (f : 'a -> bool) (x : 'a) : bool =
  let failed_with exn = 
    Util.warn ("Prover '" ^ prover ^ "' failed with " ^ exn ^ ".\n");
    false
  in
  try (f x) with 
    | Failure s 
    | Sys_error s -> failed_with ("error " ^ s)
    | Not_found -> failed_with "Not_found"
    | ex -> failed_with "unknown exception"

let get_min_sq
    prover
    (env : typeEnv)
    (goal : form) 
    (asms : form list) : form list =
  let rec get_min_sq asms (useful_asms : form list) =
    match asms with
    | [] -> useful_asms
    | f::asms1 ->
	let sqob = 
	  {sqob_pos = Common.unknown_pos; 
	   sqob_purpose = ""; 
	   sqob_sq = (List.rev_append useful_asms asms1, goal)}
	in 
	if prover sqob	    
	then get_min_sq asms1 useful_asms
	else get_min_sq asms1 (f::useful_asms)
  in get_min_sq asms []

let print_minimal_sequent
    prover
    (env : typeEnv) 
    (sqob : sq_obligation) : unit =
  let asms, goal = sqob.sqob_sq in
  let min_asms = get_min_sq prover env goal asms in
  let min_sq = (List.map strip_types min_asms, strip_types goal) in
    Util.amsg ("\nMinimal sequent is:\n" ^ string_of_sequent min_sq)

let prove_sqob_with ((prover_id : string), (options : options_t))
    (sqob : sq_obligation) (env : typeEnv) (k : int) : bool = 
  let pmsg str =
    if !Util.verbose then Util.msg str 
    else Util.amsg "."
  in
  try
    let name, prover = List.assoc prover_id provers in
    let _ = Util.msg ("Running " ^ name ^ "... ") in
    let save_prover : sq_obligation -> bool = exc_to_bool name (fun f -> prover env k f options) in
    let res : bool = save_prover sqob in
      incr_prover_stat name res;
      let _ = 
	if res then begin
	  pmsg (name ^ " proved formula.\n");
	  if !CmdLine.minasm 
	  then print_minimal_sequent save_prover env sqob
	end
	else pmsg (name ^ " failed to prove formula.\n")
      in res
  with Not_found -> 
    Util.warn ("Unknown prover \"" ^ prover_id ^ "\"");
    false

let prove_sqob (sqob : sq_obligation) (env : typeEnv) (k : int) : bool =
  let sq = sqob.sqob_sq in
  let vc_string = string_of_sequent sq in
  let pmsg str =
    Util.msg str; Util.amsg "."
  in
    pmsg ("\nProof obligation: " ^ vc_string ^ "\n");
    let used_provers = used_provers () in
    let res = List.exists (fun prover -> prove_sqob_with prover sqob env k) used_provers in
    let _ = 
      if not res then 
	Util.amsg ("All provers failed on proof obligation: '" ^ extract_comments (snd sq) ^ "'\n")
      else 
	() 
    in
      res
    
let split_and_decide (ob : obligation) : bool = 
  let f0 = ob.ob_form in
  let f, env = TypeReconstruct.reconstruct_types [] f0 in
  let sqs = generate_sequents env f in
  let len = List.length sqs in
  let rec prove_all sqs k = 
    match sqs with
      | [] -> true
      | (sq, env)::sqs1 -> begin	  
          debug_lmsg 0 (fun () -> (Printf.sprintf "\nProving sequent %d of %d.   " k len));
	  let kstr = Printf.sprintf "%d" k in
	    let sqob = { 
	      sqob_sq = sq; 
	      sqob_purpose = ob.ob_purpose ^ kstr; 
	      sqob_pos = ob.ob_pos;
	    } in
	    let ok = prove_sqob sqob env k in
              if ok then 
		prove_all sqs1 (k+1)
              else 
		(if !CmdLine.failfast then false
		  else let _ = prove_all sqs1 (k+1) in false)
	end
  in
  prove_all sqs 1
    
let ob_valid (oblig : obligation) : bool =
  if !CmdLine.verify then split_and_decide oblig
  else false
    
let valid (f : form) : bool =
  ob_valid (form_to_oblig f)
    
(*
  Bapa.lashIsUnsatisfiable f
  Bapa.valid f 
*)
