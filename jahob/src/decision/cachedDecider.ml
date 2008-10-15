open Common
open Form
open FormUtil
open Slice
open Decider
open TermRewrite
open TptpPrettyPrinter

(* debug messages *)
let debug_msg = Debug.debug_print_msg (Debug.register_debug_module "CachedDecider")

type cache_stats = {
    calls : int;
    cache_hits : int;
    total_time : float;
    max_time : float;
    max_query : form;
  }

module type Lattice =
 sig 
   type t
   val eq : t -> t -> bool
   val le : t -> t -> bool
   val join : t list -> t
   val meet : t list -> t
   val top : t 
   val bottom : t
 end

module type CachedDecider = 
  sig
    type t
    
    val decide : (t * (t -> form)) -> form -> bool
    val decide_fast : (t * (t -> form)) -> form -> bool
    val stats : unit -> cache_stats
    val max_row_length : unit -> int
    val max_row : unit -> form * (t * bool) list
    val clear_cache : unit -> unit
    val reset_stats : unit -> unit
    val	print_cache : out_channel -> unit 
  end

module Make (L : Lattice) : CachedDecider with type t = L.t =
  struct
    type t = L.t
	  
    let res_cache1 = FormHashtbl.create 1000

    let res_cache2 = FormHashtbl.create 1000

    let clear_cache () =
      FormHashtbl.clear res_cache1;
      FormHashtbl.clear res_cache2

    let calls = ref 0
    let cache_hits = ref 0
    let total_time = ref 0.0
    let max_time = ref 0.0
    let max_query = ref mk_unit

    let max_learning_attempts = ref 0
    let learn_min_length = ref 4

    (* Rewrite rule for TPTP conversion *)
    let rewrite_tptp : rewriteRule =
      let r call_back replace_map pol genv env f =
	let mk_res f = (f, []) in
	let rewrite f =
	  match f with
	  | App (Const Elem, [elem; TypedForm (Var set, _)])
	  | App (Const Elem, [elem; Var set]) ->
	      let args = match elem with
	      | App (Const Tuple, ts) -> ts
	      | _ -> [elem]
	      in App (Var set, args)
	  | App (Const Lt, args) -> App (Var "lt", args)
	  | App (Const LtEq, args) -> App (Var "lteq", args)
	  | App (Const Gt, args) -> App (Var "gt", args)
	  | App (Const GtEq, args) -> App (Var "gteq", args)
	  | _ -> f 
	in mk_res (rewrite f)
      in (r, RewriteAtoms)
	
    (** test whether the given sequent is not valid *)
    let test_notvalid env sq0 =
      let max_size = 2 in
      (* eliminate free variables *)
      let sq = elim_fv_in_seq false sq0 in
      (* rewrite tree predicate *)
      let f0 = form_of_sequent sq in
      let f1, _ = TermRewrite.rewrite true 
	  [rewrite_function_eq;
	   rewrite_tree]
	  env (TypeReconstruct.disambiguate f0)
      in
      (* instantiate rtrancl_pt for max. model size *)
      let pn, xn = (fresh_var "p", fresh_var "x") in
      let p = mk_var pn in
      let mk_step xn yn = 
	let x = mk_var xn
	and y = mk_var yn
	in mk_or [mk_eq (x, y); App (p, [x; y])] 
      in
      let rec mk_path i (yn, zs, path) =
	if i <= 0 then (yn, List.tl zs, path) else
	let zn = fresh_var "z" in
	mk_path (i - 1) (zn, zn::zs, mk_step yn zn::path)
      in
      let yn, zns, path = mk_path (max_size - 1) (xn, [], []) in
      let rtrancl_pt = 
	Binder(Lambda, [(pn, TypeUniverse); (xn, TypeUniverse); (yn, TypeUniverse)],
	       smk_exists (List.map (fun zn -> (zn, TypeUniverse)) zns, mk_and path))
      in
      let f2 = subst [(str_rtrancl, rtrancl_pt)] f1 in 
      let f3, _ = TermRewrite.rewrite false 
	  [rewrite_sets;
	   rewrite_FieldRead_FieldWrite]
	  env (unlambda f2)
      in
      let f4, env = TypeReconstruct.reconstruct_types env f3 in
      let f5, _ = TermRewrite.rewrite false [rewrite_tptp] env f4
      in
      let sqob = 
	{sqob_pos = Common.unknown_pos; 
	 sqob_purpose = ""; 
	 sqob_sq = sequent_of_form (reduce f5)}
      in
      try
	if TptpPrettyPrinter.decide_sq sqob ~prover:TptpPrettyPrinter.Paradox ~options:StringMap.empty (* TOFIX : empty is probably not what you want *)
	then None else Some false
      with _ -> None

    let cvcl_options = Common.map_of_list
	[("TimeOut", "2");
	 ("MaxQuantInst", "100");
	 ("KeepRtrancl", "no");
	 ("TryHeuristics", "no")]

    let provers = 
      [("paradox", ("Paradox", test_notvalid));
       ("mona", ("MONA", fun env sq ->
		   if Mona.prove_sequent env sq then Some true else None));
       ("cvcl", ("CVC lite", fun env sq -> 
		   if SmtPrint.cvcl_prove !CmdLine.callbohne sq cvcl_options then Some true else None))
      ];;
	
    (* TOFIX : this is a hack *)
    let usedps () = fst (List.split !CmdLine.usedps)
      
    let dispatch sq = 
      Util.filter_map (fun (id, _) -> 
	(Util.empty (usedps ()) || List.mem id (usedps ()))
	  && (Util.empty !CmdLine.excludedps || not (List.mem id !CmdLine.excludedps)))
	snd provers
 
	
    let normalize f =
      let f, env = TypeReconstruct.reconstruct_types (get_annotated_types f) f in
      let sq = sequent_of_form f in
      (sq, env)

    let reduce_query (context, fn) f =
      let sq = sequent_of_form (smk_impl (fn context, f)) in      
      let f' = reduce (unlambda (form_of_sequent (elim_fv_in_seq false sq))) in
      let rec simplify = function
	  | App (Var rtrancl, [f; t1; t2])
	    when rtrancl = str_rtrancl && equal t1 t2 
	    -> mk_true  
	  | App (Const Eq, [t1; t2]) 
	  | App (Const GtEq, [t1; t2])
	  | App (Const LtEq, [t1; t2])
	  | App (Const Subseteq, [t1; t2])
	  | App (Const Seteq, [t1; t2]) when equal t1 t2 -> mk_true
	  | App (Const Eq, [Const (BoolConst b); f])
	  | App (Const Eq, [f; Const (BoolConst b)]) ->
	      if b then simplify f else smk_not (simplify f)
	  | App (Const MetaAnd, fs) 
	  | App (Const And, fs) -> 
	      smk_and (List.map simplify fs)
	  | App (Const Or, fs) -> 
	      smk_or (List.map simplify fs)
	  | App (Const Not, [f]) -> smk_not (simplify f)
	  | App (Const Impl, [f1; f2]) 
	  | App (Const MetaImpl, [f1; f2]) -> 
	      smk_impl (simplify f1, simplify f2)
	  | Binder (Forall, vs, f) ->
	      smk_foralls (vs, simplify f)
	  | Binder (Exists, vs, f) ->
	      smk_exists (vs, simplify f)
	  | f -> f
      in simplify f'

    let cache_result context f res = 
      let _ =  debug_msg 0 (fun chan ->
	Printf.fprintf chan "Caching formula %d:\n" !calls;
	output_string chan 
	  (PrintForm.string_of_form (strip_types (reduce_query context f)) ^ "\n\n"))
      in
      FormHashtbl.add res_cache1 (reduce_query context f) res;
      FormHashtbl.add res_cache2 f (context, res)
      
    let find_cached_result (context, fn) f =
      try
	FormHashtbl.find  res_cache1 (reduce_query (context, fn) f)
      with Not_found -> 
	let cached = FormHashtbl.find_all res_cache2 f in
	Util.find_map 
	  (fun ((context', fn'), res) ->
	    if equal (fn context) (fn' context') then Some res
	    else if res then
	      if L.le context context' && equal (fn context) (fn' context)
	      then Some res else None
	    else 
	      if L.le context' context && equal (fn context) (fn' context)
	      then Some res else None
	  ) cached


    let decide_form provers (context, fn) f =
      let sq, env = normalize (smk_impl (fn context, f)) in
      let start_time = (Unix.times ()).Unix.tms_cutime in
      let res, prover_id =
	try 
	  Util.find_map 
	  (fun (prover_id, prover) -> 
	    try Util.optmap (fun res -> (res, prover_id)) (prover env sq)
	    with _ -> None) provers
	with Not_found -> (false, "")
      in
      let time = (Unix.times ()).Unix.tms_cutime -. start_time in
      total_time := !total_time +. time;
      if time > !max_time then 
	(max_time := time; 
	 let sq' = elim_fv_in_seq false sq in
	 let f = unlambda (strip_types (form_of_sequent sq')) in
	 max_query := f);
      let _ = debug_msg 0 (fun chan ->
	if res then Printf.fprintf chan "formula is valid (%s %.2fs)\n\n" prover_id time 
	else Printf.fprintf chan "formula is not valid (%s %.2fs)\n\n" prover_id time)
      in
      res
      
    let decide_and_cache fast (context, fn) f =
      let _ = incr calls in 
      let sq_f = sequent_of_form f in
      let _ = debug_msg 0 (fun chan ->
	Printf.fprintf chan "Checked formula %d:\n" !calls;
	(* let asms, conc = elim_fv_in_seq [] sq in
	let f = unlambda (FormUtil.normalize (-1) (form_of_sequent (asms, negation_normal_form (unlambda conc)))) in *)
	let sq, _ = normalize (smk_impl (fn context, f)) in
	output_string chan 
	  (PrintForm.string_of_form (strip_types (form_of_sequent sq)) ^ "\n"))
      in
      let prover sq_f =
	let f = form_of_sequent sq_f in
	let cached_sq, sigma = elim_free_vars false [] sq_f in
	let cached_f = negation_normal_form (unlambda (form_of_sequent cached_sq)) in
	let cached_fn c = subst sigma (fn c) in 
	let provers = 
	  ("test_valid", fun _ sq -> if test_valid sq then Some true else None) ::
	  if fast then [] else dispatch cached_sq
	in
	try
	  let res = 
	    if !CmdLine.usecaching then
	      find_cached_result (context, cached_fn) cached_f
	    else raise Not_found
	  in incr cache_hits; res
	with Not_found ->
          let res = decide_form provers (context, fn) f in
	  cache_result (context, cached_fn) cached_f res; res
      in
      prover sq_f
 
    (** [decide (context, fn) f] checks whether [fn context] entails [f]. 
       For soundness [fn] must be monotone. *)
    let decide = decide_and_cache false

    (** [decide_fast (context, fn) f] same as decide but potentially (more) incomplete. *)
    let decide_fast = decide_and_cache true
	 

    let stats () =
      { calls = !calls;
	cache_hits = !cache_hits;
	total_time = !total_time;
	max_time = !max_time;
	max_query = !max_query
      }	
      
    let print_cache chan =
      let print_row f _ acc =
	if not (List.mem f acc) then
	  begin
	    let row = FormHashtbl.find_all res_cache2 f in
	    output_string chan "===============\nNew cache row:\n===============\n";
	    List.iter (fun (context, res) ->
	      let f' = reduce_query context f in
	      output_string chan (PrintForm.string_of_form (smk_impl (snd context (fst context), f)) ^ "\n");
	      output_string chan (PrintForm.string_of_form f' ^ "\n");
	      if res then output_string chan "Valid\n\n"
	      else output_string chan "Not valid\n\n") row; 
	    f::acc
	  end
	else acc
      in
      ignore (FormHashtbl.fold print_row res_cache2 [])

    let reset_stats () =
      calls := 0; 
      cache_hits := 0;
      total_time := 0.0;
      max_time := 0.0;
      max_query := mk_true

    let max_row_length () = 
      let length f _ curr_max = 
	let row = FormHashtbl.find_all res_cache2 f in
	max curr_max (List.length row) in
      FormHashtbl.fold length res_cache2 0

    let max_row () =
      let res = ref (mk_true, []) in
      let max_length = max_row_length () in
      FormHashtbl.iter (fun f _ ->
	let row = FormHashtbl.find_all res_cache2 f in
	if List.length row = max_length then
	  res := (f, List.map (fun ((c, _), res) -> (c, res)) row)) res_cache2;
      !res
  end
