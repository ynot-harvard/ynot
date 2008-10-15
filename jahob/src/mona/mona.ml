(* Interface to MONA. *)

let infile  = Util.tmp_name "in.mona"
let failfile  = Util.tmp_name "fail.mona"
let outfile = Util.tmp_name "mona-out.txt"
let mona = "mona"
let valid_formula = "Formula is valid"
let invalid_formula = "Formula is unsatisfiable"
let counter_example = "A counter-example"

open Util
open MonaForm
open MonaConvert
open MonaPrint

(* debug messages *)

let debug_msg = Debug.debug_msg (Debug.register_debug_module "Mona")

let fileToLine fn =
  let chn = open_in fn in
  let str = input_line chn in
  close_in chn;
  str
  
type lineParseResult = Nothing | ParsedLine of string      
    
let parse_line s = 
  if String.contains s '=' then ParsedLine s
  else Nothing
      
let parse_counterexample fn = 
  let chn = open_in fn in
  let firstLine = input_line chn in
  let expectedStr = "A counter-example of least length" in
  let leftContains str substr = 
    try (String.sub str 0 (String.length substr) = substr) with
      Invalid_argument _ -> false in
  let res = ref "\nFailed to retrieve a counterexample.\n" in
  let line = ref "" in
  if leftContains firstLine expectedStr then begin
    try begin        
      while (parse_line !line = Nothing) do
        line := input_line chn
      done;
      res := !line ^ "\n";
      while (parse_line !line <> Nothing) do
        (match (parse_line !line) with
          ParsedLine s -> res := !res ^ s ^ ", "
        | Nothing -> fail "Mona.parseCounterexample: BUG");
        line := input_line chn
      done;
      res := !res ^ "\n"
    end with End_of_file -> ()
  end else ();
  close_in chn;
  !res

    
let parse_output_valid str =
  if str = valid_formula then true
  else if str = invalid_formula then false
  else if (try (String.sub str 0 (String.length counter_example) = counter_example) with
    Invalid_argument _ -> false) then false
  else begin
    Sys.rename infile failfile;
    fail ("Error when calling MONA: " ^ str)
  end  

let run_mona prog =
  let chn = open_out infile in
  let _ = print_prog chn prog; close_out chn in
  let _ = run_with_timeout 
      (mona ^ " -q " ^ infile ^ "> " ^ outfile) 
      !CmdLine.timeout 
  in ()

let mona_valid =
  let regexp = Str.regexp "counter-example of least length (\\([0-9]+\\))" in
  let match_size s = 
    try ignore (Str.search_forward regexp s 0); true with Not_found -> false
  in 
  fun mode preamble f ->
  let _ = run_mona (mode, preamble@[FormDecl f]) in 
  let result_string = fileToLine outfile in
  let res = parse_output_valid result_string in
  if not res && match_size result_string then 
    debug_msg ("size of counter-model: " ^ Str.matched_group 1 result_string ^ "\n");
  res
   
let get_counterexample mode all_sets decls f =
  parse_counterexample outfile

let valid env derived bb_fields f =
  let mode, preamble, f' = convert env derived bb_fields f in
  let res = match f' with
      |	Atom True -> true
      |	Atom False -> false
      |	_ -> mona_valid mode preamble f'
      in
  res
    
open Form
open FormUtil


let prove_sequent env (fs0, g0) =
  let (fs,g) = (List.map remove_comments fs0, remove_comments g0) in
  (* let env = fv (mk_impl (mk_and fs, g)) in *)
  let _ = Debug.lmsg 4 (fun () -> "Mona proving sequent:\n" ^ string_of_sequent (fs,g) ^ "\n") in
  let has_field_type fld = 
    let is_object_type ty = match ty with
    | TypeApp (TypeObject, []) -> true
    | _ -> false
    in
    try match List.assoc fld env with
    | TypeApp (TypeArray, [ty1; ty2]) 
    | TypeFun ([ty1], ty2)
      -> is_object_type ty1 && is_object_type ty2
    | _ -> false
    with Not_found -> false 
  in
  let fs, g  = elim_fv_in_seq false (fs, g) in  
  let fail msg = raise (Invalid_argument msg) in
  try
    let _ = Debug.lmsg 4 (fun () -> "sequent after elimination of free variables:\n" ^ string_of_sequent (fs,g) ^ "\n") in
    (* get field constraints and backbone fields from antecedent *)
    let fcs, bb_fields, fs' = List.fold_right (fun f (fcs, bb_fields, fs') ->
      match normalize 4 f with
      (* match field constraints *)
      | Binder (Forall, [(x1, _); (y1, _)], App(Const Impl, [App (Const Eq, [App (Var fld, [Var x2]); Var y2]); fld_def]))
	when x1 = x2 && y1 = y2 ->
	  if has_field_type fld then ((fld, f) :: fcs, bb_fields, fs') 
	  else (fcs, bb_fields, f::fs')
      (* match backbone fields *)
      | App (Var str_tree, [App (Const ListLiteral, fields)])
	-> let bb_fields' = List.fold_left (fun bb_fields' -> 
	  function | (Var fld) -> 
	    if has_field_type fld then fld :: bb_fields'
	    else fail (Printf.sprintf "Tried to declare a backbone field which is not of type field:\n    %s :: %s." 
			 fld (PrintForm.string_of_type (try List.assoc fld env with Not_found -> TypeUniverse)))
	| _ -> fail "Only atomic backbone fields supported.") [] fields 
	in 
	if empty (difference bb_fields bb_fields') then (fcs, bb_fields', fs')
	else if empty (difference bb_fields' bb_fields) 
	then (fcs, bb_fields, fs')
	else 
	  (Util.warn "Found multiple tree declarations in antecedent, using the last one.";
	   (* We could instead check which one intersects more free variables.
	      Currently we take the last one, which is usually what we want. *)
	   (fcs, bb_fields', fs')
	  )
      | _ -> (fcs, bb_fields, f :: fs')) fs ([], [], [])
    in
    (* generate missing field constraints *)
    let fcs' = 
      let x = "x" and y = "y" in
      List.fold_left (fun fcs' (v, ty) ->
	if has_field_type v then
	  let is_derived = List.exists (fun (v', _) -> v' = v) fcs'
	  and is_backbone = List.mem v bb_fields in
	  if not (is_derived || is_backbone) then
	    let fc = Binder (Forall, [(x, mk_object_type); (y, mk_object_type)], 
			     App(Const Impl, [App (Const Eq, [App (Var v, [Var x]); Var y]); mk_true]))
	    in ((*Util.warn ("Added trivial field constraint for field: " ^ v); *)
		(v, fc) :: fcs')
	  else if is_derived && is_backbone then
	    fail ("Found field constraint and backbone declaration for field: " ^ v)
	  else fcs'
	else fcs') fcs env
    in 
    let derived, env = List.fold_right (fun (v, ty) (derived, env) -> 
      try (((v, ty), Some (List.assoc v fcs'))::derived, env)
      with Not_found -> (derived, (v, ty)::env)) env ([], [])
    in
    (*
       let _ = List.iter (fun ((v, ty), _) -> Printf.printf "%s :: %s\n" v (PrintForm.string_of_type ty)) (derived @ env) in
     *)
   valid env derived bb_fields (smk_impl (smk_and fs', g))
  with 
    | Invalid_argument msg -> Util.msg ("Failed to prove sequent:\n" ^ msg); false
    | End_of_file -> Util.msg ("Failed to complete proof of sequent in given time:\n" ^ string_of_sequent (fs, g)); false

