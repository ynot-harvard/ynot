open Util
open Form
open FormUtil
open PrintForm

let slice_and_prove 
    slice_rules 
    (env : typeEnv) 
    (prover : sequent -> bool)
    ((asms, conc) : sequent) =
  let debug_msg asms' =
    if !Debug.debugOn then
      let rest = List.filter (fun x -> not (List.mem x asms')) asms in
      if not (Util.empty rest) then begin
	Debug.lmsg 0 (fun () -> "\n");
	Debug.lmsg 0 (fun () -> "Trying to prove:\n"
	^ string_of_sequent (asms', conc) ^ "\n")
      end
  in
  let dbprover ((asms, _) as sq) =
    debug_msg asms; prover sq
  in
  let rec sp slice_rules keep =
    match slice_rules with
    | sr::slice_rules' ->
	let keep' = sr env (keep, conc) in
	(sp slice_rules' keep' || dbprover (keep', conc))
    | [] -> false
  in sp slice_rules asms
     

let slice slice_rules env (asms, conc) =
  let asms' = 
    if conc = mk_false then asms
    else List.fold_left (fun asms' sr -> sr env (asms', conc)) asms slice_rules in
  (asms', conc)


let slice_default env (asms, conc) =
  let get_def f = match normalize 1 f with
  | App (Const Eq, [Var v; rhs]) 
  | App (Const Eq, [rhs; Var v]) ->
      if is_set_type (List.assoc v env) then
	Some (v, rhs)
      else None
  | App (Const Elem, [Var v; rhs]) -> Some (v, rhs)
  | _ -> None
  in
  let rec strip acc asms signifv =
    let keep hyp (acc', rest, signifv') =
      match get_def hyp with
      | Some (v, rhs) ->  
	  let fv_rhs = fv rhs in
	  let fv_asms = fv (mk_and (List.map (fun f -> safe_unsome f (optmap snd (get_def f))) asms)) in
	  if List.exists (fun v -> List.mem v signifv') fv_rhs
	  then (hyp::acc', rest, union [v] signifv')
	  else if List.mem v signifv' || List.mem v fv_asms 
	  then (hyp::acc', rest, signifv')
	  else (acc', hyp::rest, signifv') 
      | None -> (hyp::acc', rest, signifv') 
    in	  
    let acc', asms', signifv' = List.fold_right keep asms ([], [], signifv) in 
    match acc' with
    | [] -> acc
    | _ -> strip (acc' @ acc) asms' signifv'
  in
  strip [] asms (fv conc)

let slice_obj_vars env (asms, conc) =
  let fv_by_type = fv_by_type env in
  let signif_objs = ref (fv_by_type [mk_object_type] conc) in
  let add_significant vs =
    List.iter (fun x -> 
      if not (List.mem x !signif_objs)
      then signif_objs := x::!signif_objs) vs
  in
  let asms' = List.map (fun f -> (f, fv_by_type [mk_object_type] f)) asms in
  let keep, dont_knows = 
    List.partition (fun (hyp, objs) ->
      let objsets = fv_by_type [mk_set_type mk_object_type] hyp in
      Util.empty objs) asms' 
  in
  let rec filter asms acc =
    let keep (hyp, objs) = 
      let res = List.exists (fun x -> List.mem x !signif_objs) objs
      in if res then add_significant objs; res
    in 
    let signif, rest = List.partition keep asms in
    match signif with
    | [] -> acc
    | _ -> filter rest (List.rev_append (List.map fst signif) acc)
  in
  filter dont_knows (List.map fst keep)

let slice_obj_vars2 env (asms, conc) =
  let fv_by_type = fv_by_type env in
  let signif_objs = ref (fv_by_type [mk_object_type] conc) in
  let add_significant vs =
    List.iter (fun x -> 
      if not (List.mem x !signif_objs)
      then signif_objs := x::!signif_objs) vs
  in
  let asms' = List.map (fun f -> (f, fv_by_type [mk_object_type] f)) asms in
  let keep, dont_knows = 
    List.partition (fun (hyp, objs) ->
      let objsets = fv_by_type [mk_set_type mk_object_type] hyp in
      Util.empty objs) asms' 
  in
  let test (hyp, objs) = 
    List.exists (fun x -> List.mem x !signif_objs) objs
  in 
  List.rev_map fst keep @ Util.filter_map test fst dont_knows
  

let slice_obj_sets env (asms, conc) =
  let fv_by_type = fv_by_type env in
  let conc_objsets = fv_by_type [mk_set_type mk_object_type] conc in   
  let asms' = List.map (fun f -> (f, fv_by_type [mk_object_type] f)) asms in
  List.fold_right (fun (hyp, objs) asms ->
    let objsets = fv_by_type [mk_set_type mk_object_type] hyp in
    if Util.empty objsets ||
    List.exists (fun x -> List.mem x conc_objsets) objsets
    then hyp::asms else asms) asms' []
