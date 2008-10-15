open Bf
open Bf_set
open Ast
open AstUtil
open Util
open Form
open FormUtil
open Pred
open BohneUtil
open BohneProgram
open Abstraction
 
(** Cubes of Predicates *)
type cube = Bf.t

(** Abstract states *)
type abs_state = Bf.t

(** Sets of abstract states *)
type abs_states = Bf_set.bf_set

(** Region *)
type region = {
    ppoint : program_point;
    invariants : form list;
    mutable preds : pred_decl list;
    mutable best_preds : pred_decl list;
    mutable absstates : abs_states;
    mutable parent : (guarded_command * abs_states * region ref);
    mutable succs : (guarded_command * region) list;
    mutable use_best_post : bool;
  }

(** Create the root region *)
let mk_root_region entry_point init_pred_decls invariants = 
  let rec root = 
    {ppoint = entry_point;
     invariants = invariants;
     preds = init_pred_decls;
     best_preds = 
     if !CmdLine.extra_precise then init_pred_decls
     else [];
     absstates = Bf_set.bottom;
     parent = (gc_skip (), Bf_set.top, ref root);
     succs = [];
     use_best_post = !CmdLine.extra_precise}
  in root

let is_root region = 
  let _, _, parent_ref = region.parent in
  !parent_ref == region

let region_equal r1 r2 = r1 == r2


(** Create a successor region *)
let mk_succ parent command succ_pp succ_preds src_states succ_invs =
  let inherited = List.filter (has_prop Inherit) parent.preds in
  let best_inherited = List.filter (has_prop Inherit) parent.best_preds in
  let succ_region =
    {ppoint = succ_pp;
     invariants = succ_invs;
     preds = union_preds inherited succ_preds;
     best_preds = best_inherited;
     absstates = Bf_set.bottom;
     parent = (command, src_states, ref parent);
     succs = [];
     use_best_post = parent.use_best_post}
  in
  parent.succs <- (command, succ_region) :: parent.succs;
  succ_region

let get_parent_pp r =
  let _, _, parent_ref = r.parent in
  !parent_ref.ppoint

let is_parent p r =
  let _, _, parent_ref = r.parent in 
  region_equal !parent_ref p 

(** Lfp data structure. It maps a control flow point p to the
   projection of all abstract states of regions for p. *)

type lfp_node = {
    mutable lfp_preds : pred_decl list;
    mutable lfp_absstates : (form * abs_states) list
  }

type lfp = (int, lfp_node) Hashtbl.t

let get_lfp_node lfp pp_id =
  try Hashtbl.find lfp pp_id 
  with | Not_found ->
    let new_node = {lfp_preds = []; lfp_absstates = []} in
    Hashtbl.add lfp pp_id new_node;
    new_node

let find_in_lfp lfp pp_id guard =
  try 
    let lfp_node = Hashtbl.find lfp pp_id in
    List.assoc guard lfp_node.lfp_absstates
  with Not_found -> Bf_set.bottom

let project_lfp_by_guard lfp pp_id guard =
  try
    let lfp_node = Hashtbl.find lfp pp_id in
    let abs_states =
      List.fold_left (fun acc (guard', s) -> 
	if not (entails_fast trivial_context guard' (smk_not guard))
	then Bf_set.union s acc else acc)
	Bf_set.bottom lfp_node.lfp_absstates
    in (abs_states, lfp_node.lfp_preds)
  with Not_found -> (Bf_set.bottom, [])
  
let project_lfp lfp pp_id =
  try
    let lfp_node = Hashtbl.find lfp pp_id in
    let abs_states =
      List.fold_left (fun acc (guard, s) -> 
	(guard, Bf_set.join s)::acc)
	[] lfp_node.lfp_absstates
    in (abs_states, lfp_node.lfp_preds)
  with Not_found -> ([(mk_true, Bf.bottom)], [])



let update_lfp_by_guard lfp pp_id guard new_abs_states =
  let lfp_node = get_lfp_node lfp pp_id in
  let abs_states, abs_state_list' = 
    try assoc_remove guard lfp_node.lfp_absstates
    with Not_found -> (Bf_set.bottom, lfp_node.lfp_absstates)
  in
  let abs_states' = Bf_set.union abs_states new_abs_states in
  lfp_node.lfp_absstates <- (guard, abs_states')::abs_state_list';
  abs_states'
   
let update_lfp lfp pp_id new_abs_states =
  update_lfp_by_guard lfp pp_id mk_true new_abs_states

let add_preds_to_lfp lfp pp_id new_preds =
  let lfp_node = get_lfp_node lfp pp_id in
  lfp_node.lfp_preds <- union_preds new_preds lfp_node.lfp_preds

let find_preds lfp pp_id =
  try (Hashtbl.find lfp pp_id).lfp_preds with Not_found -> []

let collect region pp =
  let rec collect acc r =
    let acc' = 
      if r.ppoint.pp_id = pp.pp_id then 
	let _, _, parent_ref = r.parent in
	assoc_replace !parent_ref.ppoint (fun s ->
	  Bf_set.union r.absstates s) r.absstates acc
      else acc
    in
    List.fold_left (fun acc (_, child) -> collect acc child) acc' r.succs
  in
  List.rev_map (fun (_, s) -> Bf_set.join s) (collect [] region)


(** Remove the subtree starting in [region] from the region tree *)
let remove_subtree helper acc region =
  let rec traverse acc todo =
    match todo with
    | r::todo' ->
	let _, _, parent_ref = r.parent in
	r.succs <- [];
	if not (is_root r) then r.absstates <- Bf_set.bottom;
	traverse (helper acc r) (List.fold_left (fun acc (_, child) -> child::acc) todo' r.succs)
    | [] -> acc
  in traverse acc [region]

(** Recompute the lfp data structure *)
let recompute_lfp lfp root_region =
  Hashtbl.clear lfp;
  let rec traverse todo =
    match todo with
    | r::todo' ->
	let gc, src_states, parent_ref = r.parent in
	add_preds_to_lfp lfp r.ppoint.pp_id r.preds;
	if not (is_root r) then
	  ignore (update_lfp_by_guard lfp !parent_ref.ppoint.pp_id gc.gc_guard src_states);
	traverse (List.fold_left (fun acc (_, child) -> child::acc) todo' r.succs)

    | [] -> ()
  in traverse [root_region]

(** Add predicates to a region *)
let add_preds lfp region preds =
  region.preds <- union_preds preds region.preds;
  add_preds_to_lfp lfp region.ppoint.pp_id preds
