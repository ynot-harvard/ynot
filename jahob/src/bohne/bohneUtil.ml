open Util
open Form
open FormUtil
open Slice

let rec split_conjuncts f =
  match f with 
  | App (Const And, fs) ->
      List.concat (List.rev_map split_conjuncts fs)
  | App (Const Impl, (g::fs)) ->
      List.rev_map (curry smk_impl g)
      (List.concat (List.rev_map split_conjuncts fs)) 
  | _ -> [f]

let phase s fn x =
  Util.msg (s ^ "..."); 
  (if not !Util.verbose then Util.amsg(" (b)"));
  let res = fn x in
  Util.msg "done.\n";
  res

let normalize_form keep f0 = 
  let sq = sequent_of_form f0 in
  (* let (asms, conc) = slice [slice_obj_sets] env sq in *)
  let asms, conc = elim_fv_in_seq keep sq in
  unlambda (smk_impl (smk_and asms, conc)) 

let free_object_vars f =
  let filter env = 
    Util.filter_map (fun (_, ty) -> ty = mk_object_type) fst env
  in
  filter (get_annotated_types (normalize_form false f))

open Bf
open CachedDecider

module BfL = (Bf : Lattice with type t = Bf.t)

module BfCachedDecider = Make(BfL)

let trivial_context = (Bf.top, fun _ -> mk_true)

module type PrioQueueElem =
  sig
    type el
    type context 

    val equal : el -> el -> bool
    val compare : context -> el -> el -> int
  end

module type PrioQueue =
  sig
    type el
    type context 
    type queue      
    val empty : queue
    val insert : context -> queue -> el -> queue
    val extract : context -> queue -> el * queue
    val remove : context -> (el -> bool) -> queue -> queue
  end
    
module PriorityQueue(Elem : PrioQueueElem) : (PrioQueue with type el = Elem.el and type context = Elem.context) =
   struct
     type el = Elem.el
     type context = Elem.context
     type queue = Empty | Node of el * queue * queue
     let empty = Empty
     
     let raise_empty () = raise (Failure "Priority queue: tried to extract from an empty queue")
	 
     let insert c queue elt =
       let rec insert queue elt =
       match queue with
         Empty -> Node(elt, Empty, Empty)
       | Node(e, left, right) ->
           let comp_res = Elem.compare c elt e in
	   if comp_res < 0  
           then Node(elt, insert right e, left)
           else if comp_res > 0 || not (Elem.equal e elt) then 
	     Node(e, insert right elt, left)
	   else queue
       in insert queue elt

     let remove_top c = 
       let rec remove_top = function
	 | Empty -> raise_empty ()
	 | Node(elt, left, Empty) -> left
	 | Node(elt, Empty, right) -> right
	 | Node(elt, (Node(lelt, _, _) as left),
                (Node(relt, _, _) as right)) ->
		  if Elem.compare c lelt relt < 0
		  then Node(lelt, remove_top left, right)
		  else Node(relt, left, remove_top right)
       in remove_top

     let remove c remove_it = 
       let rec remove = function
	 | Empty -> Empty
	 | Node (elt, left, right) ->
	     let left' = remove left in
	     let right' = remove right in
	     if remove_it elt then remove_top c (Node (elt, left', right'))
	     else Node (elt, left', right')
       in remove

     let extract c = function
       | Empty -> raise_empty ()
       | Node(elt, _, _) as queue -> (elt, remove_top c queue)
   end
