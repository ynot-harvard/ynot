(** Abstract data type for sets of boolean functions *)

(* needs to be replaced by an implementation that canonically represents *)
(* sets in an efficient way -- currently using lists *)

module type BF_SET = 
  sig
    type bf = Bf.Bf.t
    type bf_set

    val top    : bf_set
    val bottom : bf_set
	
    val join : bf_set -> bf
    val singleton : bf -> bf_set
    val add   : bf_set -> bf -> bf_set
    val conj  : bf_set -> bf -> bf_set
    val union : bf_set -> bf_set -> bf_set
    val inter : bf_set -> bf_set -> bf_set
    val diff  : bf_set -> bf_set -> bf_set


    val eq    : bf_set -> bf_set -> bool
    val le    : bf_set -> bf_set -> bool
    val ge    : bf_set -> bf_set -> bool

    val map   : (bf -> bf) -> bf_set -> bf_set
    val iter  : (bf -> unit) -> bf_set -> unit 
    val find  : (bf -> bool) -> bf_set -> bf 
    val fold   :('a -> bf -> 'a) -> 'a -> bf_set -> 'a

    val filter : (bf -> bool) -> bf_set -> bf_set
    val partition : (bf -> bool) -> bf_set -> bf_set * bf_set

    val print : out_channel -> (Bf.Bf.var -> string) -> bf_set -> unit
  end

module Bf_set =
  struct
    open Bf
    type bf = Bf.t
    and bf_set = bf list

    let top = [Bf.top]
    and bottom = [Bf.bottom]
      
    let le fs gs = List.for_all (fun f -> List.exists (Bf.le f) gs) fs
    let eq fs gs = le fs gs && le gs fs
    and ge fs gs = le gs fs

    let map fn fs = 
      let check_and_filter f fs =
	List.fold_left 
	  (fun (t, rs) g -> 
	    let t'  = t || (Bf.le f g && not (Bf.eq f g))
	    and rs' = if Bf.le g f then rs else g::rs in 
	    (t',rs')) (false, []) fs in 
      List.fold_left 
	(fun res g ->
	  let g' = fn g in
	  let (t, res') = check_and_filter g' res in
	  if t then res' else g'::res')
	[] fs

    and iter = List.iter
	
    and find = List.find

    and fold = List.fold_left

    and filter p fs = 
      match List.filter p fs with
      |	[] -> bottom
      |	fs' -> fs'

    and partition p fs = 
      let p_fs, notp_fs = List.partition p fs in
      let p_fs' = match p_fs with [] -> bottom | _ -> p_fs
      and notp_fs' = match notp_fs with [] -> bottom | _ -> notp_fs
      in (p_fs', notp_fs')

    let simplify = map (fun x -> x)
    
    and singleton f = [f]

    and join = List.fold_left Bf.disj Bf.bottom  

    and add fs f = 
      if List.exists (Bf.le f) fs then fs 
      else f::List.filter (fun g -> not (Bf.le g f)) fs
		
    let union fs gs = simplify (fs @ gs)
	
    and conj fs f = map (Bf.conj f) fs
	
    let inter fs = 
      List.fold_left (fun res f -> union (List.map (Bf.conj f) fs) res) []

    let diff fs gs =
      List.filter (fun f -> not (le (singleton f) gs)) fs
	
    and print outchan var2str = 
      output_string outchan (String.make 80 '-' ^ "\n"); 
      List.iter (fun f -> Bf.print outchan var2str f; 
	output_string outchan (String.make 80 '-' ^ "\n"))
  end


