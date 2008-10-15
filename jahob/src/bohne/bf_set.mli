(** Abstract data type for sets of boolean functions *)

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
      
module Bf_set : BF_SET









