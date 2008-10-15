(** Output signature for functor {!Bf.Make}. *)
module type BF = 
  sig
    type var = int
    type index
    and t
	  
    (** maximal number of (unprimed) variables *) 
    val var_max : int

    (** reset variables *)
    val reset : unit -> unit	

    (** number of used variables *)
    val vars : unit -> int
	
    (** truth values *)
    val top      : t
    val bottom   : t
	
    (** operations on indices *)
    val var_index : var -> index
    val index_var : index -> var
    val prime_index : index -> index
    val unprime_index : index -> index

    (** variable constructors *)
    val new_var : unit -> var
    val mk_var : var -> t
    val mk_primed_var : var -> t
	
    (** boolean connectives *)
    val neg  : t -> t
    val conj : t -> t -> t
    val disj : t -> t -> t
    val impl : t -> t -> t
    val equi : t -> t -> t

    val upper_cube : t -> t

    (** equality, ordering functions *)
    val eq       : t -> t -> bool
    val neq      : t -> t -> bool
    val le       : t -> t -> bool
    val ge       : t -> t -> bool
    (** val compare  : t -> t -> int *)
	
    (** join and meet operations *)
    val join : t list -> t
    val meet : t list -> t

    (** relational product *)
    val rel_prod : t -> t -> t	

    (** substitutions 
       val substitute_fn : (atom -> t) -> t -> t
       val substitute : (atom * t) list -> t -> t
     *)

    (** projection *)
    val exists : var list -> t -> t 
    val forall : var list -> t -> t 
	
    val foreach_cube : t -> ((index -> int) -> unit) -> unit 

    val dom : t -> var list
	
    val unprime_all : t -> t
    val prime_all : t -> t

    val dnf : t -> index array list

    (* val size : t -> int **)
    val to_string : (var -> string) -> t -> string
    val print : out_channel -> (var -> string) -> t -> unit
  end

module Bf : BF











