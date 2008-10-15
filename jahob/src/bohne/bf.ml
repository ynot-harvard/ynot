module type BF = 
  sig
    type var = int
    type index
    and t

    val var_max : int
    val reset : unit -> unit
    val vars : unit -> int
    val top      : t
    val bottom   : t
    val var_index : var -> index
    val index_var : index -> var
    val prime_index : index -> index
    val unprime_index : index -> index
    val new_var : unit -> var
    val mk_var : var -> t
    val mk_primed_var : var -> t
    val neg  : t -> t
    val conj : t -> t -> t
    val disj : t -> t -> t
    val impl : t -> t -> t
    val equi : t -> t -> t
    val upper_cube : t -> t
    val eq : t -> t -> bool
    val neq : t -> t -> bool
    val le : t -> t -> bool
    val ge : t -> t -> bool
    val join : t list -> t
    val meet : t list -> t
    val rel_prod : t -> t -> t
    val exists : var list -> t -> t 
    val forall : var list -> t -> t 
    val foreach_cube : t -> ((index -> int) -> unit) -> unit 
    val dom : t -> var list
    val unprime_all : t -> t
    val prime_all : t -> t
    val dnf       : t -> index array list
    val to_string : (var -> string) -> t -> string
    val print : out_channel -> (var -> string) -> t -> unit
  end

module Bf =
  struct
    type var = int
    type index = int
    and t = CaddieBdd.bdd

    let var_max = 64
    let var_count = ref 0 
	
    let reset () = var_count := 0
	
    let vars () = !var_count 
	
    let bdd_mg = CaddieBdd.init 0 32 256 (var_max * 2) (* Values taken from Blast *)
	
    let _ = CaddieBdd.dynDisable bdd_mg
	
    let top = CaddieBdd.bddTrue bdd_mg
    let bottom = CaddieBdd.bddFalse bdd_mg
	
    let new_var () =
      if !var_count = var_max then 
	failwith "Maximal number of bdd variables exceeded."
      else 
	let _ = CaddieBdd.bddIthVar bdd_mg !var_count in
	let _ = CaddieBdd.bddIthVar bdd_mg (!var_count + var_max) in
	var_count := !var_count + 1; 
	!var_count - 1
	  
    let var_index v = v * 2

    let index_var i = i / 2
  
    let prime_index i = i + 1
    let unprime_index i = i - 1

    let mk_var i = 
      CaddieBdd.bddIthVar bdd_mg (var_index i)
	
    let mk_primed_var i = 
      CaddieBdd.bddIthVar bdd_mg (prime_index (var_index i))


    let neg  = CaddieBdd.bddNot
    let conj = CaddieBdd.bddAnd 
    let disj = CaddieBdd.bddOr
    let impl = CaddieBdd.bddImp
    let equi = CaddieBdd.bddBiimp 

    let eq  = CaddieBdd.bddEqual
    let neq f g = not (CaddieBdd.bddEqual f g)
    let le f g = CaddieBdd.bddEqual (impl f g) top
    let ge f g = le g f

    let join = List.fold_left disj bottom
    let meet = List.fold_left conj top

    (*
    let substitute sigma f = 
      CaddieBdd.substitute f (CaddieBdd.new_assoc (create_var (unprimed)) sigma)
    
    
    let substitute_fn s f =
      let sigma = List.fold_left 
	   (
	    fun xs x -> 
	      try
		(x,s (VarMap.find var2atom_map x))::xs 
	      with 
		Not_found -> xs
	   ) [] (CaddieBdd.support f)
      in
      CaddieBdd.substitute f (CaddieBdd.new_assoc (fun x -> x) sigma)
     *)

    let exists vs f =
      let vset = CaddieBdd.fromList bdd_mg (List.rev_map var_index vs) in
      CaddieBdd.exists vset f

    let forall vs f =
      let vset = CaddieBdd.fromList bdd_mg (List.rev_map var_index vs) in
      CaddieBdd.forall vset f
    
    let foreach_cube f fn = 
      let fn' c = fn (fun i -> c.(i)) in
      CaddieBdd.bddForeachCube f fn'

    let upper_cube f =
      let res = ref top in
      for i = 0 to !var_count - 1 do
	let vi = mk_var i in
	if le f vi then res := conj !res vi
	else if le f (neg vi) then res := conj !res (neg vi)
      done; !res
    
    let dnf f = 
      let cubes = ref [] in
      let sum_cubes c = cubes := c::!cubes in
      CaddieBdd.bddForeachCube f sum_cubes;
      !cubes

    let dom f = 
      List.rev_map index_var (CaddieBdd.bddSupportSet f)

    let to_string var2str f = 
      let cs = ref [] in
      let convert_literal c i si =
	let var = if i mod 2 = 0 then var2str (i / 2) 
	else  var2str (i / 2) ^ "'" in
	(match !c with
	| "" -> ()
	| _ when si < 2 -> c := !c ^ " & "
	| _ -> ());
	match si with
	| 1 -> c := !c ^ " " ^ var
	| 0 -> c := !c ^ "~" ^ var
	| _ -> ()
      in
      let cube2clause c =
	let clause = ref "" in
	Array.iteri (convert_literal clause) c;
	cs := !clause::!cs
      in
      let rec dnf cs = match cs with
      |	[] -> "false\n"
      |	c::[] -> "(" ^ c ^ ")\n"
      |	c::cs -> "(" ^ c ^ ")\n| " ^ (dnf cs)
      in
      if eq f top then "true\n" 
      else if eq f bottom then "false\n"
      else begin
	CaddieBdd.bddForeachCube f cube2clause;
	"  " ^ dnf !cs
      end

    let print outchan var2str f = output_string outchan (to_string var2str f)

    let unprime_all f =
      let dom_f = CaddieBdd.bddSupportSet f in
      let repl_map = List.fold_left 
	  (fun acc i -> if i mod 2 = 0 then acc else (i, unprime_index i)::acc) [] (dom_f)
      in
      let res = CaddieBdd.replace f (CaddieBdd.toMap bdd_mg repl_map) in
      res
	
    let prime_all f =
      let repl_map = List.fold_left 
	  (fun acc i -> if i mod 2 = 0 then (i, prime_index i)::acc else acc) [] (dom f)
      in
      CaddieBdd.replace f (CaddieBdd.toMap bdd_mg repl_map)
	
    let rel_prod f rel =
      let rec mk_varlist i acc = 
	if i = 0 then acc else mk_varlist (i - 1) (CaddieBdd.insertVar acc (2*i - 2))
      in
      let unprimed = mk_varlist !var_count (CaddieBdd.empty bdd_mg) in
      let f' = CaddieBdd.exists unprimed (conj f rel) in
      unprime_all f'
	
	
    (* let size f = CaddieBdd.size f **)


  end

