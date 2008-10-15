(** Generate some random BAPA formulas for testing purposes. *)

open Alpha

(*
let genBapa (nsetvars : int) (nintvars : int) (size : int) : form =
*)


(*
  randomly choose n elements from a list
*)
let randomChoices (inputs0 : 'a list) (n : int) : 'a list =
  let inputs = Array.of_list inputs0 in
  let l = Array.length inputs in
    if n >= l then
      inputs0
    else
      begin
	let seens = Array.make l false in
	let outputs = ref ([] : 'a list) in
	  for i = 0 to n - 1 do
	    let s = ref (Random.int l) in
	      while seens.(!s) do
		s := Random.int l
	      done;
	      Array.set seens !s true;
	      outputs := (Array.get inputs !s) :: !outputs
	  done;
	  List.rev !outputs
      end
    
(*
  generate random set term at "size"
  vars needs to contain at least one element
*)
let rec genSets (vars : ident list) (size : int) : setTerm list =
  if size = 0 then
    [Setvar (List.nth vars (Random.int (List.length vars)))]
  else
    let res = ref [] in
    let n = max 1 (Random.int size) in
      for i = 0 to n - 1 do
	res := (genSetTerm vars (size - 1)) :: !res
      done;
      !res

and genSetTerm (vars : ident list) (size : int) : setTerm =
  if size = 0 then
    Setvar (List.nth vars (Random.int (List.length vars)))
  else
    match Random.int 6 with
      | 0 -> Setvar (List.nth vars (Random.int (List.length vars)))
      | 1 -> Emptyset
      | 2 -> Fullset
      | 3 -> Complement (genSetTerm vars (size - 1))
      | 4 -> Union (genSets vars (size - 1))
      | _ -> Inter (genSets vars (size - 1))


(*
  generate random int term at "size"
  vars needs to contain at least one element
*)
let rec genInts (ivars : ident list) (svars : ident list) (size : int) : intTerm list =
  if size = 0 then
    [Intvar (List.nth ivars (Random.int (List.length ivars)))]
  else
    let res = ref [] in
    let n = max 1 (Random.int size) in
      for i = 0 to n - 1 do
	res := (genIntTerm ivars svars (size - 1)) :: !res
      done;
      !res

and genIntTerm (ivars : ident list) (svars : ident list) (size : int) : intTerm =
  if size = 0 then
    Intvar (List.nth ivars (Random.int (List.length ivars)))    
  else
    match Random.int 6 with
      | 0 -> Intvar (List.nth ivars (Random.int (List.length ivars)))
      | 1 -> Const (10 + Random.int size)
      | 2 -> Plus (genInts ivars svars (size - 1))
      | 3 -> Minus (genIntTerm ivars svars (size - 1), genIntTerm ivars svars (size - 1))
      | 4 -> Times (10 + (Random.int size), genIntTerm ivars svars (size - 1))
      | _ -> Card (genSetTerm svars size) (* genSetVar will itself reduces size *)

(*
  generate quantifier-free formulae
*)
let rec genQFForms (ivars : ident list) (svars : ident list) (size : int) : form list =
  if size = 0 then
    if Random.int 2 = 0 then
      [Less (Const 0, Const 1)]
    else
      [Less (Const 1, Const 0)]
  else
    let res = ref [] in
    let n = max 1 (Random.int size) in
      for i = 0 to n - 1 do
	res := (genQFForm ivars svars (size - 1)) :: !res
      done;
      !res

and genQFForm (ivars : ident list) (svars : ident list) (size : int) =
  if size = 0 then
    if Random.int 2 = 0 then
      Less (Const 0, Const 1)
    else
      Less (Const 1, Const 0)
  else
    match Random.int 9 with
      | 0 -> Not (genQFForm ivars svars (size - 1))
      | 1 -> And (genQFForms ivars svars (size - 1))
      | 2 -> Or (genQFForms ivars svars (size - 1))
      | 3 -> Impl (genQFForm ivars svars (size - 1), genQFForm ivars svars (size -1))
      | 4 -> Less (genIntTerm ivars svars size, genIntTerm ivars svars size)
      | 5 -> Leq (genIntTerm ivars svars size, genIntTerm ivars svars size)
      | 6 -> Inteq (genIntTerm ivars svars size, genIntTerm ivars svars size)
      | 7 -> Seteq (genSetTerm svars size, genSetTerm svars size)
      | _ -> Subseteq (genSetTerm svars size, genSetTerm svars size)


let genNames (prefix : string) (n : int) : string list =
  if n = 0 then
    []
  else
    let res = ref [] in
      for i = 0 to n - 1 do
	res := (prefix ^ (string_of_int i)) :: !res
      done;
      !res

let rec genQForm (ivars : ident list) (svars :ident list) (f : form) : form =
  let sl = List.length svars in
  let il = List.length ivars in
  if sl + il = 0 then
    f
  else
    if (sl > 0 && Random.int 2 = 0) || (il = 0)  then
      (* take one from set vars *)
      let svar = List.nth svars (Random.int sl) in
      let svars1 = List.filter (fun v -> v != svar) svars in
	if Random.int 2 = 0 then
	  genQForm ivars svars1 (Bind (Existsset, svar, f))
	else
	  genQForm ivars svars1 (Bind (Forallset, svar, f))
    else
      (* take one from int vars *)
      let ivar = List.nth ivars (Random.int il) in
      let ivars1 = List.filter (fun v -> v != ivar) ivars in
	if Random.int 2 = 0 then
	  genQForm ivars1 svars (Bind (Existsnat, ivar, f))
	else
	  genQForm ivars1 svars (Bind (Forallnat, ivar, f))

let genForm (nivars : int) (nsvars : int) (size : int) : form =
  let ivars = genNames "ivar" nivars in
  let svars = genNames "svar" nsvars in
  let qfform = genQFForm ivars svars size in
    genQForm ivars svars qfform

(*--------------------------------------------------
  Testing
  --------------------------------------------------*)

let runFormula (bf : form) : bool =
  let pf = Bapapres.bapaFormToPresForm (alpha bf) in
    Presburger.omegaIsValid pf

let print_validity (f : form) : unit = 
  let b = runFormula f in
    begin
      if b then
	print_string ("\n\tis valid\n\n")
      else
	print_string ("\n\tis invalid\n\n")
    end

(*
let _ = 
  if (Array.length Sys.argv) != 5 then
    print_string ("Usage: genbapa nivars nsvars size nforms\n"
		    ^ "\tnivars: maximum number of integer variables\n"
		    ^ "\tnsvars: maximum number of set variables\n"
		    ^ "\tsize: maximum depth of formula\n"
		    ^ "\tnforms: number of formulae to be generated\n")
  else
    let nivars = int_of_string (Sys.argv.(1)) in
    let nsvars = int_of_string (Sys.argv.(2)) in
    let size = int_of_string (Sys.argv.(3)) in
      Random.init 2;
      for i = 0 to int_of_string Sys.argv.(4) - 1 do
	let f1 = genForm nivars nsvars size in
	  print_string ((string_of_form f1) ^ "\n\n");
	  print_validity f1 
      done
*)

let _ = 
  if (Array.length Sys.argv) != 4 then
    print_string ("Usage: genbapa nivars nsvars size\n"
		    ^ "\tnivars: maximum number of integer variables\n"
		    ^ "\tnsvars: maximum number of set variables\n"
		    ^ "\tsize: maximum depth of formula\n")
  else
    let nivars = int_of_string (Sys.argv.(1)) in
    let nsvars = int_of_string (Sys.argv.(2)) in
    let size = int_of_string (Sys.argv.(3)) in
      Random.init 2;
      for i = 1 to size do
	let f1 = genForm nivars nsvars i in
	  print_string ((string_of_form f1) ^ "\n\n");
	  flush_all ();
	  let t1 = Sys.time () in
	    print_validity f1;
	    ignore (Sys.command "ls -l input.oc");
	    let t2 = Sys.time () in
	      print_string ("time taken: " ^ (string_of_float (t2 -. t1)) ^ "\n\n")
      done
