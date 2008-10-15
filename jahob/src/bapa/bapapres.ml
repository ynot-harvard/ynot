(** Connvert BAPA formula in Presburger subset into Presburger formula ast
   (mostly just datatype conversion). *)

open Alpha
open Presburger


let rec intTermToAExp (it : intTerm) : aExp = match it with
  | Intvar v -> Var v
  | Alpha.Const c -> Presburger.Const c
  | Plus its -> List.fold_left makePlus (Presburger.Const 0) its
  | Alpha.Minus (it1, it2) -> Presburger.Minus (intTermToAExp it1, intTermToAExp it2)
  | Times (c, it) -> Mult (c, intTermToAExp it)
  | Card _ -> failwith "Converting BAPA to Presburger: BAPA formula still contains Card"

and makePlus ae it = 
  let aeit = intTermToAExp it in
    Add (ae, aeit)



let rec bapaFormToPresForm (bapa : form) : presForm = match bapa with
  | Alpha.Not f -> Presburger.Not (bapaFormToPresForm f)
  | Alpha.And fs -> 
      let h = bapaFormToPresForm (List.hd fs) in
	List.fold_left makeAnd h (List.tl fs)
  | Alpha.Or fs -> 
      let h = bapaFormToPresForm (List.hd fs) in
	List.fold_left makeOr h (List.tl fs)
(*
  | Alpha.And fs -> List.fold_left makeAnd presFormTrue fs
  | Alpha.Or fs -> List.fold_left makeOr presFormFalse fs
*)
  | Alpha.Less (it1, it2) -> Presburger.Less (intTermToAExp it1, intTermToAExp it2)
  | Alpha.Leq (it1, it2) -> Presburger.Leq (intTermToAExp it1, intTermToAExp it2)
  | Inteq (it1, it2) -> Eq (intTermToAExp it1, intTermToAExp it2)
  | Impl (f1, f2) -> Presburger.Or (Presburger.Not (bapaFormToPresForm f1), 
				    bapaFormToPresForm f2)
  | Bind (Forallint, i, f) -> Forall (i, bapaFormToPresForm f)
  | Bind (Existsint, i, f) -> Exists (i, bapaFormToPresForm f)
  | Bind (Forallnat, i, f) -> 
      let bf = bapaFormToPresForm f in
      let c = Less (Var i, Const 0) in
        Forall (i, Or (c, bf))
  | Bind (Existsnat, i, f) -> 
      let bf = bapaFormToPresForm f in
      let c = Leq (Const 0, Var i) in
        Exists (i, And (c, bf))
  | _ -> failwith "Converting BAPA to Presburger: BAPA formula still contains non-Presburger constructs"

and makeAnd pf bf =
  let pfbf = bapaFormToPresForm bf in
    if pf = presFormTrue then
      pfbf
    else if pfbf = presFormTrue then
      pf
    else
      And (pf, pfbf)

and makeOr pf bf =
  let pfbf = bapaFormToPresForm bf in
    if pf = presFormFalse then
      pfbf
    else if pfbf = presFormFalse then
      pf
    else
      Or (pf, pfbf)


(*--------------------------------------------------
Testing
  --------------------------------------------------*)
(*
let _ = print_string "------------------------------\n"
let _ = print_string "------------------------------\n"

let pexample1 = bapaFormToPresForm (alpha example1)
let _ = print_string ((string_of_bool (omegaIsValid pexample1)) ^ "\n")

let pexample2 = bapaFormToPresForm (alpha example2)
let _ = print_string ((string_of_bool (omegaIsValid pexample2)) ^ "\n")

let pexample3 = bapaFormToPresForm (alpha example3)
let _ = print_string ((string_of_bool (omegaIsValid pexample3)) ^ "\n")

let pexample4 = bapaFormToPresForm (alpha example4)
let _ = print_string ((string_of_bool (omegaIsValid pexample4)) ^ "\n")

let pexample5 = bapaFormToPresForm (alpha example5)
let _ = print_string ((string_of_bool (omegaIsValid pexample5)) ^ "\n")

let pexample6 = bapaFormToPresForm (alpha example6)
let _ = print_string ((string_of_bool (omegaIsValid pexample6)) ^ "\n")

let pexample7 = bapaFormToPresForm (alpha example7)
let _ = print_string ((string_of_bool (omegaIsValid pexample7)) ^ "\n")

let pexample8 = bapaFormToPresForm (alpha example8)
let _ = print_string ((string_of_bool (omegaIsValid pexample8)) ^ "\n")

*)
