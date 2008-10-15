open Form

(** Get free type variables in a type formula.   *)

let ftv (f : typeForm) : ident list =
   let add v acc = 
    if List.mem v acc then acc
    else v::acc in
  let rec fv1 f acc = match f with
    | TypeUniverse -> acc
    | TypeVar v -> add v acc
    | TypeApp(_,fs) -> fv_list fs acc
    | TypeFun(fs,f1) -> fv_list (f1::fs) acc
    | TypeProd fs -> fv_list fs acc
  and fv_list fs acc = match fs with
    | [] -> acc
    | f0::fs1 -> fv_list fs1 (fv1 f0 acc)
  in fv1 f []

