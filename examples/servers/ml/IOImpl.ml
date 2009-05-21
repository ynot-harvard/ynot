open Ascii;;

let rec ntoi n =
  match n with
    Datatypes.O -> 0
  | Datatypes.S n' -> 1 + ntoi n'
;; 

let ctoa m =
  let n = Char.code m in
  let tobit n = if (n land 1) = 1 then true else false in
  let (a,ra) = tobit n,  n lsr 1 in
  let (b,rb) = tobit ra, ra lsr 1 in
  let (c,rc) = tobit rb, rb lsr 1 in
  let (d,rd) = tobit rc, rc lsr 1 in
  let (e,re) = tobit rd, rd lsr 1 in
  let (f,rf) = tobit re, re lsr 1 in
  let (g,rg) = tobit rf, rf lsr 1 in
  let (h,rh) = tobit rg, rg lsr 1 in
  Ascii.Ascii (a, b, c, d, e, f, g, h)
;;

let atoc (Ascii(a,b,c,d,e,f,g,h)) =
  Char.chr (List.fold_right (fun x a -> a * 2 + if x then 1 else 0)
	      [a;b;c;d;e;f;g;h] 0)
;;

let latostr l =
  let res = String.create (List.length l) in
  let rec f i l = 
    match l with
      [] -> res
    | a :: r -> 
	let _ = String.set res i (atoc a) in f (i + 1) r
  in f 0 l
;;

let strtola str =
  let len = String.length str in
  let rec f i acc =
    if i < 0 then
      acc
    else
      f (i - 1) ((ctoa (String.get str i)) :: acc)
  in f (len - 1) []
;;

let axiom_getT () = Obj.magic []
