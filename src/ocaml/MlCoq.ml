(** Coq Extraction Definitions **)
type ascii =
  | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type nat =
  | O
  | S of nat

(** Helpful functions **)
let int_to_nat =
  let rec f i acc =
    if i = 0 then 
      acc
    else
      f (i - 1) (S acc)
  in 
  fun i -> 
    if i < 0 then 
      failwith "iton : negative number!"
    else 
      f i O
;;

let nat_to_int =
  let rec f acc n =
    match n with
    | O -> acc
    | S m -> f (1 + acc) m
  in
  f 0
;;

let ascii_to_char asc = 
  let Ascii (a, b, c, d, e, f, g, h) = asc in
  let bits : bool list = [a;b;c;d;e;f;g;h] in
  let ch = List.fold_right (fun v a -> a * 2 + if v then 1 else 0) bits 0 in
  Char.chr ch
;;

let list_ascii_to_string s = 
  let rec r s =
    match s with
      [] -> ""
    | first :: rest ->
	(String.make 1 (ascii_to_char first)) ^ (r rest)
  in r s
;;
  
