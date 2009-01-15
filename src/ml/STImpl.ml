open Obj;;

type 'a axiom_ST = unit -> 'a ;;

let axiom_STBind b k = fun () -> let v = b () in k v ();;

let axiom_STReturn v () = v ;;

let axiom_STContra () = failwith "ST Contradiction" ;;

let axiom_STWeaken x = x ;;

let axiom_STStrengthen x = x ;;
 
let axiom_STNew v = fun () -> ref (Obj.magic v) ;;

let axiom_STFree p = fun () -> () ;;

let axiom_STRead p = fun () -> Obj.obj !p ;;

let axiom_STWrite p v = fun () -> (p := Obj.repr v) ;;

(** ((a -> (unit -> b)) -> a -> (unit -> b)) -> a -> (unit -> b) **)
let axiom_STFix f x = fun () -> 
  let rec fix g = fun a -> f (fix f) a
  in (fix f) x () ;;

let exec io = io ()
