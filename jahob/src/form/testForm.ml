(** read {!Form} formulas in the given files and try to decide them. *)

open Printf ;;
open Form ;;
open FormUtil ;;

(*
let do_it (filename:string) = 
  let string_f = Util.string_of_file filename in
  let f : form = ParseForm.parse_formula string_f in
  let res : bool = Decider.valid f in
    
    match res with
      | false -> printf "input formula (%s) is NOT valid. Insert coin and try again...\n" filename
      | true -> printf "input formula (%s) is VALID. Yahoooo !\n" filename ;;
	  

ListLabels.iter ~f:do_it !CmdLine.javaFiles
*)
