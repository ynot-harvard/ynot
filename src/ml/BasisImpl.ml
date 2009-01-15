open STImpl

(** printString : string -> unit sTsep **)
let axiom_printString str () = 
  print_string (MlCoq.list_ascii_to_string str); flush stdout

(** printStringLn : string -> unit sTsep **)
let axiom_printStringLn str () = 
  print_string (MlCoq.list_ascii_to_string str); print_string "\r\n"; flush stdout
