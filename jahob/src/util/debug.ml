(** Printing (conditional debugging messages).  Currently they go to terminal.  *)

(* output channel for debug messages *)
let debug_chan = stdout

let debugOn = ref false

let debug_level = ref 0

let set_debug_level l = if l >= 0 then debug_level := l

let lmsg l msg = if (!debugOn || !debug_level > 0) && l <= !debug_level then
  (output_string debug_chan ("..." ^ msg ()); flush debug_chan)

let print_msg l msg = if (!debugOn || !debug_level > 0) && l <= !debug_level then
  (msg debug_chan; flush debug_chan)

let newline () = output_char debug_chan '\n'

let msg s = lmsg 0 (fun () -> s)

(* Debug settings makes it possible to turn on and off a number of
   different debug messages independently. To speed things up, we use
   bit operations to do parallel checks on which debug messages are
   turned on. *)

let debug_smtPrint = 1
let debug_typeReconstruct = 2

(* A list of pairs with type (string, int).  The first element is the
   string denoting the name of the module. The second is 2 to the
   power of j, where j is the bit location that is to be set if the
   debug option for that module is on. New entries should use bit
   locations not already assigned. *)
let debug_flags = Hashtbl.create 0

let debug_settings = ref 0

let register_debug_module : string -> int = 
  let next_id = ref 1 in
  fun module_name ->
    let id = !next_id in
    Hashtbl.add debug_flags module_name id;
    next_id := !next_id * 2; 
    id

(* Turns on the debug option for the module associated with the module_name. *)
let set_debug_module (module_name : string) : unit = 
  try
    let bit = Hashtbl.find debug_flags module_name in
      (* sets the bit associated with module_name *)
      debug_settings := (!debug_settings lor bit)
  with Not_found -> print_string ("debugmodules option " ^ module_name ^ " not found\n")

(* Turns on the debug option for the module associated with the module_name. *)
let unset_debug_module (module_name : string) : unit = 
  try
    let bit = Hashtbl.find debug_flags module_name in
      (* sets the bit associated with module_name *)
      debug_settings := (!debug_settings land (lnot bit))
  with Not_found -> print_string ("debugmodules option " ^ module_name ^ " not found\n")

let set_debug_modules (module_names : string) : unit = 
  let module_list = Util.split_by "," module_names in
    List.iter set_debug_module module_list

let debug_is_on (msg_type : int) : bool =
  (not ((msg_type land !debug_settings) = 0))

let debug_msg (msg_type : int) (msg : string) : unit = 
  if (debug_is_on msg_type) then
    (output_string debug_chan msg; flush debug_chan)

let debug_lmsg (msg_type : int) (level : int) (msg : unit -> string) : unit = 
  if debug_is_on msg_type then lmsg level msg

let debug_print_msg (msg_type : int) (level : int) msg : unit =
  if debug_is_on msg_type then print_msg level msg

