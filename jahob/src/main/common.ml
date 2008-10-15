(** Common Jahob definitions *)

type analysis_task = {
  task_lemmas : (string * string) list;
  task_methods : (string * string) list;
  task_classes : string list;
}

type source_pos = {
  pos_class : string;
  pos_method : string;
  pos_place : string;
}

let string_of_pos (pos : source_pos) : string =
  "[" ^ pos.pos_class ^ "." ^ pos.pos_method ^ ", " ^ pos.pos_place ^ "]"

let identlike_pos (pos : source_pos) : string =
  let add s = if s="" then "" else "_" ^ s in
    pos.pos_class ^ "_" ^ pos.pos_method ^ add pos.pos_place

let unknown_pos = {
  pos_class = "UnknownClass";
  pos_method = "UnknownMethod";
  pos_place = "";
}

let task_is_empty (task : analysis_task) : bool =
  task.task_lemmas = [] &&
  task.task_methods = [] &&
  task.task_classes = []

let method_is_relevant 
    ((cname,mname) : string * string)
    (task : analysis_task) : bool =
  List.mem (cname,mname) task.task_methods ||
  List.mem cname task.task_classes

let class_is_relevant
    (cname : string)
    (task : analysis_task) : bool = 
  List.mem cname task.task_classes

(** {6 these are usefull to deal with command-line options}*)

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type options_t = string StringMap.t

(** merges two mapings. When a key [s] appears in both [default] and [provided], the associated value in the result is the value found in [provided]. *)
let merge_opts (default:options_t) (provided:options_t) : options_t = 
  StringMap.fold (fun key value oldmap -> StringMap.add key value oldmap) provided default

(** transforms a list of [(a1, b1);(a2, b2);...] in a maping [a1 => b1 ; a2 => b2 ; ....] *)
let map_of_list : (string*string) list -> options_t = 
  ListLabels.fold_left ~f:(fun m (a,b) -> StringMap.add a b m) ~init:StringMap.empty

(** [glag_positive ~o flag] is [true] iff [flag] appear as a key in [o], with an associated value different from "no". *)
let flag_positive ~(o:options_t) (flag:string) : bool = 
  try 
    not (StringMap.find flag o = "no")
  with
    | Not_found -> false
