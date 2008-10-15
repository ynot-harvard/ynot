(** Utility module with miscellaneous functions,
    including string functions and operating system functions.

  TODO: Sort functions by category, clean up.
 *)

exception Bad_string
exception Bail

(* Qualify helper file name *)
(* if you want to install the executable in one directory (e.g. /usr/bin),
 * but put helper files in another (/usr/share/module-language),
   here's what you need to change! *)

let qualify_helper_fn n =
  let d =  Filename.dirname Sys.executable_name ^ "/" in
  (* Sys.getcwd() ^ "/" ^ *) d ^ n

let lib_name n =
  try (let d = Filename.dirname Sys.executable_name ^ "/../lib/" in
	 (* Sys.getcwd() ^ "/" ^ *) d ^ n)
  with Sys_error _ -> n

let tmp_name n =
  try (let d = Filename.dirname Sys.executable_name ^ "/../tmp/" in    
	 (* Sys.getcwd() ^ "/" ^ *) d ^ n)
  with Sys_error _ -> n

(** filename handling; returns the inverse of Filename.chop_extension *)
let extension n =
  let d = String.rindex n '.' in
  String.sub n d (String.length n - d)

let get_path s = 
  if String.contains s '/' then
    let i = String.rindex s '/' in
    String.sub s 0 (i+1)
  else ""

(* List-handling stuff *)
let rec remove_dups n = 
  match n with
    [] -> []
  | q::qs -> if (List.mem q qs) then remove_dups qs else q::(remove_dups qs)

let rec find_dups n = 
  match n with
    [] -> []
  | q::qs -> if (List.mem q qs) then q::(find_dups qs) else find_dups qs


let disjoint l1 l2 = 
  List.for_all (fun x -> not (List.mem x l2)) l1

let intersect l1 l2 =
  List.filter (fun x -> List.mem x l2) l1

let difference l1 l2 =
  List.filter (fun x -> not (List.mem x l2)) l1

let union l1 l2 =
  difference l1 l2 @ l2 

let spacify i = 
  let s' z = List.fold_left (fun x y -> x ^ i ^ y) "" z in
  function [] -> ""
  | [x] -> x
  | x::xs -> x ^ (s' xs)

(** Composition of List.map and List.partition *)
let partition_map p f xs =
  List.fold_right (fun x (ys, zs) -> if p x then (f x :: ys, zs) 
      else (ys, f x :: zs)) xs ([], [])

(** Composition of List.map and List.filter *)
let filter_map p f xs =
  List.fold_right (fun x ys -> if p x then f x :: ys else ys) xs []

(** Find an element in a list and apply a function *)  
let rec find_map (f : 'a -> 'b option) (xs : 'a list) : 'b =
  match xs with
  | x::xs' -> 
      (match f x with
      |	None -> find_map f xs'
      | Some y -> y)
  | [] -> raise Not_found

(** Combination of List.assoc and List.remove *)
let assoc_remove key assoc_list =
  let rec ar assoc_list acc =
    match assoc_list with
    | [] -> raise Not_found
    | (key', v)::assoc_list' when key = key' -> 
	(v, List.rev_append acc assoc_list') 
    | kv::assoc_list' -> ar assoc_list' (kv::acc)
  in ar assoc_list []

(** Replace association [(key, v)] with
   [(key, fn v)] in association list [assoc_list]. If no association with 
   [key] exists then add [(key, default)] to the list. *)
let assoc_replace key fn default assoc_list =
  let rec ar acc = function
    | (key', v)::assoc_list' when key = key' ->
	(key, fn v)::List.rev_append acc assoc_list'
    | (key', v)::assoc_list' -> ar ((key', v)::acc) assoc_list'
    | [] -> (key, default)::List.rev acc
  in ar [] assoc_list

(** Split the list of length k>=1 into a pair consisting of
   the list of first k-1 elements and the last element. *)
let rec firsts_last xs = match xs with
| [] -> failwith "Util.first_lasts: empty list"
| [x] -> ([],x)
| x::xs1 ->
    let (fs,l) = firsts_last xs1 in
    (x::fs,l)
      
(** generate a list of length [n] using generator [f] *)
let generate_list (f : int -> 'a) (n : int) : 'a list = 
  let rec mk_tl n acc = 
    if n <= 0 then acc 
    else mk_tl (n - 1) (f n :: acc) 
  in mk_tl n []
   

(** Currify function *)
let curry f x y = f (x, y)

(** Uncurrify function *)
let uncurry f (x, y) = f x y


(** String-handling utility functions. *)

let trim_quotes s = 
  let trim_last s' = if String.get s' ((String.length s')-1) = '"' then
    String.sub s' 0 ((String.length s')-1) else s' in
  if String.get s 0 = '"' then 
    (trim_last (String.sub s 1 ((String.length s) - 1)))
  else
    trim_last s

let unescaped s =
  let n = ref 0 in
    for i = 0 to String.length s - 1 do
      n := !n +
        (match String.unsafe_get s i with
           '\\' when String.unsafe_get s (i+1) != '\\' ->
             (match String.unsafe_get s (i+1) with
               'n' -> 0
             | 't' -> 0
             | _ -> 1)
        | _ -> 1)
    done;
    if !n = String.length s then s else begin
      let s' = String.create !n in
      n := 0;
      let skip = ref 0 in
      (try (for i = 0 to String.length s - 1 do
        begin
          if (i + !skip) = String.length s then raise Bail;
          match String.unsafe_get s (i + !skip) with
          | '\\' when String.unsafe_get s (i+ !skip+1) != '\\' ->
              (match String.unsafe_get s (i+ !skip+1) with
                'n' -> String.unsafe_set s' !n '\n'; incr skip
              | 'r' -> String.unsafe_set s' !n '\r'; incr skip
              | 't' -> String.unsafe_set s' !n '\t'; incr skip
              | '\\' -> String.unsafe_set s' !n '\\'; incr skip;
              | _ -> raise Bad_string)
          | c -> String.unsafe_set s' !n c
        end;
        incr n
      done) with Bail -> ());
      Str.first_chars s' (String.length s - !skip)
    end

(** namespace mangling stuff *)

let qualify_if_needed mname n =
  if String.contains n '.' then n else (mname ^ "." ^ n)

(** return the class name, if any *)
let unqualify_getting_module s =
  if String.contains s '.' then
    let i = String.rindex s '.' in
    String.sub s 0 i
  else ""

let unqualify s =
  if String.contains s '.' then
    let i = String.rindex s '.' in
    String.sub s (i+1) (String.length s - i - 1)
  else s

let unprime s =
  let l = String.length s in 
  if l = 0 then s else 
  if (String.get s (l-1)) = '\'' then
    String.sub s 0 (l-1) else s

let is_primed s =
  let l = String.length s in 
  if l = 0 then false else 
  (String.get s (l-1) = '\'')

let replace_dot_with_uscore s =
  let dot = Str.regexp "\\." in
  let caret = Str.regexp "\\^" in
  Str.global_replace dot "_" 
    (Str.global_replace caret "$" s)

let split_by sep s =
  let sep_regexp = Str.regexp (Str.quote sep) in
  Str.split sep_regexp s

(** Error-handling functions. *)

let error_list = ref []
let no_errors () = (List.length !error_list = 0)

let err loc msg = 
  error_list := !error_list @
    [loc ^ ": error: "^msg]

let error msg = (print_string (msg ^"\n"); flush_all(); err "" msg)
let print_errors () = 
  List.iter (function x -> print_string (x ^ "\n")) !error_list;
  print_string (string_of_int (List.length !error_list)^" errors.\n");
  print_string "The program is INVALID\n";
  exit 2

(** Printing notifications [msg, amsg, etc] *)
let verbose = ref false

(** always print this message *)
let amsg s = print_string s; flush_all ()

(** print only if -v *)
let msg s = if !verbose then amsg s

let (warning_no : int ref) = ref 0
let warn msg = 
  (warning_no := !warning_no + 1);
  print_string ("*** Warning: "^ msg ^ "\n"); flush_all()

let fail s =   
  print_string (s ^ "\n"); 
  Printf.printf "There were %d warnings.\n" !warning_no;
  flush_all();
  failwith s

let warn_if_none ov msg = match ov with
  | None -> warn msg
  | Some _ -> ()

(** Failing on warnings *)

let resilient = ref false
let fail_if_warned (s : string) : unit =
  if (!warning_no > 0) then
    (print_string(" *** " ^ s ^ "\n");
     (if !resilient then 
	(msg("       -resilient option used, so Jahob is continuing despite warnings");
	 (warning_no := 0))
      else fail "     Jahob failed due to warnings in this phase; use -resilient option to ignore them"))
  else
    ()
  
(** removing 'option' types *)
let unsome : 'a option -> 'a = 
function
  | Some x -> x
  | None   -> failwith "[util] tried to deoptionify None"

let safe_unsome default : 'a option -> 'a = 
function
  | Some x -> x
  | None -> default

let optmap (f : 'a -> 'b) 
           (ox : 'a option) : 'b option = 
  match ox with 
    | None -> None 
    | Some x -> Some (f x)

let empty l = match l with [] -> true | _ -> false

(** Read the given file into a string. *)
let string_of_file (fname : string) =
  if Sys.file_exists fname then
    let chn = open_in fname in
    let len = in_channel_length chn in
    let str = String.make len ' ' in
    let _ = really_input chn str 0 len in
    (close_in chn; str)
  else
    (warn ("Could not read file " ^ fname ^ "; assuming empty content.");
     "")

let fileLine (fn:string) : string =
  begin
    let chn = open_in fn in
      let str = input_line chn in
      close_in chn;
      str
  end

(** Use timed_command utility to run an external process with a timeout. *)

(*
let timed_command = qualify_helper_fn "timed_command"
*)
let timed_command = "timeout"

let run_with_timeout (prog : string) (seconds : int) : int =
  (* msg ("Running with timeout: " ^ prog ^ "\n"); *)
  Sys.command (timed_command ^ Printf.sprintf " %d " seconds ^ prog)
