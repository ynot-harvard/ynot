(** Minimal computation of types for Java expressions. *)

open Syntax

let boolean_type = TypeName [Syntax.synth_id "boolean"]
let int_type = TypeName [Syntax.synth_id "int"]
let string_type = TypeName [Syntax.synth_id "String"]
let object_type = TypeName [synth_id "Object"]
let void_type = TypeName [synth_id "void"]

let is_void (t : typ) = 
  if t==void_type then true
  else match t with
    | TypeName [n] -> (id_string n = "void")
    | _ -> false

(*
let is_boolean (t : typ) = 
  if t==boolean_type then true
  else match t with
    | TypeName [n] -> (id_string n = "boolean")
    | _ -> false

let is_int (t : typ) = 
  if t==int_type then true
  else match t with
    | TypeName [n] -> (id_string n = "int")
    | _ -> false
*)

let type_postfix (t : typ) (op : string) : typ =
  failwith ("Don't know how to type postfix operator " ^ op)

let type_prefix (op : string) (t : typ) : typ =
  if op="-" then t
  else if (op="!" || op="not") then boolean_type
  else failwith ("Don't know how to type prefix operator " ^ op)

let rel_ops = ["=="; "!="; "<"; ">"; "<="; ">="]
let arith_op = ["+"; "-"; "/"; "*"; "%"]
let bool_op = ["&&"; "||"; "and"; "or"]

let type_infix (t1 : typ) (op : string) (t2 : typ) : typ =
  if List.mem op rel_ops then boolean_type
  else if List.mem op arith_op then t1
  else if List.mem op bool_op then t2
  else failwith ("Don't know how to type infix operator " ^ op)


