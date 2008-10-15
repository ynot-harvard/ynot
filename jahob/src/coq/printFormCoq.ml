(** Printing {!Form} formulas to strings into
    representation understood by Coq. *)

open Form
open TypeVars
open FormUtil

let nullConstName = "null"

let rec p s = "(" ^ s ^ ")"
and wr_int = function
  | Const (IntConst i) -> Printf.sprintf "%d" i
  | _ -> failwith "vcprint.isa_form: non-constant cardinality constraint"

and guarded_string_conversion = function
  | "List" -> "List_Object"
  | x -> x

and coq_ident s = Util.replace_dot_with_uscore (guarded_string_conversion s)

and wr_form_list1 op f =  (* function
  | [] -> ""
  | [f] -> wr_form f
  | f::fs1 -> wr_form f ^ op ^ wr_form_list1 op fs1
*)
  String.concat op (List.map wr_form f)
and wr_form_list op fs = p (wr_form_list1 op fs)
and infx f1 op f2 = p (wr_form f1 ^ op ^ wr_form f2)
and prefx op f1 f2 = p (op ^ " " ^ wr_form f1 ^ " " ^ wr_form f2)
and wr_binding (v,t) =
  (let v_s = coq_ident v in 
     match t with
       | TypeUniverse -> v_s
       | _ -> p (v_s ^ ":" ^ wr_type t))
and wr_bindings vts = String.concat " " (List.map wr_binding vts)
and wr_tuple vts =  "(" ^ String.concat ", " (List.map wr_binding vts) ^ ")"
and wr_binder binder vts f = p (binder ^ " " ^ wr_bindings vts ^ ", " ^ wr_form f)

(* let (v::t) = e in f *)
and wr_let1 e (v,t) f =
  "let " ^ wr_binding (v,t) ^ " := " ^ wr_form e ^ " in " ^
    wr_form f
and wr_let e (v,t) f = p (wr_let1 e (v,t) f) 

and wr_type_p (t:typeForm) = match t with
  | TypeApp(st,[]) -> wr_stype st
  | _ -> p (wr_type t)
and wr_type (t:typeForm) = match t with
| TypeUniverse -> "Type"
| TypeVar id -> id
| TypeApp(TypeSet, [st]) -> "Ensemble " ^ wr_type_p st
| TypeApp(TypeArray,[it;et]) -> p (wr_type it ^ " -> " ^ wr_type et)
| TypeApp(st,ts) -> String.concat " " (List.map wr_type_p ts @ [wr_stype st])
| TypeFun(targs,tres) -> p (String.concat " -> " (List.map wr_type_p (targs @ [tres])))
| TypeProd ts -> p (String.concat " * " (List.map wr_type_p ts))
and wr_stype (st:simpleType) = match st with
| TypeUnit -> "unit"
| TypeInt -> "nat"
| TypeString -> "string"
| TypeBool -> "Prop"
| TypeObject -> "obj"
| TypeArray -> "array"
| TypeSet -> "Ensemble"
| TypeList -> "list"
| TypeDefined s  -> coq_ident s

and wr_form f = match f with
(* constants and variables *)
  | Const NullConst -> nullConstName
  | Const (IntConst k) -> Printf.sprintf "%d" k
  | Const (StringConst s) -> s 
  | Const (BoolConst true) -> "True"
  | Const (BoolConst false) -> "False"
  | Const EmptysetConst -> p ("Empty_set _") 
  | App(Const Comment, [Const (StringConst s); f]) -> " (* " ^ s ^ " *) " ^ (wr_form f) 
  | Const Comment -> "WARNING FAILED COMMENT" 
  | Const FieldWrite -> "fieldWrite"
  | Const ArrayWrite -> "ArrayWrite"
  | Const c -> "unknown constant [" ^ string_of_const c ^ "]"
  | Var v -> coq_ident v

  | App(Var "tree", _)
  | App(TypedForm(Var "tree", _), _) -> "True"

(* handling fields *)
  | App(Const FieldRead, [field_name; class_name]) -> wr_form (App (field_name, class_name::[]))
  | App(Const FieldRead, _) -> failwith "incorrect field deference !"
  
(* handling arrays *)
  | App(Const ArrayRead, [arrays_state; array_name; index]) -> wr_form (App (arrays_state, [array_name; index]))
  | App(Const ArrayRead, _) -> failwith "incorrect array deference !" 

(* special thing for infix operators*)
| App(Const Not, [App(Const Eq,[f1;f2])]) -> infx f1 " <> " f2
| App(Const Eq,[f1;f2]) -> infx f1 " = " f2
| App(Const Lt,[f1;f2]) -> infx f1 "<" f2
| App(Const LtEq,[f1;f2]) -> infx f1 " <= " f2
| App(Const Gt,[f1;f2]) -> infx f1 " > " f2
| App(Const GtEq,[f1;f2]) -> infx f1 " >= " f2
| App(Const Plus,[f1;f2]) -> infx  f1 "+" f2
| App(Const Minus,[f1;f2]) -> infx f1 " - " f2
| App(Const Mult,[f1;f2]) -> infx f1 "*" f2
| App(Const Div,[f1;f2]) -> infx f1 " div " f2
| App(Const Mod,[f1;f2]) -> infx f1 " mod " f2

(* Unary Operators *)
| App(Const Not, [f]) -> "~ " ^ wr_form f 
| App(Const UMinus,[f]) -> p ("-" ^ wr_form f)

(* Logical operators : Meta -> Prop // Normal -> bool *)
| App(Const Or,fs) -> wr_form_list " \\/ " fs
| App(Const And,fs) -> wr_form_list " /\\ " fs
| App(Const Impl,[f1;f2]) -> infx f1 " -> " f2
| App(Const Iff,[f1;f2]) -> infx f1 " <-> " f2

| App(Const MetaAnd,fs) -> wr_form_list1 " /\\ " fs
| App(Const MetaImpl,[f1;f2]) -> infx f1 " -> " f2
| App(Const Ite,[f1;f2;f3]) -> p ("if " ^ wr_form f1 ^ " then " ^ wr_form f2 ^ " else " ^ wr_form f3)
| App(Const MetaEq,[f1;f2]) -> infx f1 " <-> " f2

(* Set handling *)
| App(Const FiniteSetConst, []) -> wr_form (Const EmptysetConst)
| App(Const FiniteSetConst, x::[]) -> p ("Singleton _ " ^ wr_form x)
| App(Const FiniteSetConst, x::suite) -> p ("Add _ " ^ wr_form (App(Const FiniteSetConst, suite)) ^ (wr_form x))
| App(Const Elem,[f1;f2]) -> prefx "In _" f2 f1
| App(Const Subseteq,[f1;f2]) -> prefx " Included _" f1 f2
| App(Const Subset,[f1;f2]) -> prefx " Strict_Included _" f1 f2
| App(Const Seteq,[f1;f2]) -> infx f1 " = " f2
| App(Const Cap,[f1;f2]) -> prefx " Intersection _" f1 f2
| App(Const Cup,[f1;f2]) -> prefx " Union _" f1 f2
| App(Const Diff,[f1;f2]) -> prefx "Setminus _ " f1 f2
| App(Const Disjoint,[f1;f2]) -> prefx "Disjoint _ " f1 f2

(* Cardinal stuff *)
| App(Const Cardeq,[f1;k]) -> "cardinal _" ^ wr_form f1 ^ " " ^ wr_int k  
| App(Const Cardleq,[f1;k]) -> wr_form (mk_exists ("n", TypeUniverse, mk_metaand [ App(Const Cardeq,[f1;k]) ; mk_lteq (Var "n", f1) ] ) )
| App(Const Cardgeq,[f1;k]) -> wr_form (mk_exists ("n", TypeUniverse, mk_metaand [ App(Const Cardeq,[f1;k]) ; mk_gteq (Var "n", f1) ] ) )

| App(Const ListLiteral, fs) -> "[" ^ wr_form_list1 "; " fs ^ "]"
| App(Const Tuple, fs) -> "(" ^ wr_form_list1 ", " fs ^ ")"

(* what is that ???!? *)
| App(Const Rimage,[f1;f2]) -> infx f1 " `` " f2

| App(Const Let, [f1;Binder(Lambda,[(v,t)],f2)]) -> wr_let f1 (v,t) f2
(* | App(Const Comment,[Var c;f]) -> " (* " ^ c ^ " *) " ^ wr_form f *)
| Binder(Forall,vts,f1) -> p ("forall " ^ wr_bindings vts ^ ", " ^ p (wr_form f1) )
| Binder(Exists, [], f1) -> wr_form f1
| Binder(Exists, [v,_], f1) -> p ("exists " ^ v ^ ", " ^ p (wr_form f1) )
| Binder(Exists, (v,_)::suite, f1) -> p ("exists " ^ v ^ ", " ^ p (wr_form (Binder (Exists, suite, f1))) )
| Binder(Lambda,vts,f1) -> p ("fun" ^ wr_bindings vts ^ " => " ^ p (wr_form f1) ) (* sets are predicates *)
| Binder(Comprehension,vts,f1) -> p ("fun" ^ wr_bindings vts ^ " => " ^ p (wr_form f1) ) (* sets are predicates *)

| TypedForm(TypedForm(f1,t1),t2) -> wr_form (TypedForm(f1,t2))
| TypedForm(f1,t) -> wr_form f1
    (* let's try to trust the type inference
			if (ftv t)=[] then p (wr_form f1 ^ " : " ^ wr_type t) else wr_form f1 *)
| App(f1,fs) -> wr_form_list " " (f1::fs) 

let string_of_type (t : typeForm) : string = wr_type t  

let string_of_typedef (td : typeDef) : string =
  let wr_param (p : string) = "'" ^ p in
  let wr_params (ps : string list) = match ps with
    | [] -> ""
    | _ -> "(" ^ String.concat ", " (List.map wr_param ps) ^ ")" in
  let wr_body (b : typeDefBody) = match b with
    | SumType _ -> "aSumType"
    | RecordType _ -> "aRecordType"
    | Synonym tf -> wr_type tf
  in
  "type " ^ wr_params td.typDefTypeVars ^ td.typDefName ^ " = " ^
    wr_body td.typDefBody

let string_of_form (f:form) = wr_form f

