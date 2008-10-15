(** Printing {!Form} formulas to strings into
    representation understood by Isabelle. *)

open Form
open TypeVars

let nullConstName = "null"

let rec p s = "(" ^ s ^ ")" 
and wr_int k = match k with
  | Const (IntConst i) -> Printf.sprintf "%d" i
  | _ -> failwith "vcprint.isa_form: non-constant cardinality constraint"
and isabelle_ident s = 
  Util.replace_dot_with_uscore s
and wr_form_list op fs = p (wr_form_list1 op fs)
and infx f1 op f2 = p (wr_form f1 ^ op ^ wr_form f2)
and prefx op f1 f2 = p (op ^ " " ^ wr_form f1 ^ " " ^ wr_form f2)
and wr_binding (v,t) =
  (let v_s = isabelle_ident v in 
     match t with
       | TypeUniverse -> v_s
       | _ -> p (v_s ^ "::" ^ wr_type t))
and wr_bindings vts = String.concat " " (List.map wr_binding vts)
and wr_tuple vts = 
  "(" ^ String.concat ", " (List.map wr_binding vts) ^ ")"
and wr_binder binder vts f = 
  p (binder ^ " " ^ wr_bindings vts ^ ". " ^ wr_form f)

(* let (v::t) = e in f *)
and wr_let1 e (v,t) f =
  "let " ^ wr_binding (v,t) ^ " = " ^ wr_form e ^ " in " ^
    wr_form f
and wr_let e (v,t) f = p (wr_let1 e (v,t) f) 
and wr_type_p t = match t with
  | TypeApp(st,[]) -> wr_stype st
  | _ -> p (wr_type t)
and wr_type t = match t with
| TypeUniverse -> "universe"
| TypeVar id -> "'" ^ id
| TypeApp(TypeArray,[it;et]) -> 
    p (wr_type it ^ " => " ^ wr_type et)
| TypeApp(st,ts) -> 
    String.concat " " 
      (List.map wr_type_p ts @ [wr_stype st])
| TypeFun(targs,tres) -> 
    p (String.concat " => " (List.map wr_type_p (targs @ [tres])))
| TypeProd ts -> p (String.concat " * " (List.map wr_type_p ts))
and wr_stype st = match st with
| TypeUnit -> "unit"
| TypeInt -> "int"
| TypeString -> "string"
| TypeBool -> "bool"
| TypeObject -> "obj"
| TypeArray -> "array"
| TypeSet -> "set"
| TypeList -> "list"
| TypeDefined s -> isabelle_ident s
and wr_fun_type ts t1 = match ts with
| [] -> wr_type t1
| t2::ts2 -> wr_type t2 ^ " => " ^ wr_fun_type ts2 t1

and wr_form f = match f with
| Const (BoolConst true) -> "True"
| Const (BoolConst false) -> "False"
| App(Const Not, [App(Const Eq,[f1;f2])]) -> infx f1 " ~= " f2
| App(Const Not, [App(Const Elem,[f1;f2])]) -> infx f1 " ~: " f2
| App(Const Not, [f]) -> p ("~" ^ wr_form f)
| App(Const Or,fs) -> wr_form_list " | " fs
| App(Const And,fs) -> wr_form_list " & " fs
| App(Const MetaAnd,fs) -> "[|" ^ wr_form_list1 ";\n" fs ^ "|]"
| App(Const Impl,[f1;f2]) -> infx f1 " --> " f2
| App(Const MetaImpl,[f1;f2]) -> infx f1 " ==>\n    " f2
| App(Const Iff,[f1;f2]) -> infx f1 " <-> " f2
| App(Const Ite,[f1;f2;f3]) -> p ("if " ^ wr_form f1 ^ " then " ^ wr_form f2 ^ " else " ^ wr_form f3)

| App(Const Eq,[f1;f2]) -> infx f1 " = " f2
| App(Const MetaEq,[f1;f2]) -> infx f1 " == " f2

| Const EmptysetConst -> "{}"
| App(Const FiniteSetConst, fs) -> "{" ^ wr_form_list1 ", " fs ^ "}"
| App(Const Tuple, fs) -> "(" ^ wr_form_list1 ", " fs ^ ")"
| App(Const Elem,[f1;f2]) -> infx f1 " : " f2
| App(Const Subseteq,[f1;f2]) -> infx f1 " \\<subseteq> " f2
| App(Const Seteq,[f1;f2]) -> infx f1 " === " f2
| App(Const Cap,fs) -> wr_form_list " Int " fs
| App(Const Cup,fs) -> wr_form_list " Un " fs
| App(Const Diff,[f1;f2]) -> infx f1 " \\<setminus> " f2
| App(Const Disjoint,fs) -> "handleDisjoint"
| App(Const Cardeq,[f1;k]) -> "cardeq" ^ wr_int k ^ " " ^ wr_form f1
| App(Const Cardleq,[f1;k]) -> "cardleq" ^ wr_int k ^ " " ^ wr_form f1
| App(Const Cardgeq,[f1;k]) -> "cardgeq" ^ wr_int k ^ " " ^ wr_form f1

| App(Const ListLiteral, fs) -> "[" ^ wr_form_list1 ", " fs ^ "]"

| Const (IntConst k) -> Printf.sprintf "%d" k
| Const (StringConst s) -> "''" ^ s ^ "''"
| App(Const Lt,[f1;f2]) -> prefx "intless" f1 f2
| App(Const LtEq,[f1;f2]) -> infx f1 " <= " f2
| App(Const Gt,[f1;f2]) -> infx f2 " < " f1
| App(Const GtEq,[f1;f2]) -> infx f2 " <= " f1

| App(Const UMinus,[f]) -> p ("-" ^ wr_form f)
| App(Const Plus,[f1;f2]) -> prefx "intplus" f1 f2
| App(Const Minus,[f1;f2]) -> infx f1 " - " f2
| App(Const Mult,[f1;f2]) -> prefx "inttimes" f1 f2
| App(Const Div,[f1;f2]) -> infx f1 " div " f2
| App(Const Mod,[f1;f2]) -> infx f1 " mod " f2
| App(Const Rimage,[f1;f2]) -> infx f1 " `` " f2
| App(Const Let,[f1;Binder(Lambda,[(v,t)],f2)]) -> 
    wr_let f1 (v,t) f2
(* | App(Const Comment,[Var c;f]) -> " (* " ^ c ^ " *) " ^ wr_form f *)
| App(Const Comment,[Const (StringConst s);f]) -> 
    "comment ''" ^ s ^ "'' " ^ wr_form f
| Const NullConst -> nullConstName
| Const c -> Form.string_of_const c 

| Var v -> isabelle_ident v
| Binder(Forall,vts,f1) -> wr_binder "ALL" vts f1
| Binder(Exists,vts,f1) -> wr_binder "EX" vts f1
| Binder(Lambda,vts,f1) -> wr_binder "%" vts f1
| Binder(Comprehension,[(v,t)],f1) ->
    "{" ^ isabelle_ident v ^ ". " ^ wr_form f1 ^ "}"
| Binder(Comprehension,vts,f1) -> 
    "{" ^ wr_binder "" vts  f1 ^ "}"
| TypedForm(TypedForm(f1,t1),t2) -> wr_form (TypedForm(f1,t2))
| TypedForm(f,TypeUniverse) -> wr_form f
| TypedForm(f1,t) -> 
    if (ftv t)=[] then p (wr_form f1 ^ " :: " ^ wr_type t)
    else wr_form f1
| App(f1,fs) -> wr_form_list " " (f1::fs)
and wr_form_list1 op fs = match fs with
| [] -> ""
| [f] -> wr_form f
| f::fs1 -> wr_form f ^ op ^ wr_form_list1 op fs1

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

let quoted_form f = "\"" ^ string_of_form f ^ "\""


(*
let isabelle_input (mod_name:string) (proof:string) (sq:string) =
  "theory vc = " ^ mod_name ^ ":\n" ^
   "lemma \"" ^ sq ^ "\"\n" ^ proof ^ "\nend\n"
*)
