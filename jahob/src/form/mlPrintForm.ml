open Form
open TypeVars

let p s = "(" ^ s ^ ")"

let wr_list (wr : 'a -> string) (xs : 'a list) : string =
  "[" ^ String.concat "; " (List.map wr xs) ^ "]"

and wr_stype st = match st with
| TypeUnit -> "TypeUnit"
| TypeInt -> "TypeInt"
| TypeString -> "TypeString"
| TypeBool -> "TypeBool"
| TypeObject -> "TypeObject"
| TypeArray -> "TypeArray"
| TypeSet -> "TypeSet"
| TypeList -> "TypeList"
| TypeDefined s -> p ("TypeDefined " ^ s)

let rec wr_type (typ : typeForm) : string =
  match typ with
    | TypeUniverse -> "TypeUniverse"
    | TypeVar tid -> p ("TypeVar " ^ tid)
    | TypeApp(s,ts) -> p ("TypeApp(" ^ wr_stype s ^ "," ^
			    wr_list wr_type ts ^ ")")
    | TypeFun(ts,t) -> p ("TypeFun(" ^ 
			    wr_list wr_type ts ^ ", " ^
			    wr_type t ^ ")")
    | TypeProd ts -> p ("TypeProd " ^ 
			  wr_list wr_type ts)

let string_of_const (c : constValue) : string = match c with 
  | Eq -> "Eq" 
  | MetaEq -> "MetaEq" 
  | Elem -> "Elem"
  | Or -> "Or"
  | And -> "And" 
  | MetaAnd -> "MetaAnd"
  | Not -> "Not" 
  | Impl -> "Impl"
  | MetaImpl -> "MetaImpl" 
  | Iff -> "Iff"
  | Disjoint -> "Disjoint"
  | Lt -> "Lt"
  | Gt -> "Gt" 
  | LtEq -> "LtEq"
  | GtEq -> "GtEq" 
  | Card -> "Card"
  | Cardeq -> "Cardeq" 
  | Cardleq -> "Cardleq"
  | Cardgeq -> "Cardgeq"
  | ArrayRead -> "ArrayRead"
  | ArrayWrite -> "ArrayWrite"
  | FieldWrite -> "FieldWrite"
  | FieldRead -> "FieldRead"
  | Cap -> "Cap"
  | Cup -> "Cup"
  | Diff -> "Diff"
  | Subseteq -> "Subseteq"
  | Subset -> "Subset"
  | Seteq -> "Seteq"
  | UMinus -> "UMins"
  | Plus -> "Plus"
  | Minus -> "Minus"
  | Mult -> "Mult"
  | Div -> "Div"
  | Mod -> "Mod"
  | IntConst x -> p ("IntConst " ^ Printf.sprintf "%d" x)
  | BoolConst b -> p ("BoolConst " ^ Printf.sprintf "%b" b)
  | NullConst -> "NullConst"
  | StringConst s -> p ("StringConst " ^ s)
  | EmptysetConst -> "EmptysetConst"
  | FiniteSetConst -> "FiniteSetConst"
  | Tuple -> "Tuple"
  | ListLiteral -> "List"
  | Let -> "Let"
  | Rtrancl -> "Rtrancl"
  | Rimage -> "Rimage"
  | Unit -> "Unit"
  | Comment -> "Comment" 
  | Old -> "Old"
  | ObjLocs -> "ObjLocs"
  | Ite -> "Ite"

let string_of_binder (b : binderKind) : string =
  match b with
    | Lambda -> "Lambda"
    | Forall -> "Forall"
    | Exists -> "Exists"
    | Comprehension -> "Comprehension"

let wr_tvar ((id,typ) : ident * typeForm) : string =
  "(" ^ id ^ "," ^ wr_type typ ^ ")"

let rec wr_form (f : form) : string = match f with
  | Var id -> p ("Var \"" ^ id ^ "\"")
  | Const c -> p ("Const " ^ string_of_const c)
  | App(f1,fs) -> p ("App(" ^ wr_form f1 ^ "," ^ 
		       wr_list wr_form fs ^ ")")
  | Binder(b,tvs,f1) -> p ("Binder(" ^ string_of_binder b ^ "," ^
			     wr_list wr_tvar tvs ^ "," ^ wr_form f1 ^")")
  | TypedForm(f,typ) -> p ("TypedForm(" ^ wr_form f ^ "," ^ wr_type typ ^ ")")

let string_of_type (t : typeForm) : string = wr_type t  

let string_of_form (f:form) = wr_form f

