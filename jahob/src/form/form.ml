(** Abstract syntax tree of Isabelle-like formulas. *)

(** Identifiers are just strings. *)
type ident = string

(** Types in formulas.                         

    Types may contain a little more information
    from the underlying language than is eventually used in Isabelle, 
    because many things are encoded as 'object'.
*)

(** Basic type expression. *)
type simpleType = 
  | TypeUnit   (** unit type *)
  | TypeInt    (** int type *)
  | TypeString (** string type *)
  | TypeBool   (** bool type *)
  | TypeObject (** object type *)
  | TypeSet    (** set type constructor *)
  | TypeList   (** list type constructor *)
  | TypeArray  (** array type constructor *)
  | TypeDefined of ident (** user-defined type *)

(** Type formula *)
type typeForm = 
  | TypeUniverse (** universal or omitted type *)
  | TypeVar of ident (** quoted type variable such as 'a *)
  | TypeApp of simpleType * typeForm list (** application of a constructor *)
  | TypeFun of typeForm list * typeForm (** function type *)
  | TypeProd of typeForm list (** product type *)

(** Type definitions -- not really used for now. *)

(** Body of a type definition *)
type typeDefBody = 
  | SumType of (ident * typeForm) list (** constructor, alternative *)
  | RecordType of (ident * typeForm) list (** field name, definition *)
  | Synonym of typeForm

(** Definition of a user-defined type. *)
type typeDef = {
    typDefName : ident;
    typDefTypeVars : ident list;
    typDefBody : typeDefBody;
  }

(** Here are some examples of representing types using {!typeForm} values.

   TypeSimple TypeInt                       -- int

   TypeApp(TypeSet,[TypeSimple TypeObject]) -- set of objects

   TypeApp(TypeSet,TypeVar "a")             -- 'a set
*)

(** The definitions below define formulas. *)

(** Some constants. Similar to predefined variables, but recognized by parser. *)
type constValue =
    Eq | MetaEq | Elem
  | Or | And | MetaAnd | Not | Impl | MetaImpl | Iff | Disjoint
  | Lt | Gt | LtEq | GtEq (* integer comparisons *)
  | Card | Cardeq | Cardleq | Cardgeq (* set card constrs *)
  | ArrayRead | ArrayWrite (* arrays *) 
  | FieldWrite | FieldRead
  | Cap | Cup | Diff (* sets *)
  | Subseteq | Subset | Seteq
  | UMinus | Plus | Minus | Mult | Div | Mod 
  | IntConst of int | BoolConst of bool | NullConst 
  | StringConst of string
  | EmptysetConst | FiniteSetConst
  | Tuple | ListLiteral
  | Let
  | Rtrancl | Rimage
  | Unit | Comment | Old | ObjLocs
  | Ite

(** String representation of constants. *)
let string_of_const (c:constValue) = match c with
| Eq -> "=" | MetaEq -> "==" | Elem -> ":"
| Or -> "|" | And -> "&" | MetaAnd -> ";" | Not -> "~" 
| Impl -> "-->" | MetaImpl -> "==>" | Iff -> "="
| Disjoint -> "disjoint"
| Lt -> "<" | Gt -> ">" | LtEq -> "<=" | GtEq -> ">="
| Card -> "card" | Cardeq -> "cardeq" | Cardleq -> "cardleq" 
| Cardgeq -> "cardgeq" 
| Old -> "old" | ObjLocs -> "objlocs"
| ArrayRead -> "arrayRead" | ArrayWrite -> "arrayWrite" 
| Cap -> "Int" | Cup -> "Un" | Diff -> "-" 
| UMinus -> "-"
| Plus -> "+" | Minus -> "-" | Mult -> "*" | Div -> "div" | Mod -> "mod"
| IntConst k -> string_of_int k
| StringConst s -> "''" ^ s ^ "''"
| BoolConst true -> "true" | BoolConst false -> "false"
| NullConst -> "null" | EmptysetConst -> "{}"
| FieldWrite -> "fieldWrite" | FieldRead -> "fieldRead"
| FiniteSetConst -> "finiteSet"
| Tuple -> "tuple" | ListLiteral -> "list"
| Let -> "Let"
| Unit -> "()" | Comment -> "comment"
| Subseteq -> "\\<subseteq>" | Subset -> "\\<subset>" | Seteq -> "\\<seteq>"
| Rtrancl -> "rtrancl" | Rimage -> "``"
| Ite -> "If then else"

(** Identifier along with its type, used in binders. *)
type typedIdent = ident * typeForm

(** Built-in binders. Others may be simulated with Lambda. *)
type binderKind =
  | Lambda (** lambda binding *)
  | Forall (** universal quantifier *)
  | Exists (** existential quantifier *)
  | Comprehension (** set comprehension *)

(** The main definition: Isabelle/HOL - like formulas. *)
type form =
  | Var of ident (** variable *)
  | Const of constValue (** constant *)
  | App of form * form list (** function application *)
  | Binder of binderKind * (typedIdent list) * form (** binder *)
  | TypedForm of form * typeForm (** formula with explicit type *)

(** Formula, type, or a list of formulas.
    Used for returning the result of parsing formula-like inputs. *)
type typeOrForm =
  | AForm of form (** formula *)
  | AType of typeForm (** type *)
  | AFormList of form list (** list of formulas *)

type typeEnv = typedIdent list

type formenv = form * typeEnv

type sequent = form list * form

type sequentenv = sequent * typeEnv

type obligation = {
  ob_pos : Common.source_pos;
  ob_purpose : string;
  ob_form : form;
}

type sq_obligation = {
  sqob_pos : Common.source_pos;
  sqob_purpose : string;
  sqob_sq : sequent;
}
