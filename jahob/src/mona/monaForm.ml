(** Abstract syntax tree of MONA formulas and programs. *)

type ident = string

and program = header * decl list

and header =
  | Ws1s
  | Ws2s
  | M2l_str
  | M2l_tree

and decl =
  | FormDecl of form
  | Guide of (ident * ident * ident) list
  | Universe of univarg list
  | Include of string
  | Assert of form
  | Execute of form
  | Const of ident * int (* TODO: replace int by intExp *)
  | Defaultwhere1 of ident * form
  | Defaultwhere2 of ident * form
  | VarDecl0 of ident list
  | VarDecl1 of ident list * varwhere list 
  | VarDecl2 of ident list * varwhere list 
  | TreeDecl of ident list * varwhere list
  | Macro of ident * param list * form
  | PredDecl of ident * param list * form
  | Allpos of ident
  | TypeDecl of ident * (ident * (ident * ident) list) list

and form = 
  | Atom of atomForm
  | Not of form
  | And of form list
  | Or of form list
  | Impl of form * form
  | Iff of form * form
  | Restrict of form
  | Prefix0 of form
  | Export of string * form
  | Import of string * (ident * ident) list 
  | Quant of qkind * ident list * ident list * form
  | Let0 of (ident * form) list * form
  | Let1 of (ident * form) list * form
  | Let2 of (ident * form) list * form
  | Pred of ident * exp list

and atomForm = 
  | True
  | False
  | Eq1 of term1 * term1
  | Neq1 of term1 * term1
  | Lt1 of term1 * term1
  | Gt1 of term1 * term1
  | Leq1 of term1 * term1
  | Geq1 of term1 * term1
  | Eq2 of term2 * term2
  | Neq2 of term2 * term2
  | Sub of term2 * term2
  | Elem of term1 * term2
  | Nelem of term1 * term2
  | Empty of term2
  | Root0 of term1 * ident list
  | InStateSpace of term1 * ident list
  | Variant of term1 * ident * ident * ident
  | Tree of ident
  | Type of term1 * ident
  | Sometype1 of term1
  | Sometype2 of term2
  
and term1 = 
  | Var1 of ident
  | Succ1 of term1 * succ list
  | Prefix1 of term1
  | Root1 of ident option
  | TreeRoot of term2
  | Succ of term1 * ident * ident * ident
  | IntConst of int
  | Plus of term1 * int
  | Minus of term1 * int
  | Max of term2
  | Min of term2

and term2 = 
  | Emptyset
  | Var2 of ident
  | Set of term1 list
  | Union of term2 * term2
  | Inter of term2 * term2
  | Diff of term2 * term2
  | Succ2 of term2 * succ list
  | Prefix2 of term2
  | ConstTree of term1 * ident * consttree

and consttree =
  | V of ident * consttree list

and param =
  | VarPar0 of ident list
  | VarPar1 of varwhere list 
  | VarPar2 of varwhere list
  | UnivPar of ident 

and varwhere = ident * form option

and univarg = ident * univ option

and univ =
  | UnivSucc of succ list
  | UnivTree of ident

and exp =
  | Form of form
  | Term1 of term1
  | Term2 of term2

and qkind = 
  | Exists0 | Exists1 | Exists2 
  | Forall0 | Forall1 | Forall2 

and succ = | L | R





