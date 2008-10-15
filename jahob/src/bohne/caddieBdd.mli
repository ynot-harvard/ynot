type ddMgr
type bdd
type add
type zadd
type varSet
type varMap

type addOp = AddPlus | AddTimes | AddDivide | AddMinus | AddAgree | AddMax | AddMin
type zaddOp = ZaddAnd | ZaddOr | ZaddNand | ZaddNor | ZaddXor | ZaddXnor

type reorderType = 
    Same
  | NoReorder 
  | Random 
  | RandomPivot 
  | Sift | SiftConv 
  | SymmSift 
  | SymmSiftConv 
  | Window2 | Window3 | Window4 | Window2Conv | Window3Conv | Window4Conv 
  | GroupSift | GroupSiftConv 
  | Anneal | Genetic 
  | Linear | LinearConv | Exact

exception InvalidMgr
exception DifferentMgrs


external init : int -> int -> int -> int -> ddMgr = "caddie_init"
external exit : ddMgr -> unit = "caddie_exit"

external dynEnable: ddMgr -> reorderType -> unit = "caddie_dynEnable"
external dynDisable: ddMgr -> unit = "caddie_dynDisable"

external bddTrue : ddMgr -> bdd = "caddie_true"
external bddFalse : ddMgr -> bdd = "caddie_false"
external addOne : ddMgr -> add = "caddie_true"
external addZero : ddMgr -> add = "caddie_zero"
external zaddOne : ddMgr -> zadd = "caddie_true"
external zaddZero : ddMgr -> zadd = "caddie_zero"
external addPlusInf : ddMgr -> add = "caddie_plusInf"
external addMinusInf : ddMgr -> add = "caddie_minusInf"
external addConst : ddMgr -> float -> add = "caddie_addConst"
external addVal : add -> float = "caddie_addVal"
external addReadBack : ddMgr -> add = "caddie_addReadBack"
external addSetBack : add -> unit = "caddie_addSetBack"
external bddIsConst : bdd -> bool = "caddie_isConst"
external addIsConst : add -> bool = "caddie_isConst"
external zaddIsConst : zadd -> bool = "caddie_isConst"

external bddCountMinterm : ddMgr -> bdd -> int -> float  = "caddie_bddCountMinterm"
external bddIthVar : ddMgr -> int -> bdd = "caddie_bddIthVar"
external bddNewVar : ddMgr -> bdd = "caddie_bddNewVar"
external addIthVar : ddMgr -> int -> add = "caddie_addIthVar"
external addNewVar : ddMgr -> add = "caddie_addNewVar"
external zaddIthVar : ddMgr -> int -> zadd = "caddie_addIthVar"
external zaddNewVar : ddMgr -> zadd = "caddie_addNewVar"

external bddEqual : bdd -> bdd -> bool = "caddie_equal"
external addEqual : add -> add -> bool = "caddie_equal"
external zaddEqual : zadd -> zadd -> bool = "caddie_equal"

external bddNot : bdd -> bdd = "caddie_bddNot"
external bddIte : bdd -> bdd -> bdd -> bdd = "caddie_bddIte"
external bddThen : bdd -> bdd = "caddie_bddThen"
external bddElse : bdd -> bdd = "caddie_bddElse"
external bddAnd : bdd -> bdd -> bdd = "caddie_bddAnd"
external bddNand : bdd -> bdd -> bdd = "caddie_bddNand"
external bddOr : bdd -> bdd -> bdd = "caddie_bddOr"
external bddNor : bdd -> bdd -> bdd = "caddie_bddNor"
external bddXor : bdd -> bdd -> bdd = "caddie_bddXor"
external bddImp : bdd -> bdd -> bdd = "caddie_bddImp"
external bddBiimp : bdd -> bdd -> bdd = "caddie_bddBiimp"

external zaddNot : zadd -> zadd = "caddie_addCmpl"
external zaddApply : zaddOp -> zadd -> zadd -> zadd ="caddie_zaddApply"

external bddFromBool : ddMgr -> bool -> bdd = "caddie_fromBool"
external bddToBool : bdd -> bool = "caddie_toBool"
external zaddFromBool : ddMgr -> bool -> zadd = "caddie_zFromBool"
external zaddToBool : zadd -> bool = "caddie_zToBool"

external empty : ddMgr -> varSet = "caddie_true"
external insertVar : varSet -> int -> varSet = "caddie_addVar"
external singleVar : ddMgr -> int -> varSet = "caddie_bddIthVar"
val fromList : ddMgr -> int list -> varSet

external forall : varSet -> bdd -> bdd = "caddie_forall"
external exists : varSet -> bdd -> bdd = "caddie_exists"

val toMap : ddMgr -> (int*int) list -> varMap

external replace : bdd -> varMap -> bdd = "caddie_replace"

external addApply : addOp -> add -> add -> add = "caddie_addApply"
external addIte : zadd -> add -> add -> add = "caddie_addIte"
external addCmpl : add -> add = "caddie_addCmpl"
external addCompose : add -> zadd -> int -> add = "caddie_addCompose"
external addMax : add -> add = "caddie_addMax"
external addMin : add -> add = "caddie_addMin"

external zaddToAdd : zadd -> add = "caddie_nop"
external zaddToBdd : zadd -> bdd = "caddie_addBddPattern"
external addToBdd : add -> bdd = "caddie_addBddPattern"
external bddToZadd : bdd -> zadd = "caddie_bddAdd"
external bddToAdd : bdd -> add = "caddie_bddAdd"
external addIthBit : add -> int -> bdd = "caddie_addIthBit"

external bddPrint : bdd -> unit = "caddie_print"
external addPrint : add -> unit = "caddie_print"
external zaddPrint : zadd -> unit = "caddie_print"


(* Other useful functions added later by Rupak.
   These are from the Glu bdd.h interface.
   The hope is that ultimately all of that interface
   would be incorporated.
*)
external bddCofactor : bdd -> bdd -> bdd = "caddie_bddCofactor"
external bddVarCofactor : bdd -> bdd -> bdd = "caddie_bddVarCofactor"
external bddCompose : bdd -> bdd -> bdd -> bdd = "caddie_bddCompose"
external bddSubstitute : bdd -> int array -> int array -> bdd = "caddie_bddSubstitute"
external bddTopVar : bdd -> bdd = "caddie_bddTopVar"




external bddIndex : bdd -> int = "caddie_bddIndex"
external bddSupport : bdd -> bdd = "caddie_bddSupport"
external bddSupportSet : bdd -> int list = "caddie_bddSupportSet"

(* Iterate over all cubes of the BDD and invoke the
   function argument on each cube.
   A cube is an array of integers:
   0 -> Corresponding variable is present negatively
   1 -> Corresponding variable is present positively
   2 -> Corresponding variable is not present
*)
external bddForeachCube : bdd -> (int array -> unit) -> unit = "caddie_forEachCube"

(* Iterate over all nodes of the BDD and invoke the function
   argument on each node.
*)
external bddForeachNode : bdd -> (bdd -> unit) -> unit = "caddie_forEachNode"



