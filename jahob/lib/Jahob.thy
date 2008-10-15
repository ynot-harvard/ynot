header {* Jahob background theory *}
theory Jahob

imports Main

begin

section {* Objects *}

typedecl obj

types objset = "obj set"

consts
  null :: obj

constdefs 
  Object :: "obj set"
  "Object == UNIV"

axioms
  objFinite: "finite Object"

types
  'v field = "obj => 'v"

constdefs
  fieldRead :: "'v field => obj => 'v"
  "fieldRead f x == f x"

  fieldWrite :: "'v field => obj => 'v => 'v field"
  "fieldWrite f x v == f(x := v)"

declare 
  fieldRead_def [simp]
  fieldWrite_def [simp]

text {* The following property of object-valued fields should prevent
  null dereferences to be considered as dangling pointers. *}
constdefs
  goodfield :: "obj field => bool"
  "goodfield f == (fieldRead f null = null)"

constdefs
  fg :: "('a => 'b) => ('a * 'b) set"
  -- {* functiong graph, converts fields to relations *}
  "fg f == {p. EX x. p=(x,f x)}"

constdefs
  fgraph :: "(obj => obj) => (obj * obj) set"
  -- {* functiong graph, converts fields to relations *}
  "fgraph f == {p. EX x. p=(x,f x) & x ~= null & f x ~= null}"

declare fgraph_def [simp]

text {* Lemma about updates of function graphs *}
lemma fg_upd [simp]: "fg (f(x:=y)) = fg f - {(x,f x)} Un {(x,y)}"
by (auto simp add: fg_def)

text {* Function graphs are functional (single-valued) *}
lemma fg_single_val: "single_valued (fg f)"
by (simp add: fg_def single_valued_def)

section {* Values *}

datatype valu = 
  ObjValue obj | IntValue int

subsection {* Java Arrays *}

text {* A value array is a function from integers to values. *}

types 'v varray = "int => 'v"

text {* A Java array is an object that has 
  an associated length and a value array.  There are two
  kinds of java arrays: arrays of objects and arrays of primitive
  types. *}

consts
  -- {* objects that are arrays *}
  allArrayObjs :: "obj set"
  -- {* int-valued arrays *}
  intArrayObjs :: "obj set"
  -- {* object-valued arrays *}
  objArrayObjs :: "obj set"

axioms
  intArraySubAll:  "intArrayObjs <= allArrayObjs"
  objArraySubAll:  "objArrayObjs <= allArrayObjs"
  intObjArrayDisj: "intArrayObjs Int objArrayObjs = {}"

types
  arrayLengthType = "int field"
  'a arrayType = "('a varray) field"
  arrayIntsType = "(int varray) field"
  arrayObjsType = "(obj varray) field"

consts
  -- {* Array length, applicable to allArrayObjs *}
  arrayLength :: arrayLengthType
  -- {* Array contents, applicable to allArrayObjs *}
  array :: "'a arrayType"

constdefs
  arrayRead :: "('a varray) field => obj => int => 'a"
  "arrayRead a o1 i == a o1 i"

constdefs
  arrayRead1 :: "obj => int => 'a"
  "arrayRead1 o1 i == arrayRead array o1 i"

constdefs
  arrayWrite :: "('a varray) field => obj => int => 'a => ('a varray) field"
  "arrayWrite a o1 i v == a(o1:=(a o1)(i:=v))"

declare 
  arrayRead_def  [simp]
  arrayRead1_def [simp]
  arrayWrite_def [simp]

section {* Locations *}

types varname = string

datatype loc =
    VarLoc   varname         ("@")
  | FieldLoc obj varname
  | ArrayLoc obj int

section {* Relations *}

constdefs
  elemImage :: "obj => (obj * obj) set => obj set"
  "elemImage x r == {y. (x,y):r}"

section {* Syntactic Sugar *}

syntax
  "_field_read" :: "['a, 'a] => 'a"      (infixl ".." 300)
  "_array_read" :: "['a, 'a] => 'a"      ("_ .[/ _ ]" [300, 301] 300)  
  "_field_loc"  :: "['a, 'a] => 'a"      (infixl "@." 300)
  "_array_loc"  :: "['a, 'a] => 'a"      ("_ @[/ _ ]" [300, 301] 300)
  "_relation_read" :: "['a, 'a] => 'a"      ("_ $[/ _ ]" [300, 301] 300)  
  "_prefix_relread" :: "['a, 'a] => 'a"      ("_ $ _ " [300, 301] 300)

translations
  "x .. f"   == "fieldRead f x"
  "a .[ i ]" == "arrayRead1 a i"
  "x @. f"   == "FieldLoc f x"
  "a @[ i ]" == "ArrayLoc a i"
  "r $[ x ]" == "elemImage x r"
  "x $ r"    == "elemImage x r"

constdefs
  example_use_of_transl1 :: "obj => obj field => int => obj"
  "example_use_of_transl1 a next i == a..next.[i]"
constdefs
  example_use_of_transl2 :: "obj => obj field => int => loc"
  "example_use_of_transl2 a next i == ((a..next) @[ i ])"
constdefs
  example_use_of_transl3 :: "obj => (obj * obj) set => obj set"
  "example_use_of_transl3 x r == (x $ r - r $[ x ])"

lemma example_use3_lemma: "example_use_of_transl3 x r = {}"
apply (unfold example_use_of_transl3_def)
apply simp
done

section {* Cardinality constraints *}

constdefs
  cardleq1 :: "'a set => bool"
  "cardleq1 x == (x={} | (EX x0. x={x0}))"

constdefs
  cardeq1 :: "'a set => bool"
  "cardeq1 x == (EX x0. x={x0})"

constdefs
  comment :: "string => 'a => 'a"
  "comment s f == f"

(*
lemma "(comment ['f';'oo"" x) = (comment ""bar"" x)"

lemma "''Foo'' = CHR ''F'' # ''oo''"
apply simp
done

*)

declare comment_def [simp]

(* Thomas's rtrancl, here called rtrancl_pt (rtrancl predicate transformer) *)

constdefs
  rtrancl_pt :: "('a => 'a => bool) => 'a => 'a => bool"
  "rtrancl_pt p x y == ((x,y) : rtrancl {(u,v). p u v})"

declare rtrancl_pt_def [simp]

(* Shorthand, useful for lists *)

constdefs
  fclosure :: "(obj => obj) => obj => obj => bool"
  "fclosure f == rtrancl_pt (% x y. f x = y)"

declare fclosure_def [simp]

(* Shorthands for lists and trees *)

constdefs
  injective_fun :: "(obj => obj) => bool"
  "injective_fun f == (ALL x y. x ~= null & y ~= null & f x = f y --> x=y)"

constdefs
  acyclic_fun :: "(obj => obj) => bool"
  "acyclic_fun f == (ALL x. x ~= null --> (x,x) ~: trancl {(x,y). f x=y})"

constdefs
  acyclic_list :: "(obj => obj) => bool"
  "acyclic_list f == injective_fun f & acyclic_fun f & f null = null"

constdefs
  acyclic_list_start :: "(obj => obj) => obj => bool"
  "acyclic_list_start f n == (ALL v. (f v = n) --> (v = null))"

(* Finite cardinality as a function into integers *)

constdefs
  fcard :: "'a set => int"
  "fcard s == int (card s)"  (* just change the result type *)

lemma "~ finite s ==> fcard s = 0"
by (simp add: fcard_def)

(* Some non-overloaded versions of operators *)

constdefs
  intless :: "int => int => bool"
  "intless x y == (x < y)"

  intplus :: "int => int => int"
  "intplus x y == (x + y)"

  intminus :: "int => int => int"
  "intminus x y == (x - y)"

  inttimes :: "int => int => int"
  "inttimes x y == (x * y)"

declare 
  intless_def [simp] 
  intplus_def [simp] 
  intminus_def [simp] 
  inttimes_def [simp]

constdefs
  "op ===" :: "'a set => 'a set => bool" ("(_/ === _)" [50, 51] 50) -- "set equality"
  "(x === y) == (x=y)"
  
declare "Jahob.op ===_def" [simp]

constdefs
  "op <==" :: "'a set => 'a set => bool" ("(_/ <== _)" [50, 51] 50) -- "set subset"
  "(x <== y) == (x \<subseteq> y)"

constdefs
  "op \<setminus>" :: "'a set => 'a set => 'a set" ("(_/ \<setminus> _)" 
                           [50, 51] 50) -- "set difference"
  "(x \<setminus> y) == (x - y)"
  
declare "Jahob.op ===_def" [simp]
declare "Jahob.op <==_def" [simp]
declare "Jahob.op \<setminus>_def" [simp]

constdefs
  "op <->" :: "bool => bool => bool" ("(_/ <-> _)" [50, 51] 50) -- "logical equivalence"
  "(x <-> y) == (x = y)"

declare "Jahob.op <->_def" [simp]

constdefs
  pointsto :: "obj set => (obj => obj) => obj set => bool"
  "pointsto a f b == ALL (x::obj). x:a --> (x..f):b"

declare pointsto_def [simp]

lemmas linear_rews =
  add_assoc add_commute diff_def minus_add_distrib minus_minus minus_zero

end