header {* Jahob background theory *}
theory ArrayVC

imports Main

begin

subsection {* Objects and Values *}

typedecl obj
types Object = obj

consts
  null :: obj

datatype value = ObjValue obj | IntValue int

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

text {* The next property of object-valued fields should prevent
  null dereferences to be considered as dangling pointers. *}
constdefs
  goodfield :: "obj field => bool"
  "goodfield f == (fieldRead f null = null)"

constdefs
  fg :: "('a => 'b) => ('a * 'b) set"
  "fg f == {p. EX x. p=(x,f x)}"

lemma fg_upd [simp]: "fg (f(x:=y)) = fg f - {(x,f x)} Un {(x,y)}"
by (auto simp add: fg_def)

lemma fg_single_val: "single_valued (fg f)"
by (simp add: fg_def single_valued_def)

(* Arrays *)

   (* Global arrays are not general enough for Java, but we keep them for now. *)
typedecl 'a garray

consts
  arrayRead :: "'a garray => int => 'a"
  arrayWrite :: "'a garray => int => 'a => 'a garray"
  newArray :: "int => 'a => 'a garray"

axioms
  array1_def: "garrayRead (garrayWrite a i x) i = x"
  array2_def: "i ~= j ==> garrayRead (garrayWrite a i x) j = garrayRead a j"
  array3_def: "0 <= i & i < n ==> garrayRead (gnewArray n x) i = x"
  array4_def: "garraySize (garrayWrite a i x) = garraySize a"
  array5_def: "garraySize (gnewArray n x) = n"

   (* Java arrays are objects, so we define functions on objects *)
consts
    
  arrayLookup :: object =>

(* Locations *)

constdefs
  cardleq1 :: "'a set => bool"
  "cardleq1 x == (x={} | (EX x0. x={x0}))"

constdefs
  cardeq1 :: "'a set => bool"
  "cardeq1 x == (EX x0. x={x0})"


end