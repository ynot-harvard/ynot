(*******************************************************************)
(* A trivial implementation of the FINITE_MAP interface where we   *)
(* use a ref to an association list.                               *)
(*******************************************************************)

Require Import Ynot.
Require Import Examples.FiniteMap.
Set Implicit Arguments.

Module RefAssocList(Assoc:ASSOCIATION) : FINITE_MAP with Module A := Assoc.
  Open Local Scope hprop_scope.

  Module AT <: FINITE_MAP_AT with Module A:=Assoc.
    Module A := Assoc.
    Module AL := AssocList(Assoc).
    Definition fmap_t := ptr.
    Definition rep(x:fmap_t)(y:AL.alist_t) := (x --> y).
  End AT.

  Module T:=FINITE_MAP_T(Assoc)(AT).
  Module A := T.A.
  Module AL := T.AL.

  Import AT AL.
  Open Local Scope stsepi_scope.

  Ltac s := T.unfm_t; intros.
  Ltac t := unfold rep; sep ltac:(subst; auto).

  Definition new : T.new. s;
    refine ({{New nil_al}})
  ; t. Defined.

  Definition free : T.free. s;
    refine ({{Free x}})
  ; t. Defined.

  Definition lookup : T.lookup. s;
    refine (z <- ! x ; 
            {{Return (lookup k z)}})
  ; t. Defined.

  Definition insert :  T.insert. s;
    refine (z <- ! x ;
            {{x ::= ((k,, v):: (remove k z))}})
  ; t. Defined.

  Definition remove : T.remove. s;
    refine (z <- ! x ;
            {{x ::= (remove k z)}})
  ; t. Defined.

End RefAssocList.
