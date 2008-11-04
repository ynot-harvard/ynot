(* This file defines the interface for an imperative FiniteMap, which
   is modeled by a function association list *)

Require Import Ynot.
Require Export AssocListModel.

Set Implicit Arguments.

(*********************************************************************************)
(* This defines the type of the abstract object and its representation invariant *)
(*********************************************************************************)

Module Type FINITE_MAP_AT.
  Declare Module A:ASSOCIATION.
  Module AL := AssocList(A).

  (* The finite map's implementation's type *)
  Variable fmap_t : Set.

  (* Its representation invariant: relates an object and a functional model in a given heap *)
  Variable rep : fmap_t -> AL.alist_t -> hprop.
End FINITE_MAP_AT.

(*********************************************************************************************)
(* The types of the finite map operations, relative to its implementation type and invariant *)
(*********************************************************************************************)
Module FINITE_MAP_T(Assoc:ASSOCIATION)(AT:FINITE_MAP_AT with Module A:=Assoc).
  Module A := AT.A.
  Module AL := AT.AL.

  Import A AT AL.

  Open Local Scope hprop_scope.

  (* Allocates a new finite map *)
  Definition new := 
    STsep __ (fun (ans:fmap_t) => rep ans nil_al).

  (* Frees a finite map *)
  Definition free := 
    forall (x:fmap_t)(l:[alist_t]), STsep (l ~~ rep x l) (fun (_:unit) => __).

  (* Inserts a new key, value pair into the finite map. If the finite map already contains a
     pair with the same key, it is overwritten *)
  Definition insert :=
    forall (x:fmap_t)(k:key_t)(v:value_t k)(l:[alist_t]),
      STsep (l ~~ rep x l)
        (fun (_:unit) => l ~~ rep x (insert v l)).

  (* Returns Some(the value) corresponding to the given key in the finite map. 
     Returns None if the key is not in the finite map *)
  Definition lookup :=
    forall (x:fmap_t)(k:key_t)(l:[alist_t]), 
      STsep (l ~~ rep x l) 
            (fun (ans:option (value_t k)) =>
               l ~~ [ans = lookup k l] * rep x l).

  (* If the finite map contains a pair with the given key, it is
     removed.  Otherwise, nothing happens. *)
  Definition remove :=
    forall (x:fmap_t)(k:key_t)(l:[alist_t]),
      STsep (l ~~ rep x l)
        (fun (_:unit) => l ~~ rep x (remove k l)).

  (* Models of finite maps do not have any duplicate keys. *)
  Definition distinct := forall (x:fmap_t) (l:alist_t), rep x l ==> [distinct l] * ??.

  (* All permutations of a model are equally valid models of a finite map. *)
  Definition perm := forall (x:fmap_t) (l l':alist_t), Permutation l l' -> rep x l ==> rep x l'.

  (* A simple tactic to unfold these types *)
  Ltac unfm_t := unfold new, free, insert, lookup, remove, distinct, perm.

End FINITE_MAP_T.

(*******************************************************************)
(* The finite-map interface, relative to an ASSOCIATION definition *)
(*******************************************************************)
Module Type FINITE_MAP.
  Declare Module A  : ASSOCIATION.
  Module AL := AssocList(A).
  Declare Module AT : FINITE_MAP_AT with Module A:=A with Module AL := AL.
  Module T := FINITE_MAP_T(A)(AT).

  Export AT.

  Parameter new : T.new.
  Parameter free : T.free.
  Parameter insert : T.insert.
  Parameter remove : T.remove.
  Parameter lookup : T.lookup.
  Axiom distinct : T.distinct.
  Axiom perm : T.perm.

End FINITE_MAP.
