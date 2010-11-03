(* Copyright (c) 2008, Harvard University
 * All rights reserved.
 *
 * Author: Avi Shinnar
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - The names of contributors may not be used to endorse or promote products
 *   derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

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
  Declare Module AT : FINITE_MAP_AT with Module A:=A.
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
