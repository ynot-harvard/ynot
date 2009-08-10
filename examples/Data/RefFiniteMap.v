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

(*******************************************************************)
(* A trivial implementation of the FINITE_MAP interface where we   *)
(* use a ref to an association list.                               *)
(*******************************************************************)

Require Import Ynot.
Require Import Data.FiniteMap.
Set Implicit Arguments.

Module RefAssocList(Assoc:ASSOCIATION) : FINITE_MAP with Module A := Assoc.
  Open Local Scope hprop_scope.

  Module AT <: FINITE_MAP_AT with Module A:=Assoc.
    Module A := Assoc.
    Module AL := AssocList(Assoc). Import AL.
    Definition fmap_t := ptr.
    Definition rep(x:fmap_t)(y:alist_t) := Exists y' :@ alist_t, (x --> y') * [distinct y] * [Permutation y y'].
  End AT.

  Module T:=FINITE_MAP_T(Assoc)(AT).
  Module A := T.A.
  Module AL := T.AL.

  Import AT AL.
  Open Local Scope stsepi_scope.

  Ltac s := T.unfm_t; intros.
  Ltac t := unfold rep, insert; sep fail ltac:(subst; auto); autorewrite with AssocListModel; sep fail ltac:(eauto).

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

  Lemma perm : T.perm. s; t. Qed.
  Lemma distinct : T.distinct. Hint Resolve himp_any_conc. s; t. Qed.

End RefAssocList.
