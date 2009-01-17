(* Copyright (c) 2008, Harvard University
 * All rights reserved.
 *
 * Author: Gregory Malecha
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

Require Import Ynot.
Require Import Basis.
Require Import Examples.LinkedListSeg.
Require Import Ascii.
Require Import List.

Open Local Scope char_scope.
Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.

Module CharDecDomain : DECIDABLE_DOMAIN with Definition A := ascii.
  Definition A : Set := ascii.

  Definition eq_bool : forall (a b : bool), {a = b} + {a <> b}.
    decide equality.
  Qed.
  Definition eq_a : forall (a b : A), {a = b} + {a <> b}.
    decide equality; apply eq_bool.
  Qed.
End CharDecDomain.

Module CharLL := HeapLinkedList(CharDecDomain).
Export CharLL.A.

Lemma nil_empty : forall p q, CharLL.llseg p q nil ==> __.
  intros.
  apply (@himp_trans [p = q]).
  apply CharLL.nil_empty.
  sep fail auto.
Qed.
Hint Resolve nil_empty.

Theorem himp_unpack_conc_meta : forall T x (y:[T]) p1 p2 p,
  p ==> p1 x * p2
  -> y = [x]%inhabited
  -> p ==> hprop_unpack y p1 * p2.
  unfold hprop_imp, hprop_unpack, hprop_sep; subst; firstorder.
  generalize (H _ H1).
  firstorder.
Qed.

Definition main : STsep (__) (fun _:unit => __).
   refine (
     hello <- CharLL.empty;
     hello <- CharLL.cons " " hello [None] _;
     hello <- CharLL.cons "o" hello [None] _;
     hello <- CharLL.cons "l" hello [None] _;
     hello <- CharLL.cons "l" hello [None] _;
     hello <- CharLL.cons "e" hello [None] _;
     hello <- CharLL.cons "h" hello [None] _;

     world <- CharLL.empty <@> _;
     world <- CharLL.cons "!" world [None] _ <@> _;
     world <- CharLL.cons "d" world [None] _ <@> _;
     world <- CharLL.cons "l" world [None] _ <@> _;
     world <- CharLL.cons "r" world [None] _ <@> _;
     world <- CharLL.cons "o" world [None] _ <@> _;
     world <- CharLL.cons "w" world [None] _ <@> _;

     hello_world <- CharLL.append hello world _ _ <@> _;
     
     str <- CharLL.elements hello_world _ _;
     printStringLn' (str) <@> _;;
     hello_world <- CharLL.freeList hello_world None _;
     {{Return tt}}
   );
   try solve [ sep fail auto 
             | intros; inhabiter; unpack_conc; sep fail auto ].
   unfold CharLL.llist; intros; inhabiter; unpack_conc; sep fail auto.
   unfold CharLL.llist; intros; inhabiter; unpack_conc; sep fail auto.
 Qed.