(* Copyright (c) 2008, Harvard University
 * All rights reserved.
 *
 * Author: Adam Chlipala
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

Require Import Arith.

Require Import Ynot.Axioms.
Require Import Ynot.Heap.
Require Import Ynot.Hprop.

Set Implicit Arguments.


Definition hpre := hprop.
Definition hpost T := heap -> T -> hprop.

Open Local Scope heap_scope.

Parameter ST : hpre -> forall T, hpost T -> Set.

Parameter STReturn : forall T (v : T), ST (fun _ => True) (fun h v' h' => h' = h /\ v' = v).

Parameter STBind : forall (pre : hpre) pre1 T1 (post1 : hpost T1) pre2 T2 (post2 : T1 -> hpost T2) (post : hpost T2),
  ST pre1 post1
  -> (forall v : T1, ST (pre2 v) (post2 v))
  -> (forall h, pre h -> pre1 h)
  -> (forall h v h', pre1 h -> post1 h v h' -> pre2 v h')
  -> (forall h v1 h' v2 h'', pre1 h -> post1 h v1 h' -> pre2 v1 h' -> post2 v1 h' v2 h'' -> post h v2 h'')
  -> ST pre post.

Parameter STContra : forall T (post : hpost T), ST (fun _ => False) post.

Parameter STFix : forall dom (ran : dom -> Type)
  (pre : dom -> hpre) (post : forall v : dom, hpost (ran v))
  (F : (forall v : dom, ST (pre v) (post v))
    -> (forall v : dom, ST (pre v) (post v)))
  (v : dom), ST (pre v) (post v).

Parameter STNew : forall T (v : T),
  ST (fun _ => True) (fun h p h' => h # p = None /\ h' = h##p <- Dyn v).

Parameter STFree : forall p,
  ST (fun h => exists d, h#p = Some d) (fun h (_ : unit) h' => h' = h###p).

Parameter STRead : forall T (p : ptr),
  ST (fun h => exists v : T, h#p = Some (Dyn v)) (fun h (v : T) h' => h' = h /\ h#p = Some (Dyn v)).

Parameter STWrite : forall T T' (p : ptr) (v : T'),
  ST (fun h => exists v : T, h#p = Some (Dyn v)) (fun h (_ : unit) h' => h' = h##p <- Dyn v).

Parameter STStrengthen : forall pre T (post : hpost T) (pre' : hpre),
  ST pre post
  -> (forall h, pre' h -> pre h)
  -> ST pre' post.

Parameter STWeaken : forall pre T (post post' : hpost T),
  ST pre post
  -> (forall h v h', pre h -> post h v h' -> post' h v h')
  -> ST pre post'.

Arguments Scope ST [hprop_scope type_scope hprop_scope].
