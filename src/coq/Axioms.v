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

Require Import Eqdep.

Set Implicit Arguments.


(** * Extensional equality of functions *)

Axiom ext_eq : forall T1 T2 (f1 f2 : T1 -> T2),
  (forall x, f1 x = f2 x) -> f1 = f2.

Theorem ext_eqS : forall (T1 T2 : Set) (f1 f2 : T1 -> T2),
  (forall x, f1 x = f2 x) -> f1 = f2.
  intros; rewrite (ext_eq f1 f2); auto.
Qed.

Ltac ext_eq := (apply ext_eq || apply ext_eqS); intro.


(** * Hidden values *)

Axiom pack_injective : forall (T : Set) (x y : T),
  inhabits x = inhabits y
  -> x = y.


(** * Dynamic packages *)

Inductive dynamic : Type :=
  | Dyn : forall T, T -> dynamic.

Theorem Dyn_inj : forall (T : Set) (x y : T),
  Dyn x = Dyn y
  -> x = y.
  injection 1; intro.
  exact (inj_pair2 _ _ _ _ _ H0).
Qed.


Lemma Dyn_inj_Some' : forall (d1 d2 : dynamic),
  Some d1 = Some d2
  -> d1 = d2.
  congruence.
Qed.

Theorem Dyn_inj_Some : forall (T : Set) (x y : T),
  Some (Dyn x) = Some (Dyn y)
  -> x = y.
  intros.
  apply Dyn_inj.
  apply Dyn_inj_Some'.
  trivial.
Qed.
