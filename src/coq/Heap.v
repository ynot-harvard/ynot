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

Set Implicit Arguments.

Axiom axiom_ptr : Set.

Definition ptr := axiom_ptr.

Axiom axiom_ptr_eq_dec : forall (a b : ptr), {a = b} + {a <> b}.

Definition ptr_eq_dec := axiom_ptr_eq_dec.
(** Definition ptr := nat. **)

Definition heap := ptr -> option dynamic.

Definition empty : heap := fun _ => None.
Definition singleton (p : ptr) (v : dynamic) : heap :=
  fun p' => if ptr_eq_dec p' p then Some v else None.
Definition read (h : heap) (p : ptr) : option dynamic := h p.
Definition write (h : heap) (p : ptr) (v : dynamic) : heap :=
  fun p' => if ptr_eq_dec p' p then Some v else h p'.
Definition free (h : heap) (p : ptr) : heap :=
  fun p' => if ptr_eq_dec p' p then None else h p'.

Infix "-->" := singleton (at level 38, no associativity) : heap_scope.
Infix "#" := read (right associativity, at level 60) : heap_scope.
Notation "h ## p <- v" := (write h p v) (no associativity, at level 60, p at next level) : heap_scope.
Infix "###" := free (no associativity, at level 60) : heap_scope.

Bind Scope heap_scope with heap.
Delimit Scope heap_scope with heap.

Open Local Scope heap_scope.

Definition join (h1 h2 : heap) : heap := fun p =>
  match h1 p with
    | None => h2 p
    | v => v
  end.

Infix "*" := join (at level 40, left associativity) : heap_scope.


(** * Theorems *)

Theorem join_id1 : forall h, empty * h = h.
  intros.
  unfold heap; ext_eq.
  trivial.
Qed.

Theorem join_id2 : forall h, h * empty = h.
  intros.
  unfold heap; ext_eq.
  unfold join.
  destruct (h x); trivial.
Qed.

Hint Resolve join_id1 join_id2 : Ynot.
Hint Rewrite join_id1 join_id2 : Ynot.

Theorem read_empty : forall p,
  empty # p = None.
  trivial.
Qed.

Theorem read_singleton_same : forall p d,
  (p --> d) # p = Some d.
  unfold read, singleton; intros.
  destruct (ptr_eq_dec p p); tauto.
Qed.

Theorem read_singleton_diff : forall p d p',
  p' <> p
  -> (p --> d) # p' = None.
  unfold read, singleton; intros.
  destruct (ptr_eq_dec p' p); tauto.
Qed.

Theorem read_write_same : forall h p d,
  (h ## p <- d) # p = Some d.
  unfold read, write; intros.
  destruct (ptr_eq_dec p p); tauto.
Qed.

Theorem read_write_diff : forall h p d p',
  p' <> p
  -> (h ## p <- d) # p' = h # p'.
  unfold read, write; intros.
  destruct (ptr_eq_dec p' p); tauto.
Qed.

Hint Rewrite read_empty read_singleton_same read_write_same : Ynot.
Hint Rewrite read_singleton_diff read_write_diff using (auto; fail) : Ynot.

Hint Extern 1 (_ # _ = _) => autorewrite with Ynot in * : Ynot.
