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

Require Import Arith QArith Bool.

Require Import Ynot.Axioms Ynot.PermModel.

Set Implicit Arguments.

Axiom axiom_ptr : Set.

Definition ptr := axiom_ptr.

Axiom axiom_ptr_eq_dec : forall (a b : ptr), {a = b} + {a <> b}.

Definition ptr_eq_dec := axiom_ptr_eq_dec.
(** Definition ptr := nat. **)

Definition hval := (dynamic * perm)%type.

Definition heap := ptr -> option hval.

Definition val (v:hval) := fst v.
Definition frac (v:hval) := snd v.

Definition hval_plus (v1 v2 : hval) :=
  (val v1,frac v1+frac v2).

Lemma hval_plus_comm (v1 v2 : hval) : val v1 = val v2 -> hval_plus v1 v2 = hval_plus v2 v1.
Proof.
  intros. unfold hval_plus. rewrite H. rewrite Qcplus_comm. trivial.
Qed.


Definition hvalo_plus (v1 v2 : option hval) :=
  match v1 with
    | None => v2
    | Some v1' =>
      match v2 with
        | None => v1
        | Some v2' => Some (hval_plus v1' v2')
      end
  end.

Bind Scope heap_scope with heap.
Delimit Scope heap_scope with heap.

Local Open Scope heap_scope.

Notation "v1 +o v2" := (hvalo_plus v1 v2) (at level 60, no associativity) : heap_scope.

(* Lemma ofrac_hvalo_plus (v1 v2 : option hval) (pf:v1|+?|v2): ofrac (v1 +o v2) == (ofrac v1) + (ofrac v2).
Proof. destruct v1; destruct v2; intuition (simpl; ring). Qed. *)

Definition empty : heap := fun _ => None.
Definition singleton (p : ptr) (v : hval) : heap :=
  fun p' => if ptr_eq_dec p' p then Some v else None.
Definition read (h : heap) (p : ptr) : option hval := h p.
Definition write (h : heap) (p : ptr) (v : hval) : heap :=
  fun p' => if ptr_eq_dec p' p then Some v else h p'.
Definition free (h : heap) (p : ptr) : heap :=
  fun p' => if ptr_eq_dec p' p then None else h p'.

Infix "|-->" := singleton (at level 35, no associativity) : heap_scope.
Notation "a # b" := (read a b) (at level 55, no associativity) : heap_scope.
Notation "h ## p <- v" := (write h p v) (no associativity, at level 60, p at next level) : heap_scope.
Infix "###" := free (no associativity, at level 60) : heap_scope.

(*Definition join_valid (h1 h2:heap) := forall p, (p h1) |+?| (p h2).
Infix "|*|" := join_valid (at level 40, left associativity) : heap_scope.
*)
Definition join (h1 h2 : heap) : heap := fun p =>
  (h1 p) +o (h2 p).

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

Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ => idtac
  end.

Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.

(*
Add Morphism Qeq_bool 
  with signature Qeq ==> Qeq ==> eq
  as Qeq_bool_compat.
Proof.
  intros. 
  repeat match goal with
    [|- context [Qeq_bool ?x ?y]] =>  generalize (Qeq_bool_iff x y); intro; destruct (Qeq_bool x y)
  end; trivial;

  repeat match goal with
    | [H: ?x = ?x <-> ?P |- _] => generalize ((proj1 H) (refl_equal x)); clear H; intro H
    | [H: ?k1 == ?k2 |- _] => extend (Qeq_sym _ _ H)
    | [H1:?k1 == ?k2, H2:?k1 == ?k3 |- _] => extend (Qeq_trans _ _ _ (Qeq_sym _ _ H1) H2)
    | [H1: ?x <-> ?y, H2:?y |- _] => generalize ((proj2 H1) H2); clear H1; intro H1
  end;

  discriminate.
Qed.

Add Morphism Qle_bool 
  with signature Qeq ==> Qeq ==> eq
  as Qle_bool_compat.
Proof.
  intros.
  assert (HH: x1 <= x2 /\ x2 <= x1). rewrite H. split; apply Qle_refl.
  assert (HH2: x0 <= x3 /\ x3 <= x0). rewrite H0. split; apply Qle_refl.
  destruct HH; destruct HH2.
  repeat match goal with
    [|- context [Qle_bool ?x ?y]] =>  generalize (Qle_bool_iff x y); intro; destruct (Qle_bool x y)
  end; trivial;

  repeat match goal with
    | [H: ?x = ?x <-> ?P |- _] => generalize ((proj1 H) (refl_equal x)); clear H; intro H
    | [H1:?k1 <= ?k2, H2:?k2 <= ?k3 |- _] => extend (Qle_trans _ _ _ H1 H2)
    | [H1: ?x <-> ?y, H2:?y |- _] => generalize ((proj2 H1) H2); clear H1; intro H1
  end;

  discriminate.
Qed.

Add Morphism Qlt_bool 
  with signature Qeq ==> Qeq ==> eq
  as Qlt_bool_compat.
Proof.
  intros. unfold Qlt_bool.
  rewrite H. rewrite H0. trivial.
Qed.

Add Morphism valid_plus_bool
  with signature Qeq ==> Qeq ==> eq 
    as valid_plus_bool_compat.
Proof.
  intros. unfold valid_plus_bool.
  rewrite H. rewrite H0. trivial.
Qed.

Add Morphism valid_plus 
  with signature Qeq ==> Qeq ==> iff
    as valid_plus_compat.
Proof.
  unfold valid_plus. intros.
  rewrite H. rewrite H0. intuition.
Qed.
*)
Lemma valid_plus_bool_comm (q1 q2 : Qc) : valid_plus_bool q1 q2 = valid_plus_bool q2 q1.
Proof. intros. unfold valid_plus_bool.
       rewrite Qcplus_comm. 
       rewrite andb_comm. f_equal.
       rewrite orb_comm. f_equal.
Qed.

Lemma valid_plus_comm (q1 q2 : Qc) : q1 |+| q2 -> q2 |+| q1.
Proof.
  intros. unfold valid_plus. rewrite valid_plus_bool_comm. trivial. 
Qed.

Hint Resolve valid_plus_comm : Ynot.

Theorem read_empty : forall p,
  empty # p = None.
  trivial.
Qed.

Theorem read_singleton_same : forall p d,
  (p |--> d) # p = Some d.
  unfold read, singleton; intros.
  destruct (ptr_eq_dec p p); tauto.
Qed.

Theorem read_singleton_diff : forall p d p',
  p' <> p
  -> (p |--> d) # p' = None.
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

(* in a total heap, everything has permission 0 *)

Definition total_heap (h:heap) := forall p, 
  match (h p) with
    | None => True
    | Some v => frac v = 0
  end.

Theorem total_heap_empty : total_heap empty.
Proof. 
  unfold total_heap, empty; intuition.
Qed.

Lemma total_heap_new h p A (v:A): total_heap h -> total_heap (h ## p <- (Dyn v, 0)).
Proof.
  unfold write, total_heap; intuition.
  destruct (ptr_eq_dec p0 p); simpl; trivial.
  generalize (H p0). destruct (h p0); trivial.
Qed.

Lemma total_heap_free h p : total_heap h -> total_heap (h ### p).
Proof.
  unfold free, total_heap; intuition.
  destruct (ptr_eq_dec p0 p); simpl; trivial.
  generalize (H p0). destruct (h p0); trivial.
Qed.

Hint Resolve total_heap_empty total_heap_new total_heap_free : Ynot.

