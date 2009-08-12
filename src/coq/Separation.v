(* Copyright (c) 2008-2009, Harvard University
 * All rights reserved.
 *
 * Authors: Adam Chlipala, Gregory Malecha
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

Require Import Qcanon.
Require Import Ynot.Axioms.
Require Import Ynot.Util.
Require Import Ynot.PermModel.
Require Import Ynot.Heap.
Require Import Ynot.Hprop.

Set Implicit Arguments.

Theorem himp_refl : forall p, p ==> p.
  unfold hprop_imp; trivial.
Qed.

Theorem himp_any_conc : forall p, p ==> ??.
  unfold hprop_imp, hprop_any; trivial.
Qed.

Theorem himp_empty_prem : forall p q,
  p ==> q
  -> __ * p ==> q.
  unfold hprop_imp, hprop_empty, hprop_sep; firstorder; subst; autorewrite with Ynot; auto.
Qed.

Theorem himp_empty_prem' : forall p q,
  p * __ ==> q
  -> p ==> q.
  unfold hprop_imp, hprop_empty, hprop_sep; firstorder; subst; autorewrite with Ynot; auto.
  apply H.
  eauto with Ynot.
Qed.

Theorem himp_empty_conc : forall p q,
  p ==> q
  -> p ==> __ * q.
  unfold hprop_imp, hprop_empty, hprop_sep; firstorder; subst; autorewrite with Ynot;
    eauto 7 with Ynot.
Qed.

Theorem himp_empty_conc' : forall p q,
  p ==> q * __
  -> p ==> q.
  unfold hprop_imp, hprop_empty, hprop_sep; intuition.
  generalize (H _ H0); clear H H0; firstorder; subst; autorewrite with Ynot; trivial.
Qed.

Theorem himp_comm_prem : forall p q r,
  q * p ==> r
  -> p * q ==> r.
  unfold hprop_imp, hprop_sep; intuition.
  apply H.
  do 2 destruct H0; intuition.
  exists x0; exists x; intuition.
Qed.

Theorem himp_assoc_prem1 : forall p q r s,
  p * (q * r) ==> s
  -> (p * q) * r ==> s.
  unfold hprop_imp, hprop_sep; intuition.
  apply H; clear H.
  destruct H0.
  destruct H; intuition.
  do 2 destruct H; intuition.
  exists x1; exists (x2 * x0)%heap; intuition.
  eapply split_splice'; eauto.
  exists x2; exists x0; intuition.
  eapply split_self; eauto.
Qed.

Theorem himp_assoc_prem2 : forall p q r s,
  q * (p * r) ==> s
  -> (p * q) * r ==> s.
  unfold hprop_imp, hprop_sep; intuition.
  apply H; clear H.
  destruct H0.
  destruct H; intuition.
  do 2 destruct H; intuition.
  exists x2; exists (x1 * x0)%heap; intuition.
  eapply split_splice'; eauto.
  apply split_comm; assumption.
  exists x1; exists x0; intuition.
  eapply split_self; eauto.
  apply split_comm; eassumption.
Qed.

Theorem himp_comm_conc : forall p q r,
  r ==> q * p
  -> r ==> p * q.
  unfold hprop_imp, hprop_sep; intuition.
  generalize (H _ H0); clear H H0; intuition.
  do 2 destruct H; intuition.
  exists x0; exists x; intuition.
Qed.

Theorem himp_assoc_conc1 : forall p q r s,
  s ==> p * (q * r)
  -> s ==> (p * q) * r.
  unfold hprop_imp, hprop_sep; intuition.
  generalize (H _ H0); clear H H0; intuition.
  do 2 destruct H; intuition.
  destruct H2.
  destruct H1; intuition.
  exists (x * x1)%heap; exists x2; intuition.
  eapply split_splice''; eauto.
  exists x; exists x1; intuition.
  eapply split_self'; eauto.
Qed.

Theorem himp_assoc_conc2 : forall p q r s,
  s ==> q * (p * r)
  -> s ==> (p * q) * r.
  unfold hprop_imp, hprop_sep; intuition.
  generalize (H _ H0); clear H H0; intuition.
  do 2 destruct H; intuition.
  destruct H2.
  destruct H1; intuition.
  exists (x1 * x)%heap; exists x2; intuition.
  eapply split_splice'''; eauto.
  exists x1; exists x; intuition.
  eapply split_self''; eauto.
Qed.

Definition isExistential T (x : T) := True.

Lemma isExistential_any : forall T (x : T), isExistential x.
  constructor.
Qed.

Ltac mark_existential e := generalize (isExistential_any e); intro.

Theorem himp_ex_prem : forall T (p1 : T -> _) p2 p,
  (forall v, isExistential v -> p1 v * p2 ==> p)
  -> hprop_ex p1 * p2 ==> p.
  Hint Immediate isExistential_any.

  unfold hprop_imp, hprop_ex, hprop_sep; simpl; intuition.
  do 2 destruct H0; intuition.
  destruct H0.
  eauto 6.
Qed.

Theorem himp_ex_conc : forall p T (p1 : T -> _) p2,
  (exists v, p ==> p1 v * p2)
  -> p ==> hprop_ex p1 * p2.
  unfold hprop_imp, hprop_ex, hprop_sep; firstorder.
  generalize (H _ H0); clear H H0.
  firstorder.
Qed.

Theorem himp_ex_conc_trivial : forall T p p1 p2,
  p ==> p1 * p2
  -> T
  -> p ==> hprop_ex (fun _ : T => p1) * p2.
  unfold hprop_imp, hprop_ex, hprop_sep; firstorder.
  generalize (H _ H0); clear H H0.
  firstorder.
Qed.

Theorem himp_unpack_prem : forall (T : Set) (x : T) p1 p2 p,
  p1 x * p2 ==> p
  -> hprop_unpack [x] p1 * p2 ==> p.
  unfold hprop_imp, hprop_unpack, hprop_sep; firstorder.
  generalize (pack_injective H1); intro; subst; firstorder.
Qed.

Theorem himp_unpack_conc : forall T x (y:[T]) p1 p2 p,
  y = [x]%inhabited
  -> p ==> p1 x * p2
  -> p ==> hprop_unpack y p1 * p2.
  unfold hprop_imp, hprop_unpack, hprop_sep; subst; firstorder.
  generalize (H0 _ H1).
  firstorder.
Qed.

Theorem himp_unpack_conc_meta : forall T x (y:[T]) p1 p2 p,
  p ==> p1 x * p2
  -> y = [x]%inhabited
  -> p ==> hprop_unpack y p1 * p2.
  unfold hprop_imp, hprop_unpack, hprop_sep; subst; firstorder.
  generalize (H _ H1).
  firstorder.
Qed.

Theorem himp_split : forall p1 p2 q1 q2,
  p1 ==> q1
  -> p2 ==> q2
  -> p1 * p2 ==> q1 * q2.
  unfold hprop_imp, hprop_sep; firstorder.
Qed.

Theorem himp_inj_prem : forall (P : Prop) p q,
  (P -> p ==> q)
  -> [P] * p ==> q.
  unfold hprop_imp, hprop_inj, hprop_sep; firstorder.
  subst.
  autorewrite with Ynot.
  eauto.
Qed.

Theorem himp_inj_prem_keep : forall (P : Prop) p q,
  (P -> [P] * p ==> q)
  -> [P] * p ==> q.
  unfold hprop_imp, hprop_inj, hprop_sep; firstorder.
Qed.

Theorem himp_inj_prem_add : forall (P : Prop) p q,
  P
  -> [P] * p ==> q
  -> p ==> q.
  unfold hprop_imp, hprop_inj, hprop_sep; firstorder.
  apply H0.
  exists empty.
  exists h.
  intuition.
Qed.

Theorem himp_inj_conc : forall (P : Prop) p q,
  P
  -> p ==> q
  -> p ==> [P] * q.
  unfold hprop_imp, hprop_inj, hprop_sep; firstorder.
  exists empty; exists h; intuition.
Qed.

Theorem himp_frame : forall p q1 q2,
  q1 ==> q2
  -> p * q1 ==> p * q2.
  intros.
  apply himp_split; [apply himp_refl | assumption].
Qed.

Theorem himp_frame_cell : forall n (T : Set) (v1 v2 : T) q1 q2 (p:perm),
  v1 = v2
  -> q1 ==> q2
  -> n -[p]-> v1 * q1 ==> n -[p]-> v2 * q2.
  intros; subst.
  apply himp_frame; assumption.
Qed.

Lemma himp_cell_split : forall (q1 q2 : perm) (p : ptr) A (v:A),
  q1 |#| q2 -> p -[ q1 + q2 ]-> v ==> p -[ q1 ]-> v * p -[ q2 ]-> v.
Proof.
  red. intuition. 
  exists (p |--> (Dyn v, q1))%heap.
  exists (p |--> (Dyn v, q2))%heap.
  intuition; try solve [red; intuition].
  red in H0.
  unfold split, singleton, join, disjoint, read in *. intuition.
  destruct (ptr_eq_dec p0 p); intuition.
  ext_eq.
  unfold hvalo_plus, hval_plus in *.
  destruct (ptr_eq_dec x p); simpl; intuition.
  subst.
  rewrite perm_plus_when_compat by auto.
  auto.
Qed.

Lemma himp_cell_join : forall (q1 q2 : perm) (p : ptr) A (v:A),
  q1 |#| q2 -> p -[ q1 ]-> v * p -[ q2 ]-> v ==> p -[ q1 + q2 ]-> v.
Proof.
  red. intuition. 
  red in H0. destruct H0. destruct H0. unfold split in H0. 
  intuition. subst.
  unfold hprop_cell, join, read in *.
  intuition.
  rewrite H2, H1. simpl.
  unfold hval_plus. simpl.
  rewrite perm_plus_when_compat by auto.
  auto.

  rewrite H3, H5 by auto.
  simpl. auto.
Qed.

Lemma himp_trans Q P R : P ==> Q -> Q ==> R -> P ==> R.
Proof. firstorder. Qed.

Lemma himp_apply P T : P ==> T -> forall Q, Q ==> P -> Q ==> T.
Proof. repeat intro; auto. Qed.

Theorem add_fact F P Q R : 
  (P ==> [F] * ??) ->
  (F -> (P * Q ==> R)) ->
  (P * Q ==> R).
Proof.
  repeat intro. apply H0; auto. 
  destruct H1 as [? [? [? [Px ?]]]].
  destruct (H _ Px) as [? [? [? [[? ?] ?]]]]; trivial.
Qed.

Lemma himp_any_ret (P:Prop) : P -> forall h, ([P] * ??)%hprop h.
Proof.
 red. repeat econstructor;  firstorder.
Qed.

Lemma himp_cell_same : forall (T:Set) p (q q' : perm) (v v' : T) P Q,
    (q |#| q' -> v = v' -> p -[q]-> v * p -[q']-> v' * P ==> Q) ->
    p -[q]-> v * p -[q']-> v' * P ==> Q.
Proof.
 intros.
 eapply (@add_fact (q |#| q' /\ v = v')); intuition.
 red. intros. destruct H0 as [? [? ?]]. intuition.
 apply himp_any_ret.
 destruct H1. destruct H0. destruct H3. subst.
 specialize (H1 p).
 rewrite H0, H3 in H1.
 simpl in H1; intuition.
 apply Dyn_inj. auto.
Qed.

Theorem himp_frame_prem : forall p1 p2 q p1',
  p1 ==> p1'
  -> p1' * p2 ==> q
  -> p1 * p2 ==> q.
  unfold hprop_imp, hprop_sep; firstorder.
Qed.

Theorem himp_frame_conc : forall p q1 q2 q1',
  q1' ==> q1
  -> p ==> q1' * q2
  -> p ==> q1 * q2.
  unfold hprop_imp, hprop_sep; firstorder.
Qed.


Theorem unpack : forall T (h : [T]) (P : Prop),
  (forall x, h = [x]%inhabited -> P)
  -> P.
  dependent inversion h; eauto.
Qed.

Theorem himp_unpack_prem_eq : forall (T : Set) h (x : T) p1 p2 p,
  h = [x]%inhabited
  -> p1 x * p2 ==> p
  -> hprop_unpack h p1 * p2 ==> p.
  intros; subst.
  apply himp_unpack_prem; assumption.
Qed.

Theorem himp_unpack_prem_alone : forall (T : Set) h (x : T) p1 p,
  h = [x]%inhabited
  -> p1 x ==> p
  -> hprop_unpack h p1 ==> p.
  intros.
  apply himp_empty_prem'.
  rewrite H.
  apply himp_unpack_prem.
  apply himp_comm_prem.
  apply himp_empty_prem.
  assumption.
Qed.
