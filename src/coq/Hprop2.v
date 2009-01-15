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

Require Import Arith List Omega.

Require Import Ynot.Axioms.
Require Import Ynot.Util.
Require Import Ynot.Heap.
Require Import Ynot.Hprop.
Require Import Ynot.Separation.

Set Implicit Arguments.

(* I used these to explicitly transform an himp goal -- there's probably a better way *)
Lemma hprop_mp(P1 P2 P3:hprop) : (P1 ==> P2) -> (P2 ==> P3) -> (P1 ==> P3).
Proof. intros. red. intros. pose (H h H1). apply (H0 h p). Qed.

Lemma hprop_mp_conc(P1 P2 P3:hprop) : (P2 ==> P3) -> (P1 ==> P2) -> (P1 ==> P3).
Proof. intros. red. intros. pose (H0 h H1). apply (H h p). Qed.

(* split separating conjunction into two pieces *)
Lemma split_sep(P:nat->hprop)(len i:nat)(H:i <= len)(start:nat) :
  ((iter_sep P start len) ==> (iter_sep P start i) * (iter_sep P (start + i) (len - i))).
Proof.
  induction len ; intros. 
  assert (i = 0) ; [ omega | subst ; sep fail auto].
  induction i ; simpl ; intros ; assert (start + 0 = start) ; try omega. 
  rewrite H0 ; sep fail auto.
  assert (start + S i = ((S start) + i)) ; try omega ; 
  rewrite H1 ; clear H0; sep fail ltac:(try subst; auto).
 replace (S (start + i)) with (S start + i) by omega.
  sep fail auto.
Qed.

(* join two adjacent separating conjunctions *)
Lemma join_sep(P:nat->hprop)(len i:nat)(H:i <= len)(start:nat) : 
  (iter_sep P start i) * (iter_sep P (start + i) (len - i)) ==> iter_sep P start len.
Proof.
  induction len ; intros. 
  assert (i = 0) ; [omega | sep fail auto].
  induction i ; simpl ; intros ; assert (start + 0 = start) ; try omega. 
  rewrite H0 ; sep fail auto.
  assert (start + S i = ((S start) + i)) ; try omega ; rewrite H1 ; sep fail auto.
(*  replace (S (start + i)) with (S start + i) by omega.
  sep fail auto. *)
Qed.

(* split out a particular index, leaving the front and rear *)
Lemma split_index_sep(P:nat->hprop)(start len i:nat) : 
  i < len -> 
  (iter_sep P start len) ==> 
  (iter_sep P start i) * (P (start + i)) * (iter_sep P (1 + start + i) (len - i - 1)).
Proof.
  intros. assert (i <= len). omega. assert (1 <= len - i). omega.
  eapply hprop_mp. apply (split_sep P H0 start). sep fail auto. 
  eapply hprop_mp. apply (split_sep P H1 (start + i)).
  assert (S (start + i) = start + i + 1). omega. rewrite H2. sep fail auto. 
Qed.

(* opposite of above *)
Lemma join_index_sep(P:nat->hprop)(start len i:nat) : 
  i < len -> 
  (iter_sep P start i) * (P (start + i)) * (iter_sep P (1 + start + i) (len - i - 1)) ==>
  (iter_sep P start len).
Proof.
  intros. eapply hprop_mp_conc. assert (i <= len). omega. 
  apply (join_sep P H0 start). sep fail auto. assert (1 <= len - i). omega.
  eapply hprop_mp_conc. apply (join_sep P H0 (start + i)).
  assert (S (start + i) = start + i + 1). omega. rewrite H1. sep fail auto. 
Qed.

(* simplify proof for iterating separating conjunction implication *)
Lemma iter_imp(P1 P2:nat->hprop)(len start:nat) : 
  (forall i, i >= start -> i < len + start -> P1 i ==> P2 i) -> 
  iter_sep P1 start len ==> iter_sep P2 start len.
Proof.
  induction len. sep fail auto. sep fail auto. eapply himp_split. apply H. auto. omega.
  apply (IHlen (S start)). intros. apply H. omega. omega.
Qed.

Lemma sp_index_hyp(P:nat->hprop)(Q R:hprop)(start len i:nat) : 
  i < len -> 
  iter_sep P start i * P (start + i) * iter_sep P (1 + start + i) (len - i - 1) * Q ==> R 
  ->
  iter_sep P start len * Q ==> R.
Proof.
  intros. eapply hprop_mp. eapply himp_split. apply (split_index_sep P start H). 
  sep fail auto. auto. 
Qed.

Lemma sp_index_conc(P:nat->hprop)(Q R:hprop)(start len i:nat) : 
  i < len -> 
  R ==> iter_sep P start i * P (start + i) * iter_sep P (1 + start + i) (len - i - 1) * Q -> 
  R ==> iter_sep P start len * Q.
Proof.
  intros. eapply hprop_mp_conc. eapply himp_split. apply (join_index_sep P start H).
  sep fail auto. auto.
Qed.

(* extra tactics *)

Ltac split_index' := idtac; 
  match goal with
    | [ |- iter_sep ?P ?s ?len * ?Q ==> ?R ] => 
      eapply (sp_index_hyp P)
    | [ |- ?R ==> iter_sep ?P ?s ?len * ?Q] => 
      eapply (sp_index_conc P) 
  end.

Ltac split_index := search_prem split_index' || search_conc split_index'.