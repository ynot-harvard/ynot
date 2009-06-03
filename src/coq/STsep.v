(* Copyright (c) 2008, Harvard University
 * All rights reserved.
 *
 * Authors: Adam Chlipala, Gregory Malecha, Avi Shinnar
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

Require Import List.

Require Import Ynot.Axioms.
Require Import Ynot.Util.
Require Import Ynot.Heap.
Require Import Ynot.Hprop.
Require Import Ynot.ST.
Require Import Qcanon.
Require Import PermModel.

Set Implicit Arguments.

Notation "{{{ v }}}" := (STWeaken _ (STStrengthen _ v _) _) (at level 0).

Local Open Scope hprop_scope.

Definition STsep pre T (post : T -> hprop) : Type :=
  ST (pre * ??) (fun h v h' =>
    forall h1 h2, h ~> h1 * h2
      -> pre h1
      -> exists h1', h' ~> h1' * h2 
        /\ post v h1').

Arguments Scope STsep [hprop_scope type_scope hprop_scope].

Ltac hreduce :=
  repeat match goal with
           | [ |- (hprop_inj _) _ ] => red
           | [ |- (hprop_cell _ _ _) _ ] => red
           | [ |- (hprop_sep _ _) _ ] => red
           | [ |- (hprop_and _ _) _ ] => red
           | [ |- hprop_empty _ ] => red
           | [ |- hprop_any _ ] => red
           | [ |- (hprop_ex _) _ ] => red

           | [ H : (hprop_inj _) _ |- _ ] => red in H
           | [ H : (hprop_cell _ _ _) _ |- _ ] => red in H
           | [ H : (hprop_sep _ _) _ |- _ ] => red in H
           | [ H : (hprop_and _ _) _ |- _ ] => red in H
           | [ H : hprop_empty _ |- _ ] => red in H
           | [ H : hprop_any _ |- _ ] => clear H
           | [ H : (hprop_ex _) _ |- _ ] => destruct H

           | [ H : ex _ |- _ ] => destruct H

           | [ H : _ ~> empty * _ |- _ ] => generalize (split_id_invert H); clear H
         end.

Hint Extern 1 ((hprop_inj _) _) => hreduce : Ynot.
Hint Extern 1 ((hprop_cell _ _ _) _) => hreduce : Ynot.
Hint Extern 1 ((hprop_sep _ _) _) => hreduce : Ynot.
Hint Extern 1 (hprop_empty _) => hreduce : Ynot.
Hint Extern 1 (hprop_any _) => hreduce : Ynot.

Tactic Notation "ynot" integer(n) := repeat progress (intuition; subst; hreduce); eauto n with Ynot.

Section Sep.
  Ltac t := intros; red.

  Definition SepReturn T (v : T) : STsep __ (fun v' => [v' = v])%hprop.
    t.
    refine {{{STReturn v}}}; ynot 8.
  Qed.

  Local Open Scope hprop_scope.

  Definition SepBind pre1 T1 (post1 : T1 -> hprop)
    pre2 T2 (post2 : T2 -> hprop)
    (st1 : STsep pre1 post1)
    (_ : forall v, post1 v ==> pre2 v)
    (st2 : forall v : T1, STsep (pre2 v) post2)
    : STsep pre1 post2.
    unfold hprop_imp; t.

    refine (STBind _ _ _ _ st1 st2 _ _ _).

    tauto.

    ynot 1.
    generalize (H1 _ _ H2); clear H1.
    ynot 7.

(*    ynot 1.
    generalize (H1 _ _ H2 H3 H0); clear H1.*)
    ynot 1. 
    generalize (H1 _ _ H4 H5); clear H1.
    ynot 1.
    eapply H3; eauto.
  Qed.

  Definition SepSeq pre1 (post1 : unit -> hprop)
    pre2 T2 (post2 : T2 -> hprop)
    (st1 : STsep pre1 post1)
    (_ : forall v, post1 v ==> pre2)
    (st2 : STsep pre2 post2)
    : STsep pre1 post2.
    intros; refine (SepBind _ st1 _ (fun _ : unit => st2)); trivial.
  Qed.

  Definition SepContra T (post : T -> hprop) : STsep [False] post.
    t.
    refine {{{STContra (fun _ => post)}}}; ynot 1.
  Qed.

  Definition SepFix : forall dom (ran : dom -> Type)
    (pre : dom -> hprop) (post : forall v : dom, ran v -> hprop)
    (F : (forall v : dom, STsep (pre v) (post v))
      -> (forall v : dom, STsep (pre v) (post v)))
    (v : dom), STsep (pre v) (post v).
    t.
    exact (STFix _ _ _ F v).
  Qed.

  Theorem split_readSS_compat : forall h h1 h2 p d1 d2 q1 q2,
    (h ~> h1 * h2
    -> h1 # p = Some (d1, q1)
    -> h2 # p = Some (d2, q2)
    -> compatible q1 q2)%heap.
  Proof.
    intros.
    destruct H; intuition.
    generalize (H p). rewrite H0. rewrite H1. simpl in *.
    intuition.
  Qed.

  Theorem compatible_top (p:perm) : compatible p top -> False.
  Proof.
    unfold compatible. intro. rewrite (compatibleb_top p). discriminate.
  Qed.

  Theorem split_readS0N : forall h h1 h2 p d,
    (h ~> h1 * h2
    -> h1 # p = Some (d, 0)
    -> h2 # p = None)%heap.
  Proof.
    intros.
    remember (h2 # p)%heap as h2p. destruct h2p; trivial.
    destruct h0.
    generalize (split_readSS_compat p H H0 (sym_eq Heqh2p)).
    intro. elim (compatible_top (compatible_sym H1)).
  Qed.

  Lemma split_read_S0 h h1 h2 d p : 
    h ~> h1 * h2 
    -> (h1 # p = Some (d, 0)
    -> h # p = Some (d, 0))%heap.
  Proof.
    intros.
    generalize (split_read1 H H0).
    generalize (split_readS0N p H H0). intros. 
    rewrite H1 in H2. simpl in *. auto.
  Qed.

  Hint Resolve split_read_S0 : Ynot.
    
  Lemma free_none_eq h p : (h # p = None -> h ### p = h)%heap.
  Proof.
    unfold read, free, heap. intros. ext_eq.
    destruct (ptr_eq_dec x p); congruence.
  Qed.

  Hint Resolve free_none_eq : Ynot.

  Definition SepNew (T : Set) (v : T)
    : STsep __ (fun p => p -0-> v)%hprop.
    t.
    refine {{{STNew v}}}; ynot 5.
    eexists. intuition.
  Qed.

  Definition SepFree T p
    : STsep (Exists v :@ T, p -0-> v)%hprop (fun _ : unit => __)%hprop.
    t.
    refine {{{STFree p}}}; ynot 5.
        generalize (split_free H1 H H4).
        rewrite (@free_none_eq h2). intros.
        eexists; intuition; intuition.
        eapply split_readS0N; eauto.
  Qed.

  Theorem Dynq_inj_Someq : forall (T : Set) (x y : T) (q1 q2 : Qc),
    Some (Dyn x, q1) = Some (Dyn y, q2)
    -> q1 = q2.
    intros. inversion H. trivial.
  Qed.

  Lemma Dynq_inj_Somed' : forall (d1 d2 : dynamic) (q : Qc),
    Some (d1, q) = Some (d2, q)
    -> d1 = d2.
    congruence.
  Qed.
  
  Theorem Dynq_inj_Somed : forall (T : Set) (x y : T) (q1 q2 : Qc),
    Some (Dyn x, q1) = Some (Dyn y, q2)
    -> x = y.
    intros. inversion H. subst.
    apply Dyn_inj.
    apply Dynq_inj_Somed' with (q:=q2).
    trivial.
  Qed.

  (* this should be automated *)
  Definition SepRead (T : Set) (p : ptr) (P : T -> hprop) (q:[Qc])
    : STsep (Exists v :@ T, (q ~~ p -[q]-> v * P v))%hprop (fun v => (q ~~ p -[q]-> v * P v))%hprop.
    t.
    refine {{{STRead T p}}}; ynot 5.

    destruct H.
    ynot 2.
    rewrite (split2_read H0 H1 H2). simpl. 
    eauto.


    exists h1. intuition.
    replace v with x; trivial.
    destruct H; destruct H1. ynot 2. 
    generalize (split2_read H0 H5 H7).
    rewrite H2. simpl. intro.
    symmetry. eapply Dynq_inj_Somed. eauto.
  Qed.

  Definition SepWrite (T T' : Set) (p : ptr) (v : T')
    : STsep (Exists v' :@ T, p -0-> v')%hprop (fun _ : unit => p -0-> v)%hprop.
    t.
    refine {{{STWrite T p v}}}; ynot 5.

    exists (h1 ## p <- (Dyn v,0))%heap; intuition.
    eapply split_writeSN; eauto.
    eapply split_readS0N; eauto.

    ynot 1.
    unfold write, read in *.
    destruct (ptr_eq_dec p' p); intuition.
  Qed.

  Definition SepStrengthen pre T (post : T -> hprop) (pre' : hpre)
    (st : STsep pre post)
    : pre' ==> pre
    -> STsep pre' post.
    unfold hprop_imp; t.
    refine {{{st}}}; ynot 8.
  Qed.

  Definition SepWeaken pre T (post post' : T -> hprop)
    (st : STsep pre post)
    : (forall v, post v ==> post' v)
    -> STsep pre post'.
    unfold hprop_imp; t.
    refine {{{st}}}; ynot 1.

    generalize (H1 _ _ H2); clear H1; ynot 6.
  Qed.

  Lemma split_refl x1 x2 :
       (x1 <#> x2)%heap 
    -> (x1 * x2) ~> x1 * x2.
  Proof.
    intros. split; ynot 0.
  Qed.

  Lemma split_comm' x1 x2 :
       (x1 <#> x2)%heap 
    -> (x1 * x2) ~> x2 * x1.
  Proof.
    intros. split; ynot 0.
  Qed.

Lemma split_self_other h h1 h2 h' x x0 x5 :
       (h ~> h1 * h2
    -> h1 ~> x * x0
    -> h' ~> x5 * (h2 * x)
    -> (x5 * x) ~> x5 * x)%heap.
Proof.
    intros.
    apply split_refl.
    unfold split in *; intuition.
    subst.
    unfold disjoint, read in *.
    split_prover'.
(*    assert ((x * x0 * h2) p = (x0 * (h2 * x)) p)%heap by congruence. *)
(*    clear H4. *)
    destruct (x5 p); trivial.
    unfold join in *.
    destruct (x p); trivial.
    destruct (h2 p); destruct (x0 p); simpl in *; try solve [intuition].
    unfold hvalo_plus, hval_plus in *. destruct H.
    rewrite perm_plus_when_compat in H2 by auto; simpl in *.
    destruct H2.
    generalize (compatible_sym (compatible_trans H1 H3)). intros.
    rewrite perm_plus_when_compat in H0 by auto; simpl in *.
    destruct H.  
    intuition.
      congruence.
      apply compatible_sym.
      eapply compatible_trans; apply compatible_sym; eauto.
      rewrite Qcplus_comm. auto.

    destruct H2. unfold hval_plus in *.
    repeat rewrite perm_plus_when_compat in H0 by ynot 1; simpl in *.
    intuition.
      congruence.
      apply compatible_sym.
      eapply compatible_trans; eauto.
      rewrite Qcplus_comm. ynot 0.
  Qed.

  Definition SepFrame pre T (post : T -> hprop) (st : STsep pre post) (P : hprop)
    : STsep (P * pre) (fun v => P * post v)%hprop.
    t.
    refine {{{st}}}; ynot 7.
    assert (h ~> x0 * (h2 * x)).
    eauto with Ynot.

    generalize (H0 _ _ H6); clear H0; ynot 0.
    exists (x5 * x)%heap; ynot 3.

    exists x.
    exists x5.
    intuition.
    apply split_comm.
    apply (split_self_other H1 H H9).
  Qed.


  Definition SepAssert (P : hprop)
    : STsep P (fun _ : unit => P).
    t.
    refine {{{STReturn tt}}}; intuition; subst; eauto.
  Qed.

  Implicit Arguments SepStrengthen [pre T post].
  Notation "{{ st }}" := (SepWeaken _ (SepStrengthen _ st _) _).

  (* We can define easily derive Fix on multiple parameters, using currying *)
  Notation Local "'curry' f" := (fun a => f (projT1 a) (projT2 a)) (no associativity, at level 75).

  Definition SepFix2 : forall (dom1 : Type) (dom2: forall (d1:dom1), Type) (ran : forall (d1 : dom1) (d2:dom2 d1), Type)
    (pre : forall (d1: dom1) (d2:dom2 d1), hprop) (post : forall v1 v2, ran v1 v2 -> hprop)
    (F : (forall v1 v2, STsep (pre v1 v2) (post v1 v2))
      -> (forall v1 v2, STsep (pre v1 v2) (post v1 v2))) v1 v2,
    STsep (pre v1 v2) (post v1 v2).
    Proof. intros;
    refine (@SepFix (sigT dom2)%type 
      (curry ran) (curry pre) (curry post)
      (fun self x => F (fun a b => self (@existT _ _ a b)) (projT1 x) (projT2 x)) (@existT _ _ v1 v2)).
    Qed.

  Definition SepFix3 : forall (dom1 : Type) (dom2: forall (d1:dom1), Type) 
    (dom3: forall (d1:dom1) (d2:dom2 d1), Type)
    (ran : forall (d1 : dom1) (d2:dom2 d1) (d3:dom3 d1 d2), Type)
    (pre : forall (d1: dom1) (d2:dom2 d1) (d3:dom3 d1 d2), hprop) 
    (post : forall v1 v2 v3, ran v1 v2 v3 -> hprop)
    (F : (forall v1 v2 v3, STsep (pre v1 v2 v3) (post v1 v2 v3))
      -> (forall v1 v2 v3, STsep (pre v1 v2 v3) (post v1 v2 v3)))
    v1 v2 v3, STsep (pre v1 v2 v3) (post v1 v2 v3).
    Proof. intros;
    refine (@SepFix2 (sigT dom2)%type (curry dom3)
      (curry ran) (curry pre) (curry post) 
      (fun self x => F (fun a b c => self (@existT _ _ a b) c) (projT1 x) (projT2 x)) (@existT _ _ v1 v2) v3).
    Qed.

  Definition SepFix4 : forall (dom1 : Type) (dom2: forall (d1:dom1), Type) 
    (dom3: forall (d1:dom1) (d2:dom2 d1), Type) (dom4: forall (d1:dom1) (d2:dom2 d1) (d3:dom3 d1 d2), Type)
    (ran : forall (d1 : dom1) (d2:dom2 d1) (d3:dom3 d1 d2) (d4:dom4 d1 d2 d3), Type)
    (pre : forall (d1: dom1) (d2:dom2 d1) (d3:dom3 d1 d2) (d4:dom4 d1 d2 d3), hprop) 
    (post : forall v1 v2 v3 v4, ran v1 v2 v3 v4 -> hprop)
    (F : (forall v1 v2 v3 v4, STsep (pre v1 v2 v3 v4) (post v1 v2 v3 v4))
      -> (forall v1 v2 v3 v4, STsep (pre v1 v2 v3 v4) (post v1 v2 v3 v4)))
    v1 v2 v3 v4, STsep (pre v1 v2 v3 v4) (post v1 v2 v3 v4).
    Proof. intros;
    refine (@SepFix3 (sigT dom2)%type (curry dom3) (curry dom4)
      (curry ran) (curry pre) (curry post) 
      (fun self x =>  F (fun a b c d => self (@existT _ _ a b) c d) (projT1 x) (projT2 x))
      (@existT _ _ v1 v2) v3 v4).
    Qed.

End Sep.

Implicit Arguments SepFree [T].
Implicit Arguments SepStrengthen [pre T post].
Implicit Arguments SepFix [dom ran].
Implicit Arguments SepFix2 [dom1 dom2 ran].
Implicit Arguments SepFix3 [dom1 dom2 dom3 ran].
Implicit Arguments SepFix4 [dom1 dom2 dom3 dom4 ran].

Notation "{{ st }}" := (SepWeaken _ (SepStrengthen _ st _) _).

Notation "p <@ c" := (SepStrengthen p c _) (left associativity, at level 81) : stsep_scope.
Notation "c @> p" := (SepWeaken p c _) (left associativity, at level 81) : stsep_scope.
Infix "<@>" := SepFrame (left associativity, at level 81) : stsep_scope.

Notation "'Return' x" := (SepReturn x) (at level 75) : stsep_scope.
Notation "x <- c1 ; c2" := (SepBind _ (SepStrengthen _ c1 _) _ (fun x => c2))
  (right associativity, at level 84, c1 at next level) : stsep_scope.
Notation "c1 ;; c2" := (SepSeq (SepStrengthen _ c1 _) _ c2)
  (right associativity, at level 84) : stsep_scope.
Notation "!!!" := (SepContra _) : stsep_scope.
Notation "'New' x" := (SepNew x) (at level 75) : stsep_scope.
Notation "'FreeT' x :@ T" := (SepFree (T := T) x) (at level 75) : stsep_scope.
Notation "p !![ q ] P" := (SepRead p P q) (no associativity, at level 75) : stsep_scope.
Notation "r ::= v" := (SepWrite _ r v) (no associativity, at level 75) : stsep_scope.

Bind Scope stsep_scope with STsep.
Delimit Scope stsep_scope with stsep.


(** Alternate notations for more spec inference *)

Notation "p <@ c" := (SepStrengthen p c _) (left associativity, at level 81) : stsepi_scope.
Notation "c @> p" := (SepWeaken p c _) (left associativity, at level 81) : stsepi_scope.
Infix "<@>" := SepFrame (left associativity, at level 81) : stsepi_scope.

Open Local Scope stsepi_scope.

Notation "'Return' x" := (SepReturn x <@> _) (at level 75) : stsepi_scope.
Notation "x <- c1 ; c2" := (SepBind _ (SepStrengthen _ c1 _) _ (fun x => c2))
  (right associativity, at level 84, c1 at next level) : stsepi_scope.
Notation "c1 ;; c2" := (SepSeq (SepStrengthen _ c1 _) _ c2)
  (right associativity, at level 84) : stsepi_scope.
Notation "!!!" := (SepContra _) : stsepi_scope.
Notation "'New' x" := (SepNew x <@> _) (at level 75) : stsepi_scope.
Notation "'Free' x" := (SepFree x <@> _) (at level 75) : stsepi_scope.
Notation "![ q ] r" := (SepRead r _ q) (no associativity, at level 75) : stsepi_scope.
Notation "! r" := (SepRead r _ _) (no associativity, at level 75) : stsepi_scope.
Notation "r : t ::= v" := (SepWrite t r v <@> _) (no associativity, at level 75) : stsepi_scope.
Notation "r ::= v" := (SepWrite _ r v <@> _) (no associativity, at level 75) : stsepi_scope.
Notation "'Assert' P" := (SepAssert P) (at level 75) : stsepi_scope.
Notation "'Fix'" := SepFix : stsepi_scope.
Notation "'Fix2'" := SepFix2 : stsepi_scope.
Notation "'Fix3'" := SepFix3 : stsepi_scope.
Notation "'Fix4'" := SepFix4 : stsepi_scope.

Delimit Scope stsepi_scope with stsepi.
