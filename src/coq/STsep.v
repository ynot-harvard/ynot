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

Set Implicit Arguments.

Notation "{{{ v }}}" := (STWeaken _ (STStrengthen _ v _) _) (at level 0).

Local Open Scope hprop_scope.

Definition STsep pre T (post : T -> hprop) : Type :=
  ST ((pre *! ??) & total_heap) (fun h v h' =>
    forall h1 h2, h ~> h1 * h2
      -> total_heap h
      -> (h1 <*> h2)%heap
      -> pre h1 
      -> exists h1', h' ~> h1' * h2 
        /\ total_heap h'
        /\ (h1' <*> h2)%heap
        /\ post v h1').

Arguments Scope STsep [hprop_scope type_scope hprop_scope].

Ltac hreduce :=
  repeat match goal with
           | [ |- (hprop_inj _) _ ] => red
           | [ |- (hprop_cell _ _ _) _ ] => red
           | [ |- (hprop_sep _ _) _ ] => red
           | [ |- (hprop_and _ _) _ ] => red
           | [ |- (hprop_sep_valid _ _) _ ] => red
           | [ |- hprop_empty _ ] => red
           | [ |- hprop_any _ ] => red
           | [ |- (hprop_ex _) _ ] => red

           | [ H : (hprop_inj _) _ |- _ ] => red in H
           | [ H : (hprop_cell _ _ _) _ |- _ ] => red in H
           | [ H : (hprop_sep _ _) _ |- _ ] => red in H
           | [ H : (hprop_and _ _) _ |- _ ] => red in H
           | [ H : (hprop_sep_valid _ _) _ |- _ ] => red in H
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
    intros.

    ynot 1;
    generalize (H1 _ _ H2); clear H1;
    ynot 8.

    ynot 1.
    generalize (H1 _ _ H4 H5); clear H1.
    ynot 1.
    generalize (H3 _ _ H14); clear H3.
    ynot 1.
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

  Lemma split_read_total0none h h1 h2 d p : 
    h ~> h1 * h2 
    -> (total_heap h 
    -> h1 <*> h2
    -> h1 # p = Some (d, 0)
    -> h2 # p = None)%heap.
  Proof.
    intros. generalize (H0 p).
    generalize (split_read1 p H H2). generalize (H1 p).
    intros. 
    rewrite H2 in H3. unfold read in *. simpl in *.
    rewrite H4 in H5. simpl in *.
    unfold add_qopl in *. destruct (h2 p); trivial.
    rewrite Qcplus_0_l in H5.
    rewrite H5 in H3. intuition.
  Qed.

  Lemma split_read_total0 h h1 h2 d p : 
    h ~> h1 * h2 
    -> (total_heap h 
    -> h1 # p = Some (d, 0)
    -> h # p = Some (d, 0))%heap.
  Proof.
    intros.
    generalize (split_read1 p H H1). unfold read. simpl. intro.
    generalize (H0 p). rewrite H2. simpl. congruence.
  Qed.

  Hint Resolve split_read_total0 : Ynot.
    
  Hint Resolve total_heap_new total_heap_free : Ynot.

  Lemma free_none_eq h p : (h # p = None -> h ### p = h)%heap.
  Proof.
    unfold read, free, heap. intros. ext_eq.
    destruct (ptr_eq_dec x p); congruence.
  Qed.

  Hint Resolve free_none_eq : Ynot.

  (* automate more of this stuff *)
  Lemma split_free_total0 h h1 h2 d p :
    h ~> h1 * h2
    -> ((total_heap h)
    -> h1 <*> h2
    -> (h1 # p) = Some (d, 0)
    -> (h2 ### p) = h2)%heap.
    Proof.
      unfold free, heap.
      intros. ext_eq.
      destruct (ptr_eq_dec x p); trivial.
      subst.
      generalize (split_read_total0none p H H0 H1 H2).
      ynot 1.
    Qed.

    Lemma valid_join_new h A (v:A) p q : ((h # p) = None ->  (p |--> (Dyn v, q)) <*> h)%heap.
    Proof.
     unfold heap, singleton, join_valid, read. simpl. intros. 
     destruct (ptr_eq_dec p0 p); trivial. subst. rewrite H. trivial.
    Qed.

    Hint Resolve valid_join_new : Ynot.

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
    eexists. intuition. 
    generalize (split_free H1 H H6). intro.
    ynot 2. rewrite H7.
    rewrite (split_free_total0 p H1); ynot 1.
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

    destruct H2. intuition. subst.
    ynot 2.
    rewrite (split2_read p H0 H3 H4). simpl. 
    eauto.


    exists h1. intuition.
    replace v with x; trivial.
    destruct H1. intuition. destruct H9.
    destruct H1. intuition.
    destruct H1.
    generalize (split2_read p H0 H9 H1).
    rewrite H2. simpl. intro.

    generalize (Dynq_inj_Somed H12); auto. 
  Qed.

  Lemma join_valid_update h1 h2 p d d' :
    h1 <*> h2 
    -> (h1 # p = Some (d, 0)
    -> (h1 ## p <- (d', 0)) <*> h2)%heap.
  Proof.
    unfold join_valid, write, read. intros.
    generalize (H p). generalize (H p0). rewrite H0. unfold read. 
    destruct (ptr_eq_dec p0 p); subst; trivial.
  Qed.

  Hint Resolve split_read_total0none : Ynot.
  Hint Resolve join_valid_update : Ynot.

  Definition SepWrite (T T' : Set) (p : ptr) (v : T')
    : STsep (Exists v' :@ T, p -0-> v')%hprop (fun _ : unit => p -0-> v)%hprop.
    t.
    refine {{{STWrite T p v}}}; ynot 5.

    exists (h1 ## p <- (Dyn v,0))%heap; intuition.
    ynot 3.
    ynot 2.
    ynot 1.
    unfold write, read in H6 |- *.
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

(*
  Lemma join_valid_splice h x x0 x1 x2 :
    total_heap h
    -> (h ~> x * x0)
    -> (x <*> x0)
    -> (x ~> x1 * x2)
    -> x2 <*> (x0 * x1).
  Proof.
    intros.
    assert (h ~> x2 * (x0 * x1)).
    eauto with Ynot.
    
    intro.
    generalize (H p). clear H.  intro H.
    generalize (H1 p). clear H1. intro H1.

    destruct H3. destruct H2. subst. unfold join, read in *.
    destruct (x2 p); destruct (x0 p); destruct (x1 p); simpl in *.
    intuition.
    rewrite H5 in *.
    rewrite Qcplus_0_l in H4.

*)

  Definition SepFrame pre T (post : T -> hprop) (st : STsep pre post) (P : hprop)
    : STsep (P * pre) (fun v => P * post v)%hprop.
    t.
    refine {{{st}}}; ynot 7. 
    assert (h ~> x2 * (x0 * x1)).
    eauto with Ynot.

    (* arg! this is more annoying *)
    eexists. eexists. split.
    2: repeat split.
    3: eauto. eauto.
    

    
    
    destruct H3. subst.
    destruct H0. subst.
    split_prover'.
    unfold join, read in *.

    destruct (x2 p); trivial.
    destruct (x0 p); destruct (x1 p); simpl in *.
    intuition. destruct h; destruct h0; destruct h1; simpl in *. subst.
    
    rewrite Qcplus_0_r in *.
    simpl in *.
    destruct
    
    clear H4 H6 pre st post T P.
    destruct H3. subst. clear H5.
    destruct H0. subst.
    (* HERE *)
    intro.
    split_prover'.
    unfold read, join in *.
    destruct (x0 p); destruct (x1 p); destruct (x2 p); simpl in *; trivial.
    intuition; trivial.
    destruct h0; destruct h1; destruct h; simpl in *; subst; trivial.
    rewrite Qcplus_0_r in *. subst.

    
    generalize (H p); clear H. intro H.
    generalize (H1 p); clear H1. intro H1.
    generalize (H2 p); clear H2. intro H2.
    unfold join, read in *.

    intuition.

    
    

    Focus 2.
    assert (h ~> x4 * (x1 * x3)).
    eauto with Ynot.

    generalize (H0 _ _ H7); clear H0; ynot 0.
    exists (x5 * x)%heap; ynot 3.
    
    x0.

    exists x.
    exists x5.
    intuition.
    eauto with Ynot.



    exists x2. exists ((x0 * x1)%heap). intuition.
    
    (* lemma me *)


    -> h ~> x2 * (x0 * x1)
    -> 
    -> h


    generalize (H0 _ _ H6); clear H0; ynot 0.
    exists (x5 * x)%heap; ynot 3.

    exists x.
    exists x5.
    intuition.
    eauto with Ynot.


    assert (h ~> x0 * (h2 * x)).
    eauto with Ynot.

    generalize (H0 _ _ H6); clear H0; ynot 0.
    exists (x5 * x)%heap; ynot 3.

    exists x.
    exists x5.
    intuition.
    eauto with Ynot.
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
Infix "!!" := SepRead (no associativity, at level 75) : stsep_scope.
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
Notation "! r" := (SepRead r _) (no associativity, at level 75) : stsepi_scope.
Notation "r : t ::= v" := (SepWrite t r v <@> _) (no associativity, at level 75) : stsepi_scope.
Notation "r ::= v" := (SepWrite _ r v <@> _) (no associativity, at level 75) : stsepi_scope.
Notation "'Assert' P" := (SepAssert P) (at level 75) : stsepi_scope.
Notation "'Fix'" := SepFix : stsepi_scope.
Notation "'Fix2'" := SepFix2 : stsepi_scope.
Notation "'Fix3'" := SepFix3 : stsepi_scope.
Notation "'Fix4'" := SepFix4 : stsepi_scope.

Delimit Scope stsepi_scope with stsepi.
