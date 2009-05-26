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

Require Import Arith QArith Bool.
Require Export Qcanon.
Opaque Qcplus.
Require Import Ynot.Axioms.

Set Implicit Arguments.

(* first we define the underlying set of permissions and its partial additive function *)
Definition perm_base := Qc.
Definition top_base : perm_base := (0%Qc).

(* notations and basic lemmas *)
Definition Qc0 := (Q2Qc (Qmake Z0 xH)).
Notation "00" := Qc0.

Lemma Qcle_bool_iff (x y : Qc) : Qle_bool x y = true <-> (x <= y)%Qc.
Proof. unfold Qcle. intros. apply Qle_bool_iff. Qed.

Definition Qlt_bool (q1 q2 : perm_base) := (Qle_bool q1 q2) && negb (Qeq_bool q1 q2).

Definition compatibleb (q1 q2 : perm_base) : bool :=
let q1pos := Qle_bool 00 q1 in
  let q2pos := Qle_bool 00 q2 in
    negb (
         (q1pos && q2pos)
      || ((q1pos || q2pos) && (negb (Qle_bool 00 ((q1 + q2)%Qc)))))%Qc.

Definition compatible (q1 q2 : perm_base) := compatibleb q1 q2 = true.

Definition compatible_dec (q1 q2 : perm_base) : {compatible q1 q2} + {~ compatible q1 q2}.
Proof. unfold compatible. decide equality. Qed.

(* Infix "|#|" := compatible (at level 60, no associativity). *)

Theorem compatibleb_comm (q1 q2 : perm_base) : compatibleb q1 q2 = compatibleb q2 q1.
Proof.  intros. unfold compatibleb.
       rewrite Qcplus_comm. 
       rewrite andb_comm. f_equal. f_equal. f_equal.
       rewrite orb_comm. f_equal.
Qed.

Theorem perm_base_plus_top (p : perm_base) : compatibleb p top_base = false.
Proof.
  unfold compatibleb, top_base. intros. 
  rewrite andb_true_r. rewrite orb_true_r. simpl.
  rewrite <- (negb_involutive false). f_equal. simpl.
  rewrite Qcplus_0_r.
  destruct (Qle_bool 00 p); intuition.
Qed.

Lemma compatible_sym (q1 q2 : perm_base) : compatible q1 q2 -> compatible q2 q1.
Proof. unfold compatible. intros. rewrite compatibleb_comm. trivial. Qed.

Definition perm_base_plus (q1 q2 : perm_base) : option perm_base := 
  if compatibleb q1 q2 then Some (q1 + q2) else None.

Infix "+pb" := perm_base_plus (at level 60, no associativity).

Theorem perm_base_plus_comm (p1 p2 : perm_base) : p1 +pb p2 = p2 +pb p1.
Proof.
  unfold perm_base_plus. intros. rewrite Qcplus_comm. rewrite compatibleb_comm. trivial.
Qed.


Theorem Some_inj : forall T (x y : T),
  Some x = Some y
  -> x = y.
  intros; congruence.
Qed.

Theorem perm_base_plus_cancel (p p1 p2 : perm_base) : compatible p p1 -> (p +pb p1) = (p +pb p2) -> p1 = p2.
Proof.
  unfold perm_base_plus, compatible.  intros. 
  rewrite H in H0. destruct (compatibleb p p2); try discriminate.
  generalize (Some_inj H0). intro.
  unfold perm_base in *.
  assert (C: -p + (p + p1) = -p + (p + p2)) by (rewrite H1; trivial).
  replace (-p + (p + p1)) with (p1) in C by ring.
  replace (-p + (p + p2)) with (p2) in C by ring.
  trivial. 
Qed.

(* We now lift this to a set of optional permissions with total + *)
Definition perm := option perm_base.

Definition perm_valid (p:perm) := if p then True else False.

Definition perm_plus (p1 p2 : perm) : perm :=
  match p1 with
    | None => None
    | Some p1' => 
      match p2 with
        | None => None
        | Some p2' => p1' +pb p2'
      end
  end.

Infix "+p" := perm_plus (at level 59, left associativity).

Definition compatiblep (p1 p2 : perm) := perm_valid (p1 +p p2).

Theorem perm_plus_comm (p1 p2 : perm) : p1 +p p2 = p2 +p p1.
Proof.
  destruct p1; destruct p2; simpl; trivial. apply perm_base_plus_comm.
Qed.


Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ => idtac
  end.

Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.

Lemma Qle_bool_plus_pos (p0 p1:Qc) :
  Qle_bool (00) p0 = true
  -> Qle_bool (00) p1 = true
  -> Qle_bool (00) (p0 + p1)%Qc = true.
Proof.
  intros.

  generalize ((proj1 (Qcle_bool_iff 0 p0 )) H); clear H; intro H.
  generalize ((proj1 (Qcle_bool_iff 0 p1 )) H0); clear H0; intro H0.
  generalize (Qcplus_le_compat _ _ _ _ H H0).
  intro G.
  apply (proj2 (Qcle_bool_iff 0 (p0 + p1)%Qc)).
  auto.
Qed.

Lemma negb_inv b1 b2 : negb b1 = negb b2 -> b1 = b2.
Proof. destruct b1; destruct b2; auto. Qed.

Lemma Qle_bool_false (q1 q2 : Qc) : Qle_bool q1 q2 = false -> (q2 < q1).
Proof.
  intros.
  generalize ((proj2 (Qle_bool_iff q1 q2))). rewrite H.
  destruct (Qlt_le_dec q2 q1); intuition; try discriminate.
Qed.

Lemma neg_neg_npos p0 p1 : 
   p0 < 0
-> p1 < 0
-> 0 <= p0 + p1
-> False.
Proof.
  intros.
  generalize (Qclt_le_trans _ _ _ H H1). intro.
  generalize ((proj1 (Qclt_minus_iff _ _)) H2). intro.
  ring_simplify in H3.
  elim (Qclt_not_le _ _ H3). apply Qclt_le_weak; auto.
Qed.

Hint Resolve neg_neg_npos.

Ltac desb := 
  repeat match goal with
           | [H: ?x = ?y |- _] => rewrite <- H in *
           | [|- context [compatibleb ?x ?y]] => 
             let HH := fresh "HH" in
               remember (compatibleb x y) as HH;
                 destruct HH
         end; simpl; trivial.


(* wow, does this need cleanup *)
Theorem perm_plus_ass (p1 p2 p3 : perm) : p1 +p (p2 +p p3) = (p1 +p p2) +p p3.
Proof.

  Ltac btol := repeat match goal with
    | [H: ?x = ?x |- _] => clear H
    | [H: true = _ |- _] => symmetry in H
    | [H: false = _ |- _] => symmetry in H
    | [|- context [Qle_bool ?x ?y]] =>  generalize (Qle_bool_iff x y); intro; destruct (Qle_bool x y)
    | [|- context [Qeq_bool ?x ?y]] =>  generalize (Qeq_bool_iff x y); intro; destruct (Qeq_bool x y)
    | [H: Qle_bool 0 ?y = true |- _] =>  generalize ((proj1 (Qcle_bool_iff 00 _)) H); clear H; intro H
    | [H: Qeq_bool ?x ?y = true |- _] =>  generalize ((proj1 (Qeq_bool_iff x y)) H); clear H; intro H
    | [H: Qle_bool 0 ?y = false |- _] =>  generalize (Qle_bool_false 00 _ H); clear H; intro H
  end; trivial.

  Ltac bool_to_logic := 
    repeat match goal with
    | [H: ?x = ?x |- _ ] => clear H
    | [H: true = _ |- _] => discriminate || symmetry in H
    | [H: false = _ |- _] => discriminate || symmetry in H
    | [H: ?x && ?y = true  |- _] => destruct (andb_true_eq  _ _ (sym_eq H)); clear H; try discriminate
    | [H: ?x || ?y = false |- _] => destruct (orb_false_elim  _ _ H); clear H; try discriminate
    | [H: ?x || ?y = true  |- _] => destruct (orb_true_elim   _ _ H); clear H
    | [H: ?x && ?y = false |- _] => destruct (andb_false_elim _ _ H); clear H
    | [H: negb ?x  = _  |- _] => generalize (f_equal negb H); clear H; intro H;
      rewrite negb_involutive in H; simpl in H
            | [H: ?x && ?y = true |- _] => destruct (andb_true_eq _ _ H); clear H
    | [|- ?x && ?y = true  ] => apply andb_true_intro
    | [|- ?x || ?y = false ] => apply orb_false_intro
    | [|- ?x || ?y = true  ] => apply orb_true_intro
(*    | [|- ?x && ?y = false ] => apply andb_false_intro *)
    | [H: ?x = ?y |- _] => rewrite H in *; simpl in *
    | _ =>   rewrite negb_andb in *; rewrite negb_involutive in *
  end.

  unfold perm_plus, perm_base_plus.
  destruct p1; trivial. 
  destruct p2; trivial.
  
  destruct p3; trivial. 2: desb.
desb;
(*  remember (compatibleb p0 p1) as p0p1; destruct p0p1; 
  remember (compatibleb p p0) as pp0; destruct pp0; trivial.
  rewrite Qcplus_assoc. desb; trivial. *)
  
  (* sub-goal 1:1 *)
  unfold compatibleb in *;
  remember (Qle_bool 0%Qc p) as b; destruct b;
  remember (Qle_bool 0%Qc p0) as b; destruct b;
  remember (Qle_bool 0%Qc p1) as b; destruct b;
(*  remember (Qlt_bool (p + p0) 0%Qc) as b; destruct b; simpl; trivial; *)
  simpl in *; try discriminate; repeat rewrite negb_involutive in *;
  repeat rewrite negb_orb in *;
  repeat progress (repeat match goal with
    [H: _ = _ |- _] => rewrite <- H in *
  end; simpl in *; 
  try rewrite negb_involutive in *; 
  try rewrite Qcplus_assoc in *;
  try rewrite andb_false_l in *; try rewrite andb_false_r in *;
  try rewrite andb_true_l in *;  try rewrite andb_true_r in *;
  try rewrite orb_false_l in *;  try rewrite orb_false_r in *;
  try rewrite orb_true_l in *;   try rewrite orb_true_r in *); 
  try discriminate; bool_to_logic; btol;
    try (elimtype False; eauto).

  (* remaining sub-goal 1/2 *)
  generalize (Qclt_le_trans _ _ _ HeqHH HeqHH1). intro.
  generalize ((proj1 (Qclt_minus_iff _ _)) H). intro.
  ring_simplify in H0.
  elim (Qclt_not_le _ _ H0). apply Qclt_le_weak; auto.

  generalize (Qclt_le_trans _ _ _ HeqHH H0). intro.
  generalize ((proj1 (Qclt_minus_iff _ _)) H1). intro.
  ring_simplify in H2.
  elim (Qclt_not_le _ _ H2). apply Qclt_le_weak; auto.
Qed.

Definition compatiblep_alt (p1 p2 : perm) :=
  match p1 with
    | None => False
    | Some p1' => 
      match p2 with
        | None => False
        | Some p2' => compatible p1' p2'
      end
  end.

Lemma compatiblep_to_alt (p1 p2 : perm) : compatiblep p1 p2 -> compatiblep_alt p1 p2.
Proof.
  unfold compatiblep, compatiblep_alt, perm_valid, perm_plus, perm_base_plus, compatible.
  destruct p1; intuition. 
  destruct p2; intuition.
  destruct (compatibleb p p0); intuition.
Qed.

Theorem perm_plus_cancel (p p1 p2 : perm) : compatiblep p p1 -> (p +p p1) = (p +p p2) -> p1 = p2.
Proof.
  intros.
  generalize (compatiblep_to_alt _ _ H). unfold compatiblep_alt. intro.
  destruct p; destruct p1; destruct p2; simpl in *; intuition.
  f_equal. eapply perm_base_plus_cancel; eauto.
  unfold perm_base_plus in H0.
  rewrite H1 in H0. discriminate.
Qed.

Definition top : perm := Some top_base.

Theorem perm_plus_top p : p +p top = None.
Proof.
  intros. unfold perm_plus, perm_base_plus.
  destruct p; trivial.
  simpl. rewrite perm_base_plus_top. trivial.
Qed.

