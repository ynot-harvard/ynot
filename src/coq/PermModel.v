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
Require Import Qcanon.
Opaque Qcplus. Opaque Qcopp.
Require Import Ynot.Axioms.

Set Implicit Arguments.
Unset Strict Implicit.

(* zeroth some general lemmas that are not specific to this particular development *)

Lemma Qcle_bool_iff (x y : Qc) : Qle_bool x y = true <-> (x <= y)%Qc.
Proof. unfold Qcle. intros. apply Qle_bool_iff. Qed.

Theorem Some_inj : forall T (x y : T),
  Some x = Some y
  -> x = y.
  intros; congruence.
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

(* first we define the underlying set of permissions and its partial additive function *)
Definition perm := Qc.

(* notations and basic lemmas *)
Definition Qc0 := (Q2Qc (Qmake Z0 xH)).
Notation "00" := Qc0.

Definition top : perm := 00.

(* The definition of compatibility (not in-compatible): 
 *  two permissions are in-compatible if 
 *     (p1 >= 0 /\ p2 >= 0)
 *  \/ (   (p1 >= 0 \/ p2 >= 0) 
 *      /\ p1 + p2 < 0)
 *)

Definition compatibleb (p1 p2 : perm) : bool :=
let p1pos := Qle_bool 00 p1 in
  let p2pos := Qle_bool 00 p2 in
    negb (
         (p1pos && p2pos)
      || ((p1pos || p2pos) && (negb (Qle_bool 00 ((p1 + p2)%Qc)))))%Qc.

Theorem compatibleb_comm (p1 p2 : perm) : compatibleb p1 p2 = compatibleb p2 p1.
Proof.  intros. unfold compatibleb.
       rewrite Qcplus_comm. 
       rewrite andb_comm. f_equal. f_equal. f_equal.
       rewrite orb_comm. f_equal.
Qed.

Theorem compatibleb_top (p : perm) : compatibleb p top = false.
Proof.
  unfold compatibleb, top. intros. 
  rewrite andb_true_r. rewrite orb_true_r. simpl.
  rewrite <- (negb_involutive false). f_equal. simpl.
  rewrite Qcplus_0_r.
  destruct (Qle_bool 00 p); intuition.
Qed.

Definition compatible (p1 p2 : perm) := compatibleb p1 p2 = true.

Infix "|#|" := compatible (at level 60, no associativity).

Lemma compatible_sym (p1 p2 : perm) : compatible p1 p2 -> compatible p2 p1.
Proof. unfold compatible. intros. rewrite compatibleb_comm. trivial. Qed.

Hint Resolve compatible_sym : Ynot.

Theorem compatible_opp (p : perm) : p <> top -> compatible p (- p).
Proof.
  unfold compatible, compatibleb, top. intros.
  rewrite Qcplus_opp_r. simpl.
  rewrite andb_false_r. rewrite orb_false_r.
  generalize (Qle_bool_iff 0 p); intro; destruct (Qle_bool 00 p); simpl; trivial.
  generalize (Qle_bool_iff 0 (- p)%Qc); intro; destruct (Qle_bool 0 (- p)%Qc); simpl; trivial.
  generalize (((proj1 H0) (reflexivity true))); clear H0; intro H0.
  generalize (((proj1 H1) (reflexivity true))); clear H1; intro H1.
  generalize (proj2 (Qcle_minus_iff p 0)). simpl.
  rewrite Qcplus_0_l. intro.
  generalize (H2 H1). intro.
  elim H.
  generalize (Qle_antisym _ _ H0 H3).
  intro. apply Qc_is_canon. symmetry. auto.
Qed.

Theorem compatible_top (p:perm) : compatible p top -> False.
Proof.
  unfold compatible. intro. rewrite (compatibleb_top p). discriminate.
Qed.

(* adding two permissions.  Addition is a partial function.
 * Only compatible permissions can be added. 
 *)

Definition perm_plus (p1 p2 : perm) : option perm := 
  if compatibleb p1 p2 then Some (p1 + p2) else None.

Infix "+p" := perm_plus (at level 60, no associativity).

Definition perm_plus_compat (p1 p2 : perm) (pf:compatible p1 p2) : perm := p1 + p2.

Lemma perm_plus_is_compat (p1 p2 : perm) (pf:compatible p1 p2) : perm_plus p1 p2 = Some (perm_plus_compat pf).
Proof. unfold compatible, perm_plus, perm_plus_compat. intros. rewrite pf. trivial. Qed.

Lemma perm_plus_when_compat (p1 p2 : perm) (pf:compatible p1 p2) : perm_plus p1 p2 = Some (p1 + p2).
Proof. unfold compatible, perm_plus, perm_plus_compat. intros. rewrite pf. trivial. Qed.

(* We show it has some nice properties as in section 3 of Brookes *)
(* SYM *)
Theorem perm_plus_comm (p1 p2 : perm) : p1 +p p2 = p2 +p p1.
Proof.
  unfold perm_plus. intros. rewrite Qcplus_comm. rewrite compatibleb_comm. trivial.
Qed.

(* CANC *)
Theorem perm_plus_cancel (p p1 p2 : perm) : compatible p p1 -> (p +p p1) = (p +p p2) -> p1 = p2.
Proof.
  unfold perm_plus, compatible.  intros. 
  rewrite H in H0. destruct (compatibleb p p2); try discriminate.
  generalize (Some_inj H0). intro.
  unfold perm in *.
  assert (C: -p + (p + p1) = -p + (p + p2)) by (rewrite H1; trivial).
  replace (-p + (p + p1)) with (p1) in C by ring.
  replace (-p + (p + p2)) with (p2) in C by ring.
  trivial. 
Qed.

(* TOP *)
Theorem perm_plus_top (p : perm) : top +p p = None.
Proof.
  unfold perm_plus. intros. rewrite compatibleb_comm. rewrite compatibleb_top. trivial.
Qed.

(* NON-ZERO *)
Theorem perm_plus_nonzero (p p' : perm) : compatible p p' -> p +p p' <> Some p.
Proof.
  unfold compatible, perm_plus.
  intros.
  rewrite H. intro.
  generalize (Some_inj H0). clear H0; intro H0.
  generalize (f_equal (Qcplus (- p)) H0).
  intro. ring_simplify in H1.
  rewrite H1 in H.
  generalize (perm_plus_top p). rewrite perm_plus_comm.
  unfold perm_plus, top, Q2Qc. simpl; intro.
  rewrite H in H2. discriminate.
Qed.

(* COMP *)
Theorem perm_comp (p : perm) : p <> top -> p +p (- p) = Some top.
Proof.
  unfold perm_plus. intros. rewrite compatible_opp; auto.
  rewrite Qcplus_opp_r. auto.
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

Lemma Qle_bool_false (p1 p2 : Qc) : Qle_bool p1 p2 = false -> (p2 < p1).
Proof.
  intros.
  generalize ((proj2 (Qle_bool_iff p1 p2))). rewrite H.
  destruct (Qlt_le_dec p2 p1); intuition; try discriminate.
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



  Ltac btol := repeat match goal with
    | [H: ?x = ?x |- _] => clear H
    | [H: true = _ |- _] => symmetry in H
    | [H: false = _ |- _] => symmetry in H
    | [|- context [Qle_bool ?x ?y]] =>  generalize (Qle_bool_iff x y); intro; destruct (Qle_bool x y)
    | [|- context [Qeq_bool ?x ?y]] =>  generalize (Qeq_bool_iff x y); intro; destruct (Qeq_bool x y)
    | [H: Qle_bool 0 ?y = true |- _] =>  generalize ((proj1 (Qcle_bool_iff 00 _)) H); clear H; intro H
    | [H: Qeq_bool ?x ?y = true |- _] =>  generalize ((proj1 (Qeq_bool_iff x y)) H); clear H; intro H
    | [H: Qle_bool 0 ?y = false |- _] =>  generalize (@Qle_bool_false 00 _ H); clear H; intro H
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


  Ltac translelt :=
    match goal with
      | [H1:?x < ?y, H2: ?y <= ?z |- _] => extend (Qclt_le_trans _ _ _ H1 H2)
      | [H1:?x <= ?y, H2: ?y < ?z |- _] => extend (Qcle_lt_trans _ _ _ H1 H2)
      | [H1:?x <= ?y, H2: ?y <= ?z |- _] => extend (Qcle_trans _ _ _ H1 H2)
    end.

  Ltac toR := match goal with
    | [H: ?x < _ |- _] => 
      match x with
        |  0 => fail 1
        | _ => 
          let newH := fresh "newH" in
            generalize ((proj1 (Qclt_minus_iff _ _)) H); intro newH
              ; ring_simplify in newH;
              let t := type of newH in revert newH; 
                notHyp newH; clear H; intro H
      end
  end.

  Ltac find_ltcontra1 :=
  match goal with
    | [H1: 0 < ?x, H2:0 < 0 + - ?x |- _] => 
      elim (Qclt_not_le _ _ H1); 
        apply Qclt_le_weak; auto;
          apply ((proj2 (Qclt_minus_iff _ _))); auto
  end.

  Ltac find_ltcontra2 :=
    unfold Q2Qc in *
  ; simpl in *
  ; match goal with
      | [H: ?x < ?x |- _] => elim (Qclt_not_eq _ _ H); reflexivity
    end.

  Ltac ltcontra := 
    repeat translelt
  ; repeat toR
  ; (find_ltcontra1 || find_ltcontra2).

Theorem compatibleb_assoc (p1 p2 p3 : perm) : 
     compatibleb p1 p2 = true
  -> compatibleb (p1 + p2) p3 = true
  -> compatibleb (p3 + p1) p2 = true.
Proof.
  intros.
  desb;
  unfold compatibleb in *. 
  remember (Qle_bool 0%Qc p1) as b; destruct b;
  remember (Qle_bool 0%Qc p2) as b; destruct b;
  remember (Qle_bool 0%Qc p3) as b; destruct b;
  simpl in *;
    try discriminate; repeat rewrite negb_involutive in *;
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
    try (elimtype False; eauto); ltcontra.
Qed.
  
Lemma compatibleb_trans (p1 p2 p3 : perm) : 
  compatibleb p1 p2 = true 
  -> compatibleb (p1 + p2) p3 = true 
  -> compatibleb p1 p3 = true.
Proof.
  intros.
  desb;
  unfold compatibleb in *. 
  remember (Qle_bool 0%Qc p1) as b; destruct b;
  remember (Qle_bool 0%Qc p2) as b; destruct b;
  remember (Qle_bool 0%Qc p3) as b; destruct b;
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
    try (elimtype False; eauto); ltcontra.
Qed.

Theorem compatible_assoc (p1 p2 p3 : perm) : 
     p1 |#| p2
  -> (p1 + p2) |#| p3
  -> (p3 + p1) |#| p2.
Proof.
  unfold compatible. intros.
  apply (compatibleb_assoc H H0).
Qed.

Lemma compatible_trans (p1 p2 p3 : perm) : compatible p1 p2 -> compatible (p1 + p2) p3 -> compatible p1 p3.
Proof.
  unfold compatible. intros.
  apply (compatibleb_trans H H0).
Qed.

Theorem perm_plus_ass (p1 p2 p3 : perm) : 
  match p2 +p p3 with
    | None => None
    | Some p2p3 => p1 +p p2p3
  end =
  match p1 +p p2 with
    | None => None
    | Some p1p2 => p1p2 +p p3
  end.
Proof.
  unfold perm_plus.
  intros p p0 p1.
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
    try (elimtype False; eauto); ltcontra.
Qed.


(* We now lift this to a set of optional permissions with total + *)
Definition permo := option perm.

Definition permo_valid (p:permo) := if p then True else False.

Definition permo_plus (p1 p2 : permo) : permo :=
  match p1 with
    | None => None
    | Some p1' => 
      match p2 with
        | None => None
        | Some p2' => p1' +p p2'
      end
  end.

Infix "+po" := permo_plus (at level 59, left associativity).

Definition compatiblep (p1 p2 : permo) := permo_valid (p1 +po p2).

Theorem permo_plus_comm (p1 p2 : permo) : p1 +po p2 = p2 +po p1.
Proof.
  destruct p1; destruct p2; simpl; trivial. apply perm_plus_comm.
Qed.


(* wow, does this need cleanup *)
Theorem permo_plus_ass (p1 p2 p3 : permo) : p1 +po (p2 +po p3) = (p1 +po p2) +po p3.
Proof.
  unfold permo_plus, perm_plus.
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
    try (elimtype False; eauto); ltcontra.
Qed.

Definition compatiblep_alt (p1 p2 : permo) :=
  match p1 with
    | None => False
    | Some p1' => 
      match p2 with
        | None => False
        | Some p2' => compatible p1' p2'
      end
  end.

Lemma compatiblep_to_alt (p1 p2 : permo) : compatiblep p1 p2 -> compatiblep_alt p1 p2.
Proof.
  unfold compatiblep, compatiblep_alt, permo_valid, permo_plus, perm_plus, compatible.
  destruct p1; intuition. 
  destruct p2; intuition.
  destruct (compatibleb p p0); intuition.
Qed.

Theorem permo_plus_cancel (p p1 p2 : permo) : compatiblep p p1 -> (p +po p1) = (p +po p2) -> p1 = p2.
Proof.
  intros.
  generalize (compatiblep_to_alt H). unfold compatiblep_alt. intro.
  destruct p; destruct p1; destruct p2; simpl in *; intuition.
  f_equal. eapply perm_plus_cancel; eauto.
  unfold perm_plus in H0.
  rewrite H1 in H0. discriminate.
Qed.

Definition topo : permo := Some top.

Theorem permo_plus_topo p : topo +po p = None.
Proof.
  intros. unfold permo_plus.
  destruct p; trivial.
  simpl. apply perm_plus_top.
Qed.

Theorem permo_plus_nonzero (p p' :permo) : compatiblep p p' -> p +po p' <> p.
Proof.
  intros. generalize (compatiblep_to_alt H).  unfold compatiblep_alt.
  destruct p; destruct p'; intuition.
  simpl in H1. eapply perm_plus_nonzero; eauto.
Qed.

