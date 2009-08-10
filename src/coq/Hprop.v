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

Require Import Arith List QArith Bool Qcanon.

Require Import Ynot.Axioms.
Require Import Ynot.Util.
Require Import Ynot.PermModel.
Require Import Ynot.Heap.

Set Implicit Arguments.
Unset Strict Implicit.

Definition hprop := heap -> Prop.

Bind Scope hprop_scope with hprop.
Delimit Scope hprop_scope with hprop.

Definition hprop_empty : hprop := eq empty.
Notation "'__'" := hprop_empty : hprop_scope.
Notation "'emp'" := hprop_empty : hprop_scope.

Definition hprop_any : hprop := fun _ => True.
Notation "??" := hprop_any : hprop_scope.

Open Local Scope heap_scope.

Definition hprop_inj (P : Prop) : hprop := fun h => h = empty /\ P.
Notation "[ P ]" := (hprop_inj P) (at level 0, P at level 99) : hprop_scope.

Definition hprop_cell (p : ptr) T (v : T) (pi:Qc): hprop := fun h =>
  h#p = Some (Dyn v, pi) /\ forall p', p' <> p -> h#p' = None.

Notation "p -0-> v" := (hprop_cell p v 0) (at level 38, no associativity) : hprop_scope.
Notation "p -[ f ]-> v" := (hprop_cell p v f) (at level 38, no associativity) : hprop_scope.

Local Open Scope hprop_scope.
Definition disjoint (h1 h2 : heap) : Prop :=
  forall p, 
    match h1#p with
      | None => True
      | Some v1 => match h2#p with
                     | None => True
                     | Some v2 => val v1 = val v2 
                               /\ compatible (frac v1) (frac v2)
                  end
    end.

Infix "<#>" := disjoint (at level 40, no associativity) : heap_scope.

Definition split (h h1 h2 : heap) : Prop := h1 <#> h2 /\ h = h1 * h2.

Notation "h ~> h1 * h2" := (split h h1 h2) (at level 40, h1 at next level, no associativity).

Definition hprop_sep (p1 p2 : hprop) : hprop := fun h =>
  exists h1, exists h2, h ~> h1 * h2
    /\ p1 h1
    /\ p2 h2.
Infix "*" := hprop_sep (at level 40, left associativity) : hprop_scope.

Definition hprop_and (p1 p2 : hprop) : hprop := fun h => p1 h /\ p2 h.
Infix "&" := hprop_and (at level 39, left associativity) : hprop_scope.

Definition hprop_ex T (p : T -> hprop) : hprop := fun h => exists v, p v h.
Notation "'Exists' v :@ T , p" := (hprop_ex (fun v : T => p)) (at level 90, T at next level) : hprop_scope.

Definition hprop_unpack T (inh : inhabited T) (p : T -> hprop) : hprop :=
  fun h => exists v, inh = inhabits v /\ p v h.
Arguments Scope hprop_unpack [type_scope inhabited_scope hprop_scope].
Notation "inh ~~ p" := (hprop_unpack inh (fun inh => p)) (at level 91, right associativity) : hprop_scope.

(* Unfortunately, inhabit_unpack is not compositional
 *)
Definition inhabit_unpack T U (inh : [T]) (f:T -> U) : [U] :=
  match inh with
    | inhabits v => inhabits (f v)
  end.
Definition inhabit_unpack' T U (inh : [T]) (f:T -> [U]) : [U] :=
  match inh with
    | inhabits v => f v
  end.

(** TODO: Remove **)
Definition inhabit_unpack2 T T' U (inh : [T]) (inh' : [T']) (f:T -> T' -> U) : [U] :=
  match inh, inh' with
    | inhabits v, inhabits v' => inhabits (f v v')
  end.
Definition inhabit_unpack3 T T' T'' U (inh : [T]) (inh' : [T']) (inh'' : [T''])
  (f:T -> T' -> T'' -> U) : [U] :=
  match inh, inh', inh'' with
    | inhabits v, inhabits v', inhabits v'' => inhabits (f v v' v'')
  end.
Definition inhabit_unpack4 T T' T'' T''' U (inh : [T]) (inh' : [T'])
  (inh'' : [T'']) (inh''' : [T''']) (f:T -> T' -> T'' -> T''' -> U) : [U] :=
  match inh, inh', inh'', inh''' with
    | inhabits v, inhabits v', inhabits v'',inhabits v''' =>
      inhabits (f v v' v'' v''')
  end.
(** **)
Notation "inh ~~~ f" := (inhabit_unpack inh (fun inh => f))
  (at level 91, right associativity).
Notation "inh ~~~' f" := (inhabit_unpack inh (fun inh => f))
  (at level 91, right associativity).

Notation "p ':~~' e1 'in' e2" := (let p := e1 in p ~~ e2) (at level 91, right associativity) : hprop_scope.

Definition ptsto_any(p:ptr) (q:Qc): hprop := Exists A :@ Set, Exists v :@ A, p -[q]-> v.
Notation "p '-->?'" := (ptsto_any p 0) (at level 38, no associativity) : hprop_scope.
Notation "p '-[' q ']->?'" := (ptsto_any p q) (at level 38, no associativity) : hprop_scope.

(* iterating, separating conjunction -- should go in a separate file *)
Fixpoint iter_sep(P:nat->hprop)(start len:nat) {struct len} : hprop :=
  match len with
  | 0%nat => __
  | S m => (P start) * (iter_sep P (1 + start) m)
  end.
Notation "{@ P | i <- s + l }" := (iter_sep (fun i => P) s l) (i ident, s at next level) : hprop_scope.

Definition hprop_imp (p1 p2 : hprop) : Prop := forall h, p1 h -> p2 h.
Infix "==>" := hprop_imp (right associativity, at level 55).

(** * Theorems *)

Theorem sep_id : forall h p, (p * __)%hprop h -> p h.
  intuition.
  red in H. unfold hprop_empty in H.
  firstorder; subst.
  autorewrite with Ynot. trivial.
Qed.

Ltac hval_plus_solve := 
  try unfold hval_plus; 
  repeat match goal with
    | [|- Some _ = Some _ ] => f_equal
    | [|- (_, _) = (_, _) ] => f_equal
  end;  simpl; try (congruence || ring).

Ltac split_prover' :=
  unfold split, disjoint, join, read, heap, hvalo_plus, hval_plus; intuition; subst; try ext_eq;
    repeat match goal with
             | [ H : _, p : ptr |- _ ] => generalize (H p); clear H; intro H
           end.

Ltac split_prover_up :=
  split_prover';
  (repeat match goal with
           | [ H : context[match ?X with Some _ => _ | None => _ end] |- _ ] => 
             (* do inner matches first *)
             match X with
               | context[match ?X with Some _ => _ | None => _ end] => fail 1
               | _ +p _ => rewrite perm_plus_when_compat in H by auto
               | _ => destruct X; simpl in *; intuition
             end
         end);
  try hval_plus_solve.

Ltac split_prover_down :=
  split_prover';
  (repeat match goal with
           | [ |- context[match ?X with Some _ => _ | None => _ end] ] => 
             match X with
               | context[match ?X with Some _ => _ | None => _ end] => fail 1
               | _ => destruct X; intuition
             end
           | [ H : context[match ?X with Some _ => _ | None => _ end] |- _ ] => 
             match X with
               | context[match ?X with Some _ => _ | None => _ end] => fail 1
               | ?x +p ?y => rewrite perm_plus_when_compat in H by auto
               | _ => destruct X; simpl in *; intuition
             end
         end); 
  try hval_plus_solve.

Lemma disjoint_sym (h1 h2 : heap) : h1 <#> h2 -> h2 <#> h1.
Proof.
  split_prover_down.
Qed.

Hint Resolve compatible_assoc compatible_trans compatible_sym : Ynot.
Hint Rewrite perm_plus_when_compat using (eauto with Ynot): Ynot.

Theorem disjoint_assoc (h1 h2 h3 : heap) : 
     h1 <#> h2 
  -> (h1 * h2) <#> h3 
  -> (h3 * h1) <#> h2.
Proof.
  split_prover'; unfold hval_plus in *.
  destruct (h1 p); destruct (h2 p); destruct (h3 p); intuition;
  repeat (autorewrite with Ynot in *; simpl in *; intuition; ( congruence || eauto with Ynot)).
Qed.

Lemma disjoint_trans (h1 h2 h3 : heap) : h1 <#> h2 -> (h1 * h2) <#> h3 -> h1 <#> h3.
Proof.
Proof.
  split_prover'; unfold hval_plus in *.
  destruct (h1 p); destruct (h2 p); destruct (h3 p); intuition;
  repeat (autorewrite with Ynot in *; simpl in *; intuition; ( congruence || eauto with Ynot)).
Qed.

Theorem disjoint_empty : forall h, h <#> empty.
  intros; red; intros.
  destruct (h # p); simpl; auto.
Qed.

Hint Resolve disjoint_sym disjoint_assoc disjoint_trans disjoint_empty : Ynot.

Lemma split_refl x1 x2 :
     (x1 <#> x2)
  -> (x1 * x2) ~> x1 * x2.
Proof.
  intros. split; eauto with Ynot.
Qed.

Theorem split_comm : forall h h1 h2,
  h ~> h1 * h2
  -> h ~> h2 * h1.
  unfold split, disjoint; intuition; subst.

  generalize (H0 p); clear H0; intro H0.
  destruct (h1 # p); destruct (h2 # p);
  intuition; auto with Ynot.
  
  unfold heap, join; ext_eq.
  generalize (H0 x); unfold read.
  destruct (h1 x); destruct (h2 x); intuition.
  simpl. rewrite hval_plus_comm; trivial.
Qed.

Theorem split_id : forall h, h ~> h * empty.
  intros; red; intuition auto with Ynot.
Qed.

Hint Resolve split_comm split_id : Ynot.

Ltac disj_read_finder :=
repeat match goal with
    | [H: ?h1 # ?p = _ |- _] => rewrite H in *; clear H
    | [H: ?h2 # ?p = _ |- _] => rewrite H in *; clear H
    | [H: ?h1 <#> ?h2, H2:context [?h1 # ?p] |- _] => extend (H p)
    | [H: ?h1 <#> ?h2, H2:context [?h2 # ?p] |- _] => extend ((disjoint_sym H) p)
       end.

Lemma disjoint_both_eq : forall h1 h2 p v1 v2,
  h1 <#> h2 -> h1 # p = Some v1 -> h2 # p = Some v2 -> val v1 = val v2.
Proof.
  intuition; disj_read_finder; intuition.
Qed.

Theorem split_read :  forall h h1 h2 p,
     h ~> h1 * h2
  -> h # p = (h1 # p) +o (h2 # p).
Proof.
  intuition.
  red in H. intuition. subst.
  unfold join, read. trivial.
Qed.

Theorem split_read1 : forall h h1 h2 p v,
  h ~> h1 * h2
  -> h1 # p = Some v
  -> h  # p =  Some (val v, frac v + ofrac (h2 # p)).
  intuition.
  generalize (split_read p H).
  unfold hvalo_plus, hval_plus, ofrac.
  red in H. destruct H. subst.
  generalize (H p).
  unfold join, read in *. rewrite H0.
  destruct (h2 p); simpl; intuition.
  unfold hval_plus.
  rewrite (perm_plus_when_compat H4). trivial.

  rewrite Qcplus_0_r. destruct v; trivial.
Qed.

Theorem split_read2 : forall h h1 h2 p v,
  h ~> h1 * h2
  -> h2 # p = Some v
  -> h  # p = Some (val v, ofrac (h1 # p) + frac v).
  intuition.
  rewrite Qcplus_comm.
  exact (split_read1 (split_comm H) H0).
Qed.

Hint Resolve split_read1 split_read2 : Ynot.

Theorem split_read_inj1 : forall h h1 h2 p (T : Set) (v v1 : T) q1 q2,
  h ~> h1 * h2
  -> h # p = Some (Dyn v, q1)
  -> h1 # p = Some (Dyn v1, q2)
  -> v = v1.
  intros.
  generalize (split_read1 H H1). rewrite H0.
  simpl. intros. 
  apply Dyn_inj. congruence.
Qed.

Theorem split_read_inj2 : forall h h1 h2 p (T : Set) (v v1 : T) q1 q2,
  h ~> h1 * h2
  -> h # p = Some (Dyn v, q1)
  -> h2 # p = Some (Dyn v1, q2)
  -> v = v1.
  intros.
  generalize (split_read2 H H1). rewrite H0.
  simpl. intros. 
  apply Dyn_inj. congruence.
Qed.

Theorem split_writeSN : forall h h1 h2 p (T T' : Set) (v : T) (v' : T') q1,
  h ~> h1 * h2
  -> h1 # p = Some (Dyn v, q1)
  -> h2 # p = None
  -> (h ## p <- (Dyn v', q1)) ~> (h1 ## p <- (Dyn v', q1)) * h2.

  intros.
  red in H; intuition; subst.
  unfold split, disjoint, join, write, read; intuition; subst.

  destruct (ptr_eq_dec p0 p); subst; unfold join, read in *.
    rewrite H1 in *; trivial.    
    apply (H2 p0).

  unfold heap; ext_eq.
  destruct (ptr_eq_dec x p); trivial.
  unfold read in *; simpl; subst. rewrite H1. trivial.
Qed.

Theorem split_writeNS : forall h h1 h2 p (T T' : Set) (v : T) (v' : T') q2,
  h ~> h1 * h2
  -> h1 # p = None
  -> h2 # p = Some (Dyn v, q2)
  -> (h ## p <- (Dyn v', q2)) ~> h1 * (h2 ## p <- (Dyn v', q2)).
  
  intros.
  
  red in H; intuition; subst.
  unfold split, disjoint, join, write, read; intuition; subst.

  destruct (ptr_eq_dec p0 p); subst; unfold join, read in *.
    rewrite H0 in *; trivial.    
    apply (H2 p0).

  unfold heap; ext_eq.
  destruct (ptr_eq_dec x p); trivial.
  unfold read in *; simpl; subst. rewrite H0. trivial.
Qed.

Theorem split_writeSS : forall h h1 h2 p (T T' : Set) (v : T) (v' : T') q1 q2,
  h ~> h1 * h2
  -> h1 # p = Some (Dyn v, q1)
  -> h2 # p = Some (Dyn v, q2)
  -> (h ## p <- (Dyn v', q1+q2)) ~> (h1 ## p <- (Dyn v', q1)) * (h2 ## p <- (Dyn v', q2)).

  intros.
  red in H; intuition; subst.
  unfold split, disjoint, join, write, read; intuition; subst.

  destruct (ptr_eq_dec p0 p); subst; unfold join, read in *.
    generalize (H2 p); unfold read; rewrite H0; rewrite H1; intuition.
    apply (H2 p0).

  unfold heap; ext_eq.
  destruct (ptr_eq_dec x p); simpl; trivial.
  unfold hval_plus. simpl.
  generalize (H2 p). rewrite H0; rewrite H1. simpl.  intuition.
  rewrite (perm_plus_when_compat H4). trivial.
Qed.

Hint Resolve split_writeSN split_writeNS split_writeSS : Ynot.

Theorem new_sep : forall h p (T : Set) (v : T) q,
  h # p = None
  -> (h ## p <- (Dyn v, q)) ~> (p |--> (Dyn v, q)) * h.
  intros.
  red; intuition.
  red; intuition.

  unfold singleton, read in *.
  destruct (ptr_eq_dec p0 p); subst; trivial.
  rewrite H; trivial.

  unfold read, write, singleton, join, heap in *; ext_eq.
  destruct (ptr_eq_dec x p); subst; trivial.
  rewrite H. trivial.
Qed.

Hint Resolve new_sep : Ynot.

Theorem split_id_invert : forall h h',
  h ~> empty * h'
  -> h = h'.
  intros.
  destruct H.
  subst.
  unfold empty, join, heap; ext_eq; trivial.
Qed.

Theorem split2_read : forall h h1 h2 h3 h4 p d,
  h ~> h1 * h2
  -> h1 ~> h3 * h4
  -> h3 # p = Some d
  -> h # p = Some (val d, frac d + ofrac (h4 # p) + ofrac (h2 # p)).
  intros.
  generalize (split_read1 H0 H1). intro.
  generalize (split_read1 H H2).  simpl. trivial.
Qed.

Hint Resolve split2_read : Ynot.

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

Theorem split_readS0N : forall h h1 h2 p d,
  (h ~> h1 * h2
  -> h1 # p = Some (d, 0)
  -> h2 # p = None)%heap.
Proof.
  intros.
  remember (h2 # p)%heap as h2p. destruct h2p; trivial.
  destruct h0.
  generalize (split_readSS_compat H H0 (sym_eq Heqh2p)).
  intro. elim (compatible_top (compatible_sym H1)).
Qed.

Lemma split_read_S0 h h1 h2 d p : 
  h ~> h1 * h2 
  -> (h1 # p = Some (d, 0)
  -> h # p = Some (d, 0))%heap.
Proof.
  intros.
  generalize (split_read1 H H0).
  generalize (split_readS0N H H0). intros. 
  rewrite H1 in H2. simpl in *. auto.
Qed.

Hint Resolve split_read_S0 : Ynot.

Lemma free_none_eq h p : (h # p = None -> h ### p = h)%heap.
Proof.
  unfold read, free, heap. intros. ext_eq.
  destruct (ptr_eq_dec x p); congruence.
Qed.

Hint Resolve free_none_eq : Ynot.


Lemma hvalo_plus_none_r v1 : v1 +o None = v1.
Proof.
  destruct v1; intuition.
Qed.


Theorem hvalo_plus_assoc (p1 p2 p3 : option hval) :
      ofrac p1 |#| ofrac p2 
   -> ofrac (p1 +o p2) |#| ofrac p3
   -> (p1 +o (p2 +o p3) = (p1 +o p2) +o p3)%heap.
Proof.
  intros.
  destruct p1; destruct p2; destruct p3; intuition;
  simpl in *; unfold hval_plus in *; simpl in *.

  generalize (perm_plus_ass (frac h) (frac h0) (frac h1)); intro.
  remember ((frac h0) +p (frac h1)) as r1. 
  remember (frac h +p frac h0) as r2.
  destruct r1; destruct r2; simpl in *; intuition.
  rewrite H1; auto.
  rewrite perm_plus_when_compat in Heqr2 by auto; discriminate.
  rewrite perm_plus_when_compat in H1 by auto. discriminate.
  rewrite perm_plus_when_compat in Heqr2 by auto. discriminate.
  
  rewrite perm_plus_when_compat in * by auto. auto.
Qed.

Theorem join_comm (h1 h2 : heap) :
  h1 <#> h2 -> (h1 * h2 = h2 * h1)%heap.
Proof.
  split_prover'.
  destruct (h1 x); destruct (h2 x); intuition.
  rewrite perm_plus_comm. rewrite H0. trivial.
Qed.

Theorem join_assoc (h1 h2 h3 : heap) : 
     h1 <#> h2 
  -> (h1 * h2) <#> h3 
  -> (h1 * (h2 * h3) = (h1 * h2) * h3)%heap.
Proof.
  split_prover'.
  destruct (h1 x); destruct (h2 x); destruct (h3 x); simpl; intuition.

  generalize (perm_plus_ass (frac h) (frac h0) (frac h4)); intro.
  remember ((frac h0) +p (frac h4)) as r1. 
  remember (frac h +p frac h0) as r2.
  destruct r1; destruct r2; simpl in *; intuition.
  rewrite H; auto.
  rewrite perm_plus_when_compat in Heqr2 by auto; discriminate.
  rewrite perm_plus_when_compat in H by auto. discriminate.
  rewrite perm_plus_when_compat in Heqr2 by auto. discriminate.
  
  rewrite perm_plus_when_compat in * by auto. auto.
Qed.


Theorem disjoint_join_sym (h1 h2 h3 : heap) :
     h1 <#> h3 
  -> h2 <#> h3
  -> (h1 * h2) <#> h3 -> (h2 * h1) <#> h3.
Proof.
  split_prover'.
  destruct (h1 p); destruct (h2 p); destruct (h3 p); intuition;
  rewrite perm_plus_comm;
  destruct (frac h +p frac h0); simpl; intuition; congruence.
Qed.

Theorem disjoint_join_sym2 (h1 h2 h3 : heap) :
     h1 <#> h2 
  -> (h1 * h2) <#> h3 -> (h2 * h1) <#> h3.
Proof. intros. rewrite join_comm; eauto with Ynot. Qed.

Hint Resolve disjoint_join_sym disjoint_join_sym2  : Ynot.

Theorem disjoint_assoc2 (h1 h2 h3 : heap) :
     (h1 <#> h2 
  -> (h1 * h2) <#> h3 
  -> h1 <#> (h2 * h3))%heap.
Proof.
  intros. 
  generalize (disjoint_trans H H0). intro.
  eauto with Ynot.
Qed.

Hint Resolve disjoint_assoc2 : Ynot.

Hint Resolve join_comm join_assoc : Ynot.

Theorem split_splice : forall h h1 h2 h3 h4,
  h ~> h1 * h2
  -> h1 ~> h3 * h4
  -> h ~> h4 * (h2 * h3).
Proof.
  intros.
  assert ((h2 * h3) <#> h4); unfold split in *; intuition; subst; eauto with Ynot.

  rewrite join_comm; auto.
  rewrite (@join_assoc h2); eauto with Ynot.
Qed.

Hint Resolve split_splice : Ynot.

Theorem split_splice' : forall h x x0 x1 x2,
  h ~> x * x0
  -> x ~> x1 * x2
  -> h ~> x1 * (x2 * x0).
  unfold split; intuition; subst.
  eauto with Ynot.

  rewrite join_assoc; trivial.
Qed.

Theorem split_splice'' : forall h x x0 x1 x2,
  h ~> x * x0
  -> x0 ~> x1 * x2
  -> h ~> (x * x1) * x2.
  unfold split; intuition; subst.
  eauto with Ynot.

  rewrite join_assoc; eauto with Ynot.
Qed.

Theorem split_shuffle : forall h h1 h2 h3 h' h'' h''',
  h ~> h1 * (h2 * h3)
  -> h' ~> h'' * h2
  -> h'' ~> h3 * h'''
  -> h ~> (h1 * h3) * h2.
  unfold split; intuition; subst;
  generalize (disjoint_trans H0 H); intro.
  eauto with Ynot.
  rewrite (@join_comm h2); eauto with Ynot.
  
  apply join_assoc. 
  apply disjoint_sym. 
  eapply disjoint_trans. 
  eauto. rewrite join_comm; eauto with Ynot.

  eauto with Ynot.
Qed.

Hint Resolve split_shuffle : Ynot.

(*
Theorem split_comm' : forall h1 h2 h h',
  h ~> h1 * (h2 * h')
  -> (h1 * h2) ~> h2 * h1.
  split_prover_down.
Qed.

Hint Resolve split_comm' : Ynot.
*)

Theorem split_self : forall h x x0 x1 x2,
  h ~> x * x0
  -> x ~> x1 * x2
  -> (x2 * x0) ~> x2 * x0.
  unfold split; intuition; subst.
  eauto with Ynot.
Qed.

Theorem split_self' : forall h x x0 x1 x2,
  h ~> x * x0
  -> x0 ~> x1 * x2
  -> (x * x1) ~> x * x1.
  unfold split; intuition; subst.
  eauto with Ynot.
Qed.

Theorem split_splice''' : forall h x x0 x1 x2,
  h ~> x * x0
  -> x0 ~> x1 * x2
  -> h ~> (x1 * x) * x2.
  unfold split; intros; 
  assert ((x1 * x) <#> x2); intuition; subst.

  apply disjoint_sym; apply disjoint_assoc2; eauto with Ynot. 

  rewrite join_assoc;  eauto with Ynot.
  rewrite (@join_comm x); eauto with Ynot.
Qed.

Theorem split_self'' : forall h x x0 x1 x2,
  h ~> x * x0
  -> x0 ~> x1 * x2
  -> (x1 * x) ~> x1 * x.
  unfold split; intuition; subst.
  eauto with Ynot.
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
    repeat rewrite perm_plus_when_compat in H0 by eauto with Ynot; simpl in *.
    intuition.
      congruence.
      apply compatible_sym.
      eapply compatible_trans; eauto.
      rewrite Qcplus_comm. eauto with Ynot.
  Qed.

Theorem split_free : forall h h1 h2 p d,
  h ~> h1 * h2
  -> h1 # p = Some d
  -> (forall p' : ptr, (p' = p -> False) -> h1 # p' = None)
  -> (h ### p) ~> empty * (h2 ### p).
  intros.

  replace (h ### p) with (h2 ### p).
  auto with Ynot.
  unfold free, heap; ext_eq.
  destruct (ptr_eq_dec x p); auto.
  generalize (H1 _ n); intro.
  red in H; intuition; subst.
  unfold join, hvalo_plus. unfold read in H2.
  rewrite H2; trivial.
Qed.

Theorem pack_type_inv : forall (T : Type) (a : inhabited T),
  exists b, a = inhabits b.
  intros; case_eq a; intros t; exists t; auto.
Qed.

Hint Resolve split_free : Ynot.
