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

Require Import Arith List.

Require Import Ynot.Axioms.
Require Import Ynot.Util.
Require Import Ynot.Heap.

Set Implicit Arguments.


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

Definition hprop_cell (p : ptr) T (v : T) : hprop := fun h =>
  h#p = Some (Dyn v) /\ forall p', p' <> p -> h#p' = None.
Infix "-->" := hprop_cell (at level 38, no associativity) : hprop_scope.

Definition disjoint1 (h1 h2 : heap) : Prop :=
  forall p,
    match h1#p with
      | None => True
      | Some _ => match h2#p with
                    | None => True
                    | Some _ => False
                  end
    end.

Infix "<##>" := disjoint1 (at level 40, no associativity) : hprop_scope.

Open Local Scope hprop_scope.

Definition disjoint (h1 h2 : heap) : Prop := h1 <##> h2 /\ h2 <##> h1.

Infix "<#>" := disjoint (at level 40, no associativity) : hprop_scope.

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

Definition ptsto_any(p:ptr) : hprop := Exists A :@ Set, Exists v :@ A, p --> v.
Notation "p '-->?'" := (ptsto_any p) (at level 38, no associativity) : hprop_scope.

(* iterating, separating conjunction -- should go in a separate file *)
Fixpoint iter_sep(P:nat->hprop)(start len:nat) {struct len} : hprop :=
  match len with
  | 0 => __
  | S m => (P start) * (iter_sep P (1 + start) m)
  end.
Notation "{@ P | i <- s + l }" := (iter_sep (fun i => P) s l) (i ident, s at next level) : hprop_scope.

Definition hprop_imp (p1 p2 : hprop) : Prop := forall h, p1 h -> p2 h.
Infix "==>" := hprop_imp (right associativity, at level 85).


(** * Theorems *)

Theorem sep_id : forall h p, (p * __)%hprop h -> p h.
  intuition.
  red in H.
  firstorder; subst.

  replace (x * x0)%heap with x; auto.

  unfold heap; ext_eq.

  unfold join.
  destruct (x x1); auto.
  red in H2.
  rewrite <- H2.
  trivial.
Qed.

Theorem disjoint1_empty1 : forall h, h <##> empty.
  intros; red; intros.
  destruct (h # p); simpl; auto.
Qed.

Theorem disjoint1_empty2 : forall h, empty <##> h.
  intros; red; intros.
  destruct (h # p); simpl; auto.
Qed.

Hint Resolve disjoint1_empty1 disjoint1_empty2 : Ynot.

Theorem disjoint_empty1 : forall h, h <#> empty.
  intros; red; intuition auto with Ynot.
Qed.

Theorem disjoint_empty2 : forall h, empty <#> h.
  intros; red; intuition auto with Ynot.
Qed.

Hint Resolve disjoint_empty1 disjoint_empty2 : Ynot.

Theorem split_id1 : forall h, h ~> h * empty.
  intros; red; intuition auto with Ynot.
Qed.

Theorem split_id2 : forall h, h ~> empty * h.
  intros; red; intuition auto with Ynot.
Qed.

Hint Resolve split_id1 split_id2 : Ynot.

Theorem split_read1 : forall h h1 h2 p v,
  h ~> h1 * h2
  -> h1 # p = Some v
  -> h # p = Some v.
  intuition.
  red in H; intuition; subst.
  unfold join, read in *.
  rewrite H0; trivial.
Qed.

Theorem split_read2 : forall h h1 h2 p v,
  h ~> h1 * h2
  -> h2 # p = Some v
  -> h # p = Some v.
  intuition.
  red in H; intuition; subst.

  red in H1; intuition.
  generalize (H p).

  unfold join, read in *.
  rewrite H0; trivial.

  destruct (h1 p); tauto.
Qed.

Hint Resolve split_read1 split_read2 : Ynot.

Theorem Some_inj : forall T (x y : T),
  Some x = Some y
  -> x = y.
  intros; congruence.
Qed.

Theorem split_read_inj1 : forall h h1 h2 p (T : Set) (v v1 : T),
  h ~> h1 * h2
  -> h # p = Some (Dyn v)
  -> h1 # p = Some (Dyn v1)
  -> v = v1.
  intros.
  red in H; intuition; subst.
  unfold join, read in *.
  rewrite H1 in H0.
  generalize (Some_inj H0); clear H0; intro H0.
  apply Dyn_inj; auto.
Qed.

Theorem split_read_inj2 : forall h h1 h2 p (T : Set) (v v1 : T),
  h ~> h1 * h2
  -> h # p = Some (Dyn v)
  -> h2 # p = Some (Dyn v1)
  -> v = v1.
  intros.
  red in H; intuition; subst.
  red in H2; intuition.
  generalize (H3 p); intro Hdisj.
  unfold join, read in *.
  rewrite H1 in Hdisj.
  destruct (h1 p); auto.
  tauto.
  rewrite H1 in H0.
  generalize (Some_inj H0); clear H0; intro H0.
  apply Dyn_inj; auto.
Qed.

Theorem split_write1 : forall h h1 h2 p (T T' : Set) (v : T) (v' : T'),
  h ~> h1 * h2
  -> h1 # p = Some (Dyn v)
  -> (h ## p <- Dyn v') ~> (h1 ## p <- Dyn v') * h2.
  unfold split, disjoint, disjoint1, join, write, read; intuition; subst.

  destruct (ptr_eq_dec p0 p); subst.
  generalize (H3 p); intro Hp.
  destruct (h2 p); trivial.
  rewrite H0 in Hp; trivial.

  apply H.

  generalize (H3 p0); intro Hp0.
  destruct (h2 p0); trivial.

  destruct (ptr_eq_dec p0 p); subst; trivial.

  rewrite H0 in Hp0; trivial.

  unfold heap; ext_eq.
  destruct (ptr_eq_dec x p); trivial.
Qed.

Theorem split_write2 : forall h h1 h2 p (T T' : Set) (v : T) (v' : T'),
  h ~> h1 * h2
  -> h2 # p = Some (Dyn v)
  -> (h ## p <- Dyn v') ~> h1 * (h2 ## p <- Dyn v').
  intros.
  red in H; intuition; subst.
  red in H1; intuition.
  red; intuition.
  red; intuition.

  intro.
  generalize (H p0).
  unfold write, read in *.
  destruct (h1 p0); trivial.
  destruct (ptr_eq_dec p0 p); subst; auto.
  rewrite H0; auto.

  intro.
  generalize (H2 p0).
  unfold write, read in *.
  destruct (ptr_eq_dec p0 p); subst; auto.
  rewrite H0; auto.

  generalize (H p); intro Hp.
  unfold read, write, join, heap in *.
  ext_eq.
  destruct (ptr_eq_dec x p); subst; trivial.
  destruct (h1 p); trivial.
  rewrite H0 in Hp; tauto.
Qed.

Hint Resolve split_write1 split_write2 : Ynot.

Theorem new_sep : forall h p (T : Set) (v : T),
  h # p = None
  -> (h ## p <- Dyn v) ~> (p --> Dyn v) * h.
  intros.
  red; intuition.
  red; intuition.

  intro.
  unfold singleton, read in *.
  destruct (ptr_eq_dec p0 p); subst; trivial.
  rewrite H; trivial.

  intro.
  unfold read, write, singleton in *.
  destruct (ptr_eq_dec p0 p); subst; trivial.
  rewrite H; trivial.

  destruct (h p0); trivial.

  unfold read, write, singleton, join, heap in *; ext_eq.
  destruct (ptr_eq_dec x p); subst; trivial.
Qed.

Hint Resolve new_sep : Ynot.

Theorem split_id1_invert : forall h h',
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
  -> h # p = Some d.
  unfold split, disjoint, disjoint1, read, join; intuition; subst.
  rewrite H1; trivial.
Qed.

Hint Resolve split2_read : Ynot.

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

Ltac split_prover' :=
  unfold split, disjoint, disjoint1, join, read, heap; intuition; subst; try ext_eq;
    repeat match goal with
             | [ H : _, p : ptr |- _ ] => generalize (H p); clear H; intro H
           end.

Ltac split_prover_up :=
  split_prover';
  repeat match goal with
           | [ H : context[match ?X with Some _ => _ | None => _ end] |- _ ] => destruct X; intuition
         end.

Ltac split_prover_down :=
  split_prover';
  repeat match goal with
           | [ |- context[match ?X with Some _ => _ | None => _ end] ] => destruct X; intuition
           | [ H : context[match ?X with Some _ => _ | None => _ end] |- _ ] => destruct X; intuition
         end.

Theorem split_splice : forall h h1 h2 h3 h4,
  h ~> h1 * h2
  -> h1 ~> h3 * h4
  -> h ~> h4 * (h2 * h3).
  split_prover_up.
Qed.

Hint Resolve split_splice : Ynot.

Theorem split_splice' : forall h x x0 x1 x2,
  h ~> x * x0
  -> x ~> x1 * x2
  -> h ~> x1 * (x2 * x0).
  split_prover_up.  
Qed.

Theorem split_splice'' : forall h x x0 x1 x2,
  h ~> x * x0
  -> x0 ~> x1 * x2
  -> h ~> (x * x1) * x2.
  split_prover_up.
Qed.

Theorem split_shuffle : forall h h1 h2 h3 h' h'' h''',
  h ~> h1 * (h2 * h3)
  -> h' ~> h'' * h2
  -> h'' ~> h3 * h'''
  -> h ~> (h1 * h3) * h2.
  split_prover'.

  destruct (h1 p); trivial.
  destruct (h2 p); trivial.

  destruct (h3 p); trivial.

  destruct (h2 p); trivial.
  destruct (h1 p); trivial.
  destruct (h3 p); trivial.

  destruct (h1 x); trivial.
  destruct (h2 x).
  destruct (h3 x); tauto.

  destruct (h3 x); trivial.
Qed.

Hint Resolve split_shuffle : Ynot.

Theorem split_comm' : forall h1 h2 h h',
  h ~> h1 * (h' * h2)
  -> (h1 * h2) ~> h2 * h1.
  split_prover'.

  destruct (h2 p); trivial.
  destruct (h1 p); trivial.
  destruct (h' p); trivial.

  destruct (h1 p); trivial.
  destruct (h2 p); trivial.
  destruct (h' p); trivial.

  destruct (h1 x).
  destruct (h2 x); trivial.
  destruct (h' x); tauto.
  destruct (h2 x); trivial.
Qed.

Hint Resolve split_comm' : Ynot.

Theorem split_comm : forall h h1 h2,
  h ~> h1 * h2
  -> h ~> h2 * h1.
  unfold split, disjoint; intuition; subst.
  unfold heap, join; ext_eq.
  generalize (H x); unfold read.
  destruct (h1 x); destruct (h2 x); tauto.
Qed.

Theorem split_self : forall h x x0 x1 x2,
  h ~> x * x0
  -> x ~> x1 * x2
  -> (x2 * x0) ~> x2 * x0.
  split_prover_up.
Qed.

Theorem split_self' : forall h x x0 x1 x2,
  h ~> x * x0
  -> x0 ~> x1 * x2
  -> (x * x1) ~> x * x1.
  split_prover_up.
Qed.

Theorem split_splice''' : forall h x x0 x1 x2,
  h ~> x * x0
  -> x0 ~> x1 * x2
  -> h ~> (x1 * x) * x2.
  split_prover_up.
Qed.

Theorem split_self'' : forall h x x0 x1 x2,
  h ~> x * x0
  -> x0 ~> x1 * x2
  -> (x1 * x) ~> x1 * x.
  split_prover_up.
Qed.

Theorem split_free : forall h h1 h2 p d,
  h ~> h1 * h2
  -> h1 # p = Some d
  -> (forall p' : ptr, (p' = p -> False) -> h1 # p' = None)
  -> (h ### p) ~> empty * h2.
  intros.

  replace (h ### p) with h2.
  auto with Ynot.
  unfold free, heap; ext_eq.
  destruct (ptr_eq_dec x p); subst.

  red in H; intuition.
  red in H2; intuition.
  generalize (H p).
  rewrite H0.
  unfold read.
  destruct (h2 p); tauto.

  red in H; intuition; subst.
  unfold join, read in *.
  rewrite (H1 _ n); trivial.
Qed.

Theorem pack_type_inv : forall (T : Type) (a : inhabited T),
  exists b, a = inhabits b.
  intros; case_eq a; intros t; exists t; auto.
Qed.

Hint Resolve split_free : Ynot.
