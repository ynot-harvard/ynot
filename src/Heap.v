Require Import Arith.

Require Import Ynot.Axioms.

Set Implicit Arguments.


Definition heap := nat -> option dynamic.
Definition ptr := nat.

Definition empty : heap := fun _ => None.
Definition singleton (p : ptr) (v : dynamic) : heap :=
  fun p' => if eq_nat_dec p' p then Some v else None.
Definition read (h : heap) (p : ptr) : option dynamic := h p.
Definition write (h : heap) (p : ptr) (v : dynamic) : heap :=
  fun p' => if eq_nat_dec p' p then Some v else h p'.
Definition free (h : heap) (p : ptr) : heap :=
  fun p' => if eq_nat_dec p' p then None else h p'.

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
  destruct (eq_nat_dec p p); tauto.
Qed.

Theorem read_singleton_diff : forall p d p',
  p' <> p
  -> (p --> d) # p' = None.
  unfold read, singleton; intros.
  destruct (eq_nat_dec p' p); tauto.
Qed.

Theorem read_write_same : forall h p d,
  (h ## p <- d) # p = Some d.
  unfold read, write; intros.
  destruct (eq_nat_dec p p); tauto.
Qed.

Theorem read_write_diff : forall h p d p',
  p' <> p
  -> (h ## p <- d) # p' = h # p'.
  unfold read, write; intros.
  destruct (eq_nat_dec p' p); tauto.
Qed.

Hint Rewrite read_empty read_singleton_same read_write_same : Ynot.
Hint Rewrite read_singleton_diff read_write_diff using (auto; fail) : Ynot.

Hint Extern 1 (_ # _ = _) => autorewrite with Ynot in * : Ynot.
