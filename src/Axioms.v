Require Import Eqdep.

Set Implicit Arguments.


(** * Extensional equality of functions *)

Axiom ext_eq : forall T1 T2 (f1 f2 : T1 -> T2),
  (forall x, f1 x = f2 x) -> f1 = f2.

Theorem ext_eqS : forall (T1 T2 : Set) (f1 f2 : T1 -> T2),
  (forall x, f1 x = f2 x) -> f1 = f2.
  intros; rewrite (ext_eq f1 f2); auto.
Qed.

Ltac ext_eq := (apply ext_eq || apply ext_eqS); intro.


(** * Hidden values *)

Axiom pack_injective : forall T (x y : T),
  inhabits x = inhabits y
  -> x = y.


(** * Dynamic packages *)

Inductive dynamic : Type :=
  | Dyn : forall T, T -> dynamic.

Theorem Dyn_inj : forall T (x y : T),
  Dyn x = Dyn y
  -> x = y.
  injection 1; intro.
  exact (inj_pair2 _ _ _ _ _ H0).
Qed.
