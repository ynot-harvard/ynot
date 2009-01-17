Require Import Ynot.STsep.
Require Import Ynot.Hprop.

Require Import String.
Require Import List.

Open Local Scope hprop_scope.

Axiom printString : forall (s : string),
  STsep (__) (fun _:unit => __).

Axiom printStringLn : forall (s : string),
  STsep (__) (fun _:unit => __).

Axiom printString' : forall (s : list Ascii.ascii),
  STsep (__) (fun _:unit => __).

Axiom printStringLn' : forall (s : list Ascii.ascii),
  STsep (__) (fun _:unit => __).
