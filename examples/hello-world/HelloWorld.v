Require Import Ynot.
Require Import Basis.
Require Import String.

Open Local Scope string_scope.
Open Local Scope stsepi_scope.

Definition main : STsep (__) (fun _:unit => hprop_empty).
   refine (printStringLn "Hello World");
   sep fail auto.
Qed.
