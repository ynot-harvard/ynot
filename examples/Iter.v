Require Import List.
Require Import Ynot.

Require Examples.Stack.
Module S := Examples.Stack.Stack.

Open Scope hprop_scope.
Open Scope stsepi_scope.

Set Implicit Arguments.

Definition iter (A : Set) (spec : list A -> hprop)
  (F : forall (x : A) (ls : list A), STsep (spec ls) (fun _ : unit => spec (x :: ls)))
  (ls : list A)
  : STsep (spec nil) (fun _ : unit => spec ls).
  do 3 intro.
  refine (fix self (ls : list A) : STsep (spec nil) (fun _ : unit => spec ls) :=
    match ls return STsep (spec nil) (fun _ : unit => spec ls) with
      | nil => {{Return tt}}
      | x :: ls' =>
        self ls';;
        F x ls'
    end); sep fail idtac.
Defined.

Open Scope inhabited_scope.

Definition stackFromList (A : Set) (ls : list A)
  : STsep __ (fun s : S.t A => S.rep s ls).
  intros; refine (s <- S.new _;
    iter (fun ls => S.rep s ls)
         (fun x ls => {{S.push s x [ls]}})
         ls;;
    {{Return s}}); sep fail idtac.
Qed.
