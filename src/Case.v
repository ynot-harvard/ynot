Require Import Separation.

Section ocase.
  Variables A B : Type.

  Variable disc : option A.

  Variable NoneCase : disc = None -> B.
  Variable SomeCase : forall v, disc = Some v -> B.

  Definition ocase :=
    match disc as disc' return (disc = disc' -> B) with
      | None => NoneCase
      | Some v => SomeCase _
    end (refl_equal _).
End ocase.

Implicit Arguments ocase [A B].

Notation "'IfNull' x 'Then' e1 'Else' e2" :=
  (ocase x (fun _ => e1) (fun x _ => e2))
  (no associativity, at level 90).
Notation "'IfNull' e 'As' x 'Then' e1 'Else' e2" :=
  (ocase e (fun _ => e1) (fun x _ => e2))
  (no associativity, at level 90).

Ltac simpl_IfNull :=
  repeat match goal with
           | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intro H; try (rewrite H in *; clear H)
           | [ H : ?p = None |- _ ] => rewrite H; mark_existential p
           | [ H : ?p = Some _ |- _ ] => rewrite H; mark_existential p
         end.

Section sbcase.
  Variables P Q:Prop.
  Variables B : Type.

  Variable disc : {P} + {Q}.

  Variable pCase : forall v, disc = left Q v -> B.
  Variable qCase : forall v, disc = right P v -> B.

  Definition sbcase :=
    match disc as disc' return (disc = disc' -> B) with
      | left v => @pCase v
      | right v => @qCase v
    end (refl_equal _).
End sbcase.

Implicit Arguments sbcase [P Q B].

Notation "'IfSB' x 'Then' e1 'Else' e2" :=
  (sbcase x (fun x _ => e1) (fun x _ => e2))
  (no associativity, at level 90).
Notation "'IfSB' e 'As' x 'Then' e1 'Else' e2" :=
  (sbcase e (fun x _ => e1) (fun x _ => e2))
  (no associativity, at level 90).
Section socase.
  Variable P:Type.
  Variable Q:Prop.
  Variable B : Type.

  Variable disc : P + {Q}.

  Variable pCase : forall v, disc = inleft Q v -> B.
  Variable qCase : forall v, disc = inright P v -> B.

  Definition socase :=
    match disc as disc' return (disc = disc' -> B) with
      | inleft v => @pCase v
      | inright v => @qCase v
    end (refl_equal _).
End socase.

Implicit Arguments socase [P Q B].

Notation "'IfSO' x 'Then' e1 'Else' e2" :=
  (socase x (fun x _ => e1) (fun x _ => e2))
  (no associativity, at level 90).
Notation "'IfSO' e 'As' x 'Then' e1 'Else' e2" :=
  (socase e (fun x _ => e1) (fun x _ => e2))
  (no associativity, at level 90).
