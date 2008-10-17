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
