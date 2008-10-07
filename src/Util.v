Set Implicit Arguments.


Theorem push_and_ex : forall P T (P' : T -> Prop),
  (exists x, P /\ P' x)
  -> P /\ ex P'.
  firstorder.
Qed.


Ltac not_eq e1 e2 :=
  match e1 with
    | e2 => fail 1
    | _ => idtac
  end.
Ltac equate e1 e2 := not_eq e1 e2; let H := fresh in assert (H : e1 = e2); [reflexivity | clear H].


Notation "[ T ]" := (inhabited T) (at level 0, T at level 99) : type_scope.
Notation "[ v ]" := (inhabits v) (at level 0, v at level 99) : inhabited_scope.
Bind Scope inhabited_scope with inhabited.
Delimit Scope inhabited_scope with inhabited.


Ltac hdestruct x := let y := fresh in (dependent inversion x as [y]; clear x; rename y into x; destruct x).
