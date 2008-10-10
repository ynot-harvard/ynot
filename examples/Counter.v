Require Import Ynot.

Set Implicit Arguments.


Module Type COUNTER.
  Parameter t : Set.
  Parameter rep : t -> nat -> hprop.

  Parameter new : STsep __ (fun c => rep c 0).
  Parameter free : forall c n, STsep (n ~~ rep c n) (fun _ : unit => __)%hprop.
  Parameter get : forall c n, STsep (n ~~ rep c n) (fun n' => n ~~ rep c n * [n' = n])%hprop.
  Parameter inc : forall c n, STsep (n ~~ rep c n) (fun _ : unit => n ~~ rep c (S n))%hprop.
End COUNTER.

Module Counter : COUNTER.
  Definition t := ptr.
  Definition rep (p : t) (n : nat) := (p --> n)%hprop.

  Ltac t := unfold rep; sep idtac.

  Open Local Scope stsep_scope.

  Definition new : STsep __ (fun c => rep c 0).
    refine {{New 0}}; t.
  Qed.

  Definition free : forall c n, STsep (n ~~ rep c n) (fun _ : unit => __)%hprop.
    intros; refine {{Free c :@ _}}; t.
  Qed.

  Definition get : forall c n, STsep (n ~~ rep c n) (fun n' => n ~~ rep c n * [n' = n])%hprop.
    intros; refine {{c ! _}}; t.
  Qed.
  
  Definition inc : forall c n, STsep (n ~~ rep c n) (fun _ : unit => n ~~ rep c (S n))%hprop.
    intros; refine (
      n' <- c ! _;

      {{c ::= S n' <@> _}}
    ).

    t.

    simpl.
    intro.
    match goal with
      | [ |- ?P ==> _ ] => pose P
    end.
    pattern v in h.
    let x := eval cbv delta [h] in h in
      match x with
        | ?F _ =>
          match goal with
            | [ |- _ ==> ?Q v ] => equate Q F
          end
      end.
    t.

    t.
    t.
  Qed.
End Counter.
