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

  Ltac t := unfold rep; sep simpl.

  Open Scope stsepi_scope.

  Definition new : STsep __ (fun c => rep c 0).
    refine {{New 0}}; t.
  Qed.

  Definition free : forall c n, STsep (n ~~ rep c n) (fun _ : unit => __)%hprop.
    intros; refine {{Free c}}; t.
  Qed.

  Definition get : forall c n, STsep (n ~~ rep c n) (fun n' => n ~~ rep c n * [n' = n])%hprop.
    intros; refine {{!c}}; t.
  Qed.
  
  Definition inc : forall c n, STsep (n ~~ rep c n) (fun _ : unit => n ~~ rep c (S n))%hprop.
    intros; refine (
      n' <- !c;

      {{c ::= S n'}}
    ); t.
  Qed.
End Counter.
