
Require Import Ynot.

Open Scope hprop_scope.
Open Scope stsepi_scope.

Definition T := ptr.
Definition M := nat.
Definition rep t (m: M) := t --> m.
Definition inc t m : STsep (m ~~ rep t m) 
 (fun _:unit => m ~~ rep t (m + 1)).
  intros. refine (
    x <- ! t ;
    {{ t ::= x + 1 }} ); 
 unfold rep; sep fail auto.
Qed.

Require Import List String.
Require Import IO FS Net.
Require Import Basis.

Export UDP.

Inductive echoes (local: SockAddr) : nat -> Trace -> Prop :=
 | NilEchoes : echoes local 0 nil
 | ConsEchoes : forall remote s past n str, echoes local n past ->
   str = (str2la (ntos n ++ " : ") ++ s) ->
   echoes local (S n) (Sent local remote str :: Recd local remote s :: past).

Require Import Data.Counter.

Definition echo_iter_t local (cnt : Counter.t) (i : [nat]) := forall (tr: [Trace]),
 STsep (i ~~ tr ~~ traced tr * [echoes local i tr] * Counter.rep cnt i)
       (fun _:unit => i ~~ tr ~~ Exists r :@ Trace, Counter.rep cnt (S i) *
          traced (r ++ tr) * [echoes local (S i) (r ++ tr)]).

Require Import RSep.

Lemma f : forall T (a b : T) (c: list T), (a :: (b :: c)) = (a :: b :: nil) ++ c.
 sep fail auto.
Qed.

Lemma traced_app : forall a b c P Q,
  P ==> Q ->
  traced (a :: b :: c) * P ==> traced ((a :: b :: nil) ++ c) * Q.
Proof. sep fail auto. Qed.

Ltac simplr := 
  search_prem ltac:(search_conc ltac:(simple eapply traced_app)).


Definition echo : forall (local: SockAddr) (cnt : Counter.t) (i : [nat]), echo_iter_t local cnt i.
  unfold echo_iter_t; refine (fun local cnt i tr =>
    x <- recv local tr <@> _  ;
    n <- Counter.get cnt i <@> _ ;
    Counter.inc cnt i <@> _ ;;
    {{ send local (fst x) ((str2la (ntos n ++ " : ")%string) ++ snd x)
          (tr ~~~ (Recd  local (fst x) (snd x) :: tr)) <@> _ }});
  rsep fail auto. sep fail auto; simplr. simpl; cut_pure; constructor; eauto.
Qed.

