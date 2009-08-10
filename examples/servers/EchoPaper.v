
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

Require Import List.
Require Import IO.
Require Import FS.
Require Import Net.

(*
Definition Sent := axiom_UDP_Sent.
Definition Recd := axiom_UDP_Recd.
*)
Export UDP.

Inductive echoes (local: SockAddr) : Trace -> Prop :=
 | NilEchoes : echoes local nil
 | ConsEchoes : forall remote s past, echoes local past -> 
    echoes local (Sent local remote s :: Recd local remote s :: past).

Definition echo_iter_t local := forall (tr: [Trace]), 
 STsep (tr ~~ traced tr * [echoes local tr])
       (fun _:unit => tr ~~ Exists r :@ Trace, 
          traced (r ++ tr) * [echoes local (r ++ tr)]).
(*
Definition recv := axiom_UDP_recv.
Definition send := axiom_UDP_send.
*)

Require Import RSep.


Lemma f : forall T (a b : T) (c: list T), (a :: (b :: c)) = (a :: b :: nil) ++ c.
 sep fail auto.
Qed.

Lemma lm1 : forall local x tr, 
 (tr ~~ traced (Sent local (fst x) (snd x) :: Recd local (fst x) (snd x) :: tr) * [echoes local tr]) ==>
  (tr ~~ (Exists r :@ Trace, traced (r ++ tr) * [echoes local (r ++ tr)])).
 sep fail auto.  instantiate (2:= (Sent local a b) :: ((Recd local a b) :: nil)).
 sep fail auto. pose (ConsEchoes local a b x0 H). sep fail auto.
Qed.

Lemma lm : forall local x0 x,
   traced (Sent local (fst x) (snd x) :: Recd local (fst x) (snd x) :: x0) * [echoes local x0] ==>
   (Exists r :@ Trace, traced (r ++ x0) * [echoes local (r ++ x0)]) .
 sep fail auto.  instantiate (2:= (Sent local a b) :: ((Recd local a b) :: nil)).
 sep fail auto. pose (ConsEchoes local a b x0 H). sep fail auto.
Qed.

Definition echo (local: SockAddr) : echo_iter_t local.
  unfold echo_iter_t; intros; refine (
    x <- recv local tr <@> _  ;
    {{ send local (fst x) (snd x)  (tr ~~~ (Recd  local (fst x) (snd x) :: tr)) <@> _ }} );
  rsep fail auto. apply lm.
Qed.

