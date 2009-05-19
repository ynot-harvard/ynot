Require Import List Ascii.
Require Import Ynot.
Require Import IO Net FS.
Require Import RSep.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.
Open Local Scope char_scope.

Set Implicit Arguments.

Inductive trace (local remote : Net.SockAddr)
  (fd : File (BoundSocketModel local remote) (R :: W :: nil)) : IO.Trace -> Prop :=
| NilCorrect : trace fd nil
| ConsCorrect : forall request reply past, trace fd past -> secure fd ->
  trace fd  
      (WroteString stdout reply ++ ReadLine fd reply ++ 
        Flush fd :: WroteString fd request ++ ReadLine FS.stdin request ++ past).

Lemma proj_inv : forall (T1 T2 : Type) (a b : T1) (c d : T2),
  (a,c) = (b,d) -> a = b /\ c = d.
  intros; inversion H; auto.
Qed.

Definition iter_post (local remote : Net.SockAddr) (req rep : list ascii)
  (fd : File (BoundSocketModel local remote) (R :: W :: nil)) (tr : Trace) :=
  WroteString stdout rep ++ ReadLine fd rep ++ Flush fd :: WroteString fd req ++ ReadLine stdin req ++ tr.

Definition iter : forall (local remote : Net.SockAddr)
  (fd : File (BoundSocketModel local remote) (R :: W :: nil)) (tr : [Trace]),
  STsep (tr ~~ IO.traced tr * [secure fd])
        (fun _:unit => tr ~~ Exists req :@ list ascii, Exists rep :@ list ascii,
          traced (iter_post req rep fd tr) * [secure fd]).
  intros. refine (
    ln <- readline FS.stdin FS.ro_readable tr <@> _ ;
    writeline fd ln rw_writeable (tr ~~~ ReadLine stdin ln ++ tr) <@> _ ;;
    flush fd (tr ~~~ WroteString fd ln ++ ReadLine stdin ln ++ tr) rw_writeable <@> _;;
    reply <- readline fd rw_readable (tr ~~~ Flush fd :: WroteString fd ln ++ ReadLine stdin ln ++ tr) <@> _ ;
    writeline FS.stdout reply FS.wo_writeable (tr ~~~ ReadLine fd reply ++ Flush fd :: WroteString fd ln ++ ReadLine stdin ln ++ tr) <@> _;;
    {{Return tt}});
  rsep fail auto. canceler. sep fail auto. sep fail auto.
  instantiate (1:=reply). instantiate (1:=ln). unfold iter_post. sep fail auto.
Qed.

Theorem list_no_cycle : forall (T : Type) (l1 l2 : list T),
  l2 <> nil -> l1 <> l2 ++ l1.
  induction l1. 
    auto.
    intros. rewrite <- app_nil_end. auto.
    intros. destruct l2. congruence. unfold not in *. intros. inversion H0.
    rewrite <- nil_cons_app in H3. eapply IHl1. instantiate (1 := (l2 ++ t :: nil)). intros. destruct l2; discriminate.
     auto.
Qed.

Theorem list_no_cycle' : forall (T : Type) (l1 l2 : list T),
  l2 <> nil -> l2 ++ l1 <> l1.
  intros; pose (@list_no_cycle T l1 l2); unfold not in *; auto.
Qed.

Lemma list_fix : forall T (x y z : list T) a,
  (a :: x ++ y) ++ z = a :: x ++ y ++ z.
  intros. simpl. rewrite app_ass. auto.
Qed.

Definition client : forall (local remote : Net.SockAddr) (tr : [Trace]),
  STsep (tr ~~ IO.traced nil)
        (fun _:unit => tr ~~ Exists v :@ Trace, IO.traced v).
  intros. refine (
    skt <- SSL.bindSocket local remote <@> _ ;

    xxx <- IO.forever 
             (fun t:Trace => [trace skt t] * handle skt * [secure skt])
             (fun t:[Trace] => 
               {{iter skt t <@> _}})
             [nil] ;
    close skt;;
    {{Return tt}}); try unfold iter_post.
  solve [ rsep fail auto ].
  solve [ rsep fail auto ].
  solve [ intros; inhabiter; unpack_conc; canceler; sep fail auto ]. (** rsep doesn't have good enough support for re-packing **)
  solve [ sep fail auto;
  instantiate (1 := WroteString stdout v1 ++
    ReadLine skt v1 ++ Flush skt :: WroteString skt v0 ++ ReadLine stdin v0);
    repeat rewrite app_ass; rewrite list_fix; canceler;  sep fail ltac:(econstructor; auto) ].
  solve [ rsep fail ltac:(auto; econstructor) ].
  solve [ rsep fail auto ].
  solve [ destruct xxx ].
  solve [ rsep fail auto ].
  solve [ rsep fail auto ].
  solve [ destruct xxx ].
Qed.