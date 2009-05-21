Require Import List.
Require Import Ascii.
Require Import Ynot.
Require Import IO FS Net.
Require Import UdpServer TcpServer SslServer.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Set Implicit Arguments.

Opaque ReadLine.
Opaque ReadString.
Opaque WroteString.

Module UdpEchoServer : UdpServer.EXECPARAMS.
  
  Inductive ccorrect' (req : list ascii) : Trace -> Prop :=
  | NilCorrect : ccorrect' req nil.
  Definition ccorrect := ccorrect'.
  
  Inductive reply' (a b : list ascii): Prop :=
  | ReplyIdentity : reply' a b.
  Definition reply := reply'.

  Definition io : forall (req : list ascii) (tr : [Trace]),
    STsep (tr ~~ traced tr)
          (fun r:(list ascii * [Trace])=> tr ~~ tr' :~~ (snd r) in traced (tr' ++ tr) * [reply req (fst r)] * [ccorrect req tr']).
    intros. refine ( {{Return (req, [nil]%inhabited)}} ).
    solve [ sep fail auto ].
    solve [ unfold ccorrect, reply; intros; simpl; inhabiter; unpack_conc; intro_pure; subst; sep fail auto ].
  Qed.
End UdpEchoServer.

Module udpmes := UdpServer.ExecImpl UdpEchoServer.

Definition udp := udpmes.main.

Module TcpEchoServer : TcpServer.STATELESS_EXECPARAMS.

  Inductive ccorrect' (local remote : SockAddr) (fd : File (BoundSocketModel local remote) (R :: W :: nil)) : Trace -> Prop :=
  | DoneCorrect : forall past, ecorrect fd past -> ccorrect' fd (Flush fd :: ReadLine fd nil ++ past)
  with ecorrect (local remote : SockAddr) (fd : File (BoundSocketModel local remote) (R :: W :: nil)) : Trace -> Prop :=
  | NilCorrect : ecorrect fd nil
  | ConsCorrect : forall s past, s <> nil -> ecorrect fd past ->
    ecorrect fd (Flush fd :: WroteString fd s ++ ReadLine fd s ++ past).
  Definition ccorrect := ccorrect'.

  Definition traceCombine (t1 t2 : [Trace]) := inhabit_unpack2 t1 t2 (fun t1 t2 => t1 ++ t2).
  Definition traceAfter (t1 t2 : [Trace]) (f : Trace -> Trace) := inhabit_unpack2 t1 t2 (fun t1 t2 => f (t1 ++ t2)).

  Definition empty_eq : forall T (a : list T), {a = nil} + {a <> nil}.
    intros; destruct a; firstorder.
  Qed.

  Ltac rcombine := idtac;
    match goal with
      | [ H : traceCombine ?X ?Y = [_]%inhabited |- _ ] =>
        rwpack X H; rwpack Y H; simpl in H; rewrite <- (pack_injective H) in *; clear H
      | [ H : traceAfter ?X ?Y _ = [_]%inhabited |- _ ] =>
        rwpack X H; rwpack Y H; simpl in H; rewrite <- (pack_injective H) in *; clear H
      | [ H : (inhabit_unpack ?X _) = [_]%inhabited |- _ ] =>
        rwpack X H; simpl in H; rewrite <- (pack_injective H)
    end.

  Definition io : forall (local remote : SockAddr) (fd : File (BoundSocketModel local remote) (R :: W :: nil)) (tr : [Trace]),
    STsep (tr ~~ traced tr * handle fd)
          (fun tr':[Trace] => tr ~~ tr' ~~ traced (tr' ++ tr) * [ccorrect fd tr']).
    intros. refine (
      lt <- Fix (fun tr' => tr ~~ tr' ~~ traced (tr' ++ tr) * [ecorrect fd tr'] * handle fd)
                (fun _ tr' => tr ~~ tr' ~~ traced (tr' ++ tr) * [ccorrect fd tr'])
                (fun self tr' => 
                  str <- readline fd rw_readable (traceCombine tr' tr) <@> (tr' ~~ [ecorrect fd tr']);
                  if empty_eq str then
                    flush fd (traceAfter tr' tr (fun t => ReadLine fd str ++ t)) rw_writeable <@> _ ;;
                    close fd <@> _ ;;
                    {{Return (tr' ~~~ Flush fd :: ReadLine fd str ++ tr')}}
                  else
                    writeline fd str rw_writeable (traceAfter tr' tr (fun t => ReadLine fd str ++ t)) <@> _;;
                    flush fd (traceAfter tr' tr (fun t => WroteString fd str ++ ReadLine fd str ++ t)) rw_writeable <@> _;;
                    {{self (tr' ~~~ Flush fd :: WroteString fd str ++ ReadLine fd str ++ tr')}})
                [nil]%inhabited <@> _ ;
      {{Return lt}}); try unfold ccorrect.
    sep fail auto.
    sep fail auto.
    cbv beta; inhabiter; unpack_conc. repeat rcombine; canceler; sep fail auto.
    sep fail auto.
    inhabiter; unpack_conc. repeat rcombine. canceler; sep fail auto.
    sep fail auto.
    sep fail auto.
    intros. inhabiter; unpack_conc. repeat rcombine. sep fail ltac:(auto; try constructor).
    solve [ cbv beta; inhabiter; unpack_conc; repeat rcombine; canceler; sep fail auto ].
    sep fail auto.
    inhabiter; unpack_conc. repeat rcombine. canceler. sep fail auto.
    sep fail auto.
    inhabiter; unpack_conc. repeat rcombine. canceler. intro_pure.
    assert (ecorrect fd (Flush fd :: WroteString fd str ++ ReadLine fd str ++ x)).
     constructor; auto.
    assert (Flush fd :: WroteString fd str ++ ReadLine fd str ++ x ++ x0 = (Flush fd :: WroteString fd str ++ ReadLine fd str ++ x) ++ x0).
     simpl. repeat rewrite app_ass. auto. rewrite H4. sep fail auto.

    sep fail auto.
    intros; inhabiter; unpack_conc. rewrite <- (pack_injective H0). simpl. sep fail ltac:(try constructor).
    sep fail auto.
    sep fail auto.
    sep fail auto.    
  Qed.
End TcpEchoServer.

Module mes' := TcpServer.ADD_STATE(TcpEchoServer).
Module mes := TcpServer.ExecImpl(mes').

Definition tcp := mes.main.

Module smes' := SslServer.ADD_STATE(TcpEchoServer).
Module smes := SslServer.ExecImpl(smes').

Definition ssl := smes.main.