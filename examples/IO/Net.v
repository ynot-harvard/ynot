Require Import Ynot.
Require Import IO FS.
Require Import List Ascii.

Set Implicit Arguments.

Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.

(** Socket Address **)
Axiom axiom_SockAddr : Set.
Definition SockAddr := axiom_SockAddr.
Definition SockAddrModel := unit.

(** constructor for socket addresses **)
Axiom axiom_sockaddr : forall (n1 n2 n3 n4 : sig (fun x : nat => x <= 255))
  (port : nat),
  STsep (__)
        (fun r : SockAddr => hprop_empty).
Definition sockaddr := axiom_sockaddr.
Definition sockaddr_model :  forall (n1 n2 n3 n4 : sig (fun x : nat => x <= 255))
  (port : nat),
  STsep (__)
        (fun r : SockAddrModel => hprop_empty).
Proof.
 intros. refine {{ Return tt }}; sep fail auto.
Qed.

Axiom axiom_sock_eq : forall (sa1 sa2 : SockAddr), {sa1 = sa2} + {sa1 <> sa2}.
Definition sock_eq := axiom_sock_eq.
Definition sock_eq_model : forall (sa1 sa2 : SockAddrModel), {sa1 = sa1} + {sa1 <> sa2}.
Proof.
 intros. left. trivial.
Qed.

(** UDP Sockets **)
Axiom axiom_UDP_Sent : SockAddr -> SockAddr -> list ascii -> Action.
Definition UDP_Sent_Model (x y: SockAddrModel) (z: list ascii) : Action_model := tt.

Axiom axiom_UDP_Recd : SockAddr -> SockAddr -> list ascii -> Action.
Definition UDP_Recd_Model (x y: SockAddrModel) (z: list ascii) : Action_model := tt.

Axiom axiom_UDP_send : forall (local remote: SockAddr) (s: list ascii) (tr: [Trace]),
  STsep (tr ~~ traced tr)
        (fun r:unit => tr ~~ traced (axiom_UDP_Sent local remote s :: tr)).   

Definition UDP_send_Model (local remote: SockAddrModel) (s: list ascii) (tr: [TraceModel]) :
  STsep (tr ~~ traced_model tr)
        (fun r:unit => tr ~~ traced_model (UDP_Sent_Model local remote s :: tr)).
Proof.
 intros. refine {{ Return tt }}; sep fail auto.
Qed.

Axiom axiom_UDP_recv : forall (local: SockAddr) (tr: [Trace]),
  STsep (tr ~~ traced tr) 
        (fun r => tr ~~  traced (axiom_UDP_Recd local (fst r) (snd r) :: tr)).
Definition UDP_recv_model (local: SockAddrModel) (tr: [TraceModel]) :
  STsep (tr ~~ traced_model tr)
        (fun r => tr ~~ traced_model (UDP_Recd_Model local (fst r) (snd r) :: tr)).
Proof.
 intros. refine {{ Return (tt,nil) }}; sep fail auto.
Qed.

Module UDP.

  Definition Sent := axiom_UDP_Sent.
  Definition Recd := axiom_UDP_Recd.

  Definition send : forall (local remote: SockAddr) (s: list ascii) (tr: [Trace]),
    STsep (tr ~~ traced tr)
          (fun r:unit => tr ~~ traced (Sent local remote s :: tr)) :=
    axiom_UDP_send.  
  Definition recv : forall (local: SockAddr) (tr: [Trace]),
    STsep (tr ~~ traced tr) 
          (fun r => tr ~~  traced (Recd local (fst r) (snd r) :: tr)) :=
    axiom_UDP_recv.

End UDP.

(** TCP Sockets **)
Axiom axiom_BoundSocketModel : SockAddr -> SockAddr -> fd_model.
Definition BoundSocketModel := axiom_BoundSocketModel.
Axiom axiom_ListenSocketModel : SockAddr -> fd_model.
Definition ListenSocketModel := axiom_ListenSocketModel.

Axiom axiom_TCP_Accept : SockAddr -> SockAddr -> SockAddr -> Action.

Axiom axiom_TCP_listenSocket : forall (skt : SockAddr),
  STsep (__)
        (fun fd:(File (ListenSocketModel skt) (R :: nil)) => handle fd).

Definition rt := sigT (fun x:(SockAddr * SockAddr) => (File (BoundSocketModel (fst x) (snd x)) (R :: W :: nil))).

Axiom axiom_TCP_bindSocket : forall (local remote : SockAddr),
  STsep (__)
        (fun fd:File (BoundSocketModel local remote) (R :: W :: nil) => handle fd).

Axiom axiom_TCP_accept : forall (skt : SockAddr) (fd : File (ListenSocketModel skt) (R :: nil))
  (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun r:rt => tr ~~ handle (projT2 r) *
            traced (axiom_TCP_Accept (fst (projT1 r)) (snd (projT1 r)) skt :: tr)).

Module TCP.

  Definition Accept := axiom_TCP_Accept.

  Definition listenSocket := axiom_TCP_listenSocket.
  Definition bindSocket := axiom_TCP_bindSocket.
  Definition accept : forall (skt : SockAddr) 
    (fd : File (ListenSocketModel skt) (R :: nil)) (tr : [Trace]),
    STsep (tr ~~ traced tr)
          (fun r:rt => tr ~~ handle (projT2 r) *
              traced (Accept (fst (projT1 r)) (snd (projT1 r)) skt :: tr)) :=
      axiom_TCP_accept.

End TCP.

(** SSL Sockets **)
Axiom axiom_SslListenSocketModel : SockAddr -> fd_model.
Definition SslListenSocketModel := axiom_SslListenSocketModel.

Axiom axiom_SSL_secure : forall (m : fd_model) (ms : list mode), File m ms -> Prop.
Definition secure := axiom_SSL_secure.

Axiom axiom_SSL_listenSocket : forall (skt : SockAddr),
  STsep (__)
        (fun fd:(File (SslListenSocketModel skt) (R :: nil)) => handle fd * [secure fd]).

Axiom axiom_SSL_bindSocket : forall (local remote : SockAddr),
  STsep (__)
        (fun fd:File (BoundSocketModel local remote) (R :: W :: nil) => handle fd * [secure fd]).

Axiom axiom_SSL_accept : forall (skt : SockAddr) (fd : File (SslListenSocketModel skt) (R :: nil))
  (tr : [Trace]),
  STsep (tr ~~ traced tr * [secure fd])
        (fun r:rt => tr ~~ handle (projT2 r) * [secure fd] * [secure (projT2 r)] *
            traced (axiom_TCP_Accept (fst (projT1 r)) (snd (projT1 r)) skt :: tr)).

Module SSL.

  Definition listenSocket := axiom_SSL_listenSocket.
  Definition bindSocket := axiom_SSL_bindSocket.
  Definition accept : forall (skt : SockAddr) 
    (fd : File (SslListenSocketModel skt) (R :: nil)) (tr : [Trace]),
    STsep (tr ~~ traced tr * [secure fd])
          (fun r:rt => tr ~~ handle (projT2 r) * [secure fd] * [secure (projT2 r)] *
              traced (TCP.Accept (fst (projT1 r)) (snd (projT1 r)) skt :: tr)) :=
      axiom_SSL_accept.

End SSL.
