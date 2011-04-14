Require Import List Ascii. 
Require Import Ynot.
Require Import IO Net FS.
Require Import RSep.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Set Implicit Arguments.

Ltac rwpack X H := idtac;
  match X with 
    | [_]%inhabited => idtac
    | _ =>
      match goal with
        | [ H' : X = [_]%inhabited |- _ ] => rewrite -> H' in H
        | [ H' : [_]%inhabited = X |- _ ] => rewrite -> H' in H
      end
  end.

Module Type STATELESS_EXECPARAMS.

  Parameter ccorrect : forall (local remote : SockAddr), File (BoundSocketModel local remote) (R :: W :: nil) -> Trace -> Prop.

  Parameter io : forall (local remote : SockAddr) (fd : File (BoundSocketModel local remote) (R :: W :: nil)) (tr : [Trace]),
    STsep (tr ~~ traced tr * handle fd)
          (fun tr':[Trace] => tr ~~ tr' ~~ traced (tr' ++ tr) * [ccorrect fd tr']).

End STATELESS_EXECPARAMS.

Module Type STATE_EXECPARAMS.
  Parameter context : Type.
  Parameter cmodel : Set.
  Parameter rep : context -> cmodel -> hprop.
  Parameter inv : cmodel -> Prop.

  Parameter ccorrect : forall (local remote : SockAddr)
    (fd : File (BoundSocketModel local remote) (R :: W :: nil)) 
    (m m' : cmodel), Trace -> Prop.

  Parameter io : forall (local remote : SockAddr)
    (fd : File (BoundSocketModel local remote) (R :: W :: nil)) (tr : [Trace])
    (ctx : context) (m : [cmodel]),
    STsep (tr ~~ m ~~ traced tr * handle fd * rep ctx m * [inv m])
          (fun res':([Trace] * [cmodel]) => m ~~ tr ~~ 
            hprop_unpack (fst res') (fun tr' => 
              hprop_unpack (snd res') (fun m' =>
                traced (tr' ++ tr) * [ccorrect fd m m' tr'] * rep ctx m' * [inv m']))).

  Parameter init : 
    STsep (__)
          (fun cm:(context * [cmodel]) => hprop_unpack (snd cm) 
            (fun m => rep (fst cm) m * [inv m])).

End STATE_EXECPARAMS.

Module ADD_STATE(A : STATELESS_EXECPARAMS) : STATE_EXECPARAMS.

  Definition context := unit.
  Definition cmodel := unit.
  Definition rep (c:context) (m:cmodel) := __. 
  Definition inv (m:cmodel) := True.
  
  Definition ccorrect (local remote : SockAddr) (fd : File (BoundSocketModel local remote) (R :: W :: nil)) 
     (m m' : cmodel) (t : Trace) := A.ccorrect fd t.

  Definition io : forall (local remote : SockAddr)
    (fd : File (BoundSocketModel local remote) (R :: W :: nil)) (tr : [Trace])
    (ctx : context) (m : [cmodel]),
    STsep (tr ~~ m ~~ traced tr * handle fd * rep ctx m * [inv m])
          (fun res':([Trace] * [cmodel]) => m ~~ tr ~~ 
            hprop_unpack (fst res') (fun tr' => 
              hprop_unpack (snd res') (fun m' =>
                traced (tr' ++ tr) * [ccorrect fd m m' tr'] * rep ctx m' * [inv m']))).
    intros. refine (
      t <- A.io fd tr <@> _ (*m ~~ [inv m]*);
      {{ Return (t, [tt]%inhabited) }}).
    rsep fail auto.
    rsep fail auto.
    rsep fail auto.
    rsep fail auto. unfold rep. unfold ccorrect. rewrite H3 in H5. simpl in H5. rewrite (pack_injective H5). sep fail auto.
  Qed.

  Definition init : 
    STsep (__)
          (fun cm:(context * [cmodel]) => hprop_unpack (snd cm) 
            (fun m => rep (fst cm) m * [inv m])).
      refine {{Return (tt, [tt]%inhabited)}};
    solve [ unfold inv; sep fail auto ].
  Qed.

  Export A.

End ADD_STATE.


Module ExecModel(A : STATE_EXECPARAMS).
  Export A.

  Inductive correct (local: Net.SockAddr) : cmodel -> cmodel -> IO.Trace -> Prop :=
  | NilCorrect   : forall (m : cmodel), correct local m m nil
  | ConsCorrect  : forall remote aux past interim (fd : File (BoundSocketModel aux remote) (R :: W :: nil))
    (m m' m'' : cmodel), correct local m m' past -> ccorrect fd m' m'' interim 
    -> correct local m m'' (interim ++ TCP.Accept aux remote local :: past).

End ExecModel.

Lemma nil_cons_app : forall (A : Type) (l2 : list A) (a : A) (l1 : list A),
  (l1 ++ a :: nil) ++ l2 = l1 ++ a :: l2.
  induction l1; auto. simpl. rewrite IHl1. auto.
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

Module ExecImpl(A : STATE_EXECPARAMS).
  Module A := A.
  Module AL := ExecModel(A).
  Import AL.
  Import A.

  Definition iter (local: Net.SockAddr) (lsock : File (ListenSocketModel local) (R :: nil))
    (ctx : context) (m0 m : [cmodel]) (tr: [IO.Trace]) : 
    STsep (m0 ~~ m ~~ tr ~~ IO.traced tr * rep ctx m * [inv m] * [correct local m0 m tr]) 
          (fun r:([IO.Trace] * [cmodel]) => m0 ~~ tr ~~ 
            hprop_unpack (fst r) (fun tr' => 
              hprop_unpack (snd r) (fun m' => 
                [correct local m0 m' (tr' ++ tr)] * [tr' <> nil] * IO.traced (tr' ++ tr) * 
                rep ctx m' * [inv m']))).
    intros. refine (
      fd_lsa_rsa <- TCP.accept lsock tr <@> _;
      let lsa := fst (projT1 fd_lsa_rsa) in
      let rsa := snd (projT1 fd_lsa_rsa) in
      let fd  := projT2 fd_lsa_rsa in
      tm' <- A.io fd (tr ~~~ TCP.Accept lsa rsa local :: tr) ctx m <@> _ ;
      {{Return (inhabit_unpack (fst tm') (fun tr' => tr' ++ TCP.Accept lsa rsa local :: nil),
                snd tm')}}).
    solve [ rsep fail auto ].
    solve [ rsep fail auto ].
    rsep fail auto.
      assert (projT2 fd_lsa_rsa = fd); auto;
      assert (fst (projT1 fd_lsa_rsa) = lsa); auto;
      assert (snd (projT1 fd_lsa_rsa) = rsa); auto.
      rewrite <- H6. rewrite <- H7. rewrite <- H5. rsep fail auto.
    solve [ rsep fail auto ].
    solve [ rsep fail auto ].
    rsep fail auto. 
      repeat match goal with
               | [ H : v = _ , H' : fst v = [_]%inhabited |- _ ] => rewrite H in H'; simpl in H'; rewrite <- (pack_injective H'); clear H'
               | [ H : v = _ , H' : snd v = [_]%inhabited |- _ ] => rewrite H in H'; simpl in H'; rewrite <- (pack_injective H'); clear H'
             end.
      repeat rewrite nil_cons_app.
      assert (correct local x x4 (x3 ++ TCP.Accept lsa rsa local :: x1));
        [ eapply ConsCorrect; eassumption | ].
      assert (x3 ++ TCP.Accept lsa rsa local :: nil <> nil);
        [ unfold not; intro H10'; destruct x3; inversion H10' | ];
      sep fail auto.
  Qed.

  Definition main : forall (local: Net.SockAddr),
    STsep (traced nil)
          (fun _:unit => Exists t :@ Trace, traced t).
    refine (fun local =>
      (** Open a listen socket **)
      lsock <- TCP.listenSocket local <@> _;

      (** Initialize the state **)
      cm <- A.init <@> _;

      (** forever **)
      xxx <- @IO.foreverInv _ cm
              (fun ctx t => 
                hprop_unpack (snd ctx) (fun m => 
                  hprop_unpack (snd cm) (fun m0 => 
                    [correct local m0 m t] * [inv m] * rep (fst ctx) m)))
              (fun ctx t => 
                x <- iter lsock (fst ctx) (snd cm) (snd ctx) t;
                {{Return ((fst ctx, snd x), fst x)}})
              [nil] <@> _;
      close lsock;;
            
      {{Return tt}}).
    solve [ rsep fail auto ].
    solve [ rsep fail auto ].
    solve [ rsep fail auto ].
    solve [ rsep fail auto ].
    solve [ rsep fail auto ].
    solve [ rsep fail auto ].
    solve [ rsep fail auto ].
    solve [ sep fail auto ].
    solve [ inhabiter; unpack_conc; sep fail ltac:(auto; try constructor) ].
    solve [ instantiate (1:= (fun _ => [False])); sep fail auto ].
    solve [ sep fail auto ].
    solve [ instantiate (1:=[False]); sep fail auto ].
    solve [ instantiate (1:=[False]); sep fail auto ].
    solve [ sep fail auto ].
  Qed.

End ExecImpl.
