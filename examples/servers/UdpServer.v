Require Import List Ascii. 
Require Import Ynot.
Require Import IO Net.

(* todo what does Warning: Trying to mask the absolute name "IO" mean *)

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

Ltac rcombine := idtac;
  match goal with
    | [ H : (inhabit_unpack ?X _) = [_]%inhabited |- _ ] =>
      rwpack X H; simpl in H; rewrite <- (pack_injective H)
    | [ H : (inhabit_unpack2 ?X ?Y _) = [_]%inhabited |- _ ] =>
      rwpack X H; rwpack Y H; simpl in H; rewrite <- (pack_injective H)
  end.

Module Type EXECPARAMS.

  Parameter ccorrect : forall (req : list ascii), Trace -> Prop.
  Parameter reply : list ascii -> list ascii -> Prop.

  Parameter io : forall (req : list ascii) (tr : [Trace]),
    STsep (tr ~~ traced tr)
          (fun r:(list ascii * [Trace])=> tr ~~ tr' :~~ (snd r) in traced (tr' ++ tr) * [reply req (fst r)] * [ccorrect req tr']).

End EXECPARAMS.

Module ExecModel(A : EXECPARAMS).
  Export A.

  (* This correctness criteria says that we respond
     to correct requests *)
  Inductive correct (local: Net.SockAddr) : IO.Trace -> Prop :=
  | NilCorrect   : correct local nil
  | ConsCorrect  : forall remote past interim req resp, reply req resp -> correct local past ->
    ccorrect req interim -> correct local (UDP.Sent local remote resp :: interim ++ UDP.Recd local remote req :: past).

  (* A type for an exec server loop. *)
  Definition exec_server_t local := IO.server_t (correct local) (NilCorrect local).

End ExecModel.

Lemma nil_cons_app : forall (A : Type) (l2 : list A) (a : A) (l1 : list A),
  (l1 ++ a :: nil) ++ l2 = l1 ++ a :: l2.
  induction l1; auto. simpl. rewrite IHl1. auto.
Qed.

Module ExecImpl(A : EXECPARAMS).
  Module A := A.
  Module AL := ExecModel(A).
  Import AL.
  Import A.

  Definition iter : forall (local: Net.SockAddr) (tr: [IO.Trace]),
    STsep (tr ~~ IO.traced tr * [correct local tr]) 
          (fun r:[IO.Trace] => tr ~~ r ~~ [correct local (r ++ tr)] * [r <> nil] * IO.traced (r ++ tr)).
(**
            Exists remote :@ Net.SockAddr, Exists s :@ list ascii, Exists rp :@ list ascii, Exists it :@ Trace, [reply s rp] *
            [r = Net.UDP.Sent local remote rp :: it ++ Net.UDP.Recd local remote s :: nil] * IO.traced (r ++ tr)).
**)
  refine (fun local tr =>
    x <- Net.UDP.recv local tr <@> _;
    rtr <- io (snd x) (tr ~~~ UDP.Recd local (fst x) (snd x) :: tr) <@> _;
    UDP.send local (fst x) (fst rtr)
        (inhabit_unpack2 tr (snd rtr) (fun tr it => it ++ UDP.Recd local (fst x) (snd x) :: tr)) <@> _;;
    {{Return (inhabit_unpack (snd rtr) (fun it => UDP.Sent local (fst x) (fst rtr) :: it ++ UDP.Recd local (fst x) (snd x) :: nil))}}).
  solve [ inhabiter; unpack_conc; canceler; sep fail auto ].
  solve [ sep fail auto ].
  solve [ inhabiter; unpack_conc; repeat rcombine; canceler; sep fail auto ].
  solve [ sep fail auto ].
  inhabiter; unpack_conc; destruct (pack_type_inv (snd rtr)); repeat rcombine. simpl. rewrite H2. inhabiter. rewrite <- (pack_injective H3). canceler. sep fail auto.
  solve [ sep fail auto ].
  solve [ sep fail auto ].
  intros; inhabiter; unpack_conc. destruct (pack_type_inv (snd rtr)). rewrite H3. simpl. intro_pure. rewrite H4 in H. repeat rcombine. rewrite <- (pack_injective H).
    simpl. rewrite nil_cons_app. canceler.
    sep fail ltac:(auto; try constructor; auto; try discriminate).
Qed.

Definition main : forall (local: Net.SockAddr),
  STsep (traced nil)
        (fun _:unit => Exists t :@ Trace, traced t).
  refine (fun local => 
    xxx <- IO.forever
             (fun t => [correct local t])
             (fun t => {{ iter local t }})
             [nil];
   {{Return tt}});
  sep fail ltac:(auto; try constructor).
Qed.

End ExecImpl.
