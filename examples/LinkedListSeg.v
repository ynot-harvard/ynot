Require Import Ynot.
Require Import List.

Set Implicit Arguments.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Section LINKED_LIST_SEG.
Variable A : Set.

Parameter ptr_eq  : forall (p q : ptr), {p = q} + {p <> q}.
Parameter ptr_eq' : forall (p q : option ptr), {p = q} + {p <> q}.
Parameter nat_eq  : forall (p q : nat), {p = q} + {p <> q}.
  
(******************************************************************************)
(** Representation                                                           **)
(******************************************************************************)

(** LLSeg : pointer to a node or none **)
Definition LinkedList : Set := option ptr.

Record Node : Set := node {
  data: A;
  next: LinkedList
}.

Definition head (ls : list A) :=
  match ls with
    | nil => None
    | x :: _ => Some x
  end.

Definition tail (ls : list A) :=
  match ls with
    | nil => nil
    | _ :: ls' => ls'
  end.

Fixpoint llseg (s : LinkedList) (e : LinkedList) (m : list A) {struct m} : hprop :=
  match m with 
    | nil => [s = e]
    | v :: r => [s <> e] * match s with
                             | None => [False]
                             | Some p => Exists p' :@ LinkedList, p --> node v p' * llseg p' e r
                           end
  end.
  
Definition llist (s : LinkedList) (m : list A) : hprop :=
  llseg s None m.

Definition maybe_points_to (T : Type) (p : option ptr) (v : T) : hprop :=
  match p with
    | None   => __
    | Some p => p --> v
  end%hprop.

Notation "x ~~> y" := (maybe_points_to x y) (at level 38).

(******************************************************************************)
(** Lemmas & Tactics                                                         **)
(******************************************************************************)

Lemma eta_node : forall nde, nde = node (data nde) (next nde).
  destruct nde; reflexivity.
Qed.

Lemma head_tail : forall l f r,
  head l = Some f -> r = tail l -> l = f :: r.
  destruct l; intros;[ discriminate | simpl in *; congruence ] .
Qed.
Hint Resolve eta_node head_tail.

(** Folding and Unfolding **)
Lemma llist_unfold : forall ls hd,
  llist hd ls ==> llseg hd None ls.
  unfold llist; sep fail simpl.
Qed.

Lemma llseg_unfold_nil : forall hd tl,
  llseg hd tl nil ==> [hd = tl].
  unfold llseg; sep fail simpl.
Qed.

Lemma llseg_unfold_cons : forall hd tl ls v,
  llseg hd tl (v :: ls) ==> Exists p :@ ptr, Exists nde :@ Node, [hd = Some p] *
    p --> nde * [v = data nde] * llseg (next nde) tl ls.
  unfold llseg; destruct ls; destruct hd; destruct tl; sep fail simpl. 
Qed.

Lemma llseg_unfold : forall hd tl ls,
  llseg hd tl ls ==> 
  match ls with
    | nil => [hd = tl]
    | v :: r => (*[hd <> tl] *) match hd with
                               | None => [False]
                               | Some p => Exists nde :@ Node, p --> nde * [v = data nde] * llseg (next nde) tl r
                             end
  end.
  unfold llseg; destruct ls; destruct hd; sep fail simpl.
Qed.

Lemma cons_seg : forall (nde : Node) e l p,
  Some p <> e ->
  p --> nde * llseg (next nde) e l ==> llseg (Some p) e (data nde :: l).
  sep fail simpl.
Qed.

Lemma cons_seg2 : forall (d : A) p p' ls,
  p --> node d (Some p') * llseg (Some p') None ls ==> llseg (Some p) None (d :: ls).
  sep fail auto. assert (Some p <> None). unfold not; intro; congruence. sep fail auto.
Qed.

Lemma cons_seg3 : forall d x x0 p0 p'0,
  head x = Some d -> 
  p0 --> node d (Some p'0) * llseg (Some p'0) None (tail x ++ x0) ==>
  llseg (Some p0) None (x ++ x0).
  destruct x; sep fail auto; [ congruence |  | ]. congruence. assert (Some p0 <> None); [ congruence |  sep fail auto ].
Qed.
Hint Resolve cons_seg cons_seg2 cons_seg3.


Theorem himp_disjoint : forall S T p1 p2 (a1:S) (a2:T), 
  p1 --> a1 * p2 --> a2 ==> p1 --> a1 * p2 --> a2 * [p1 <> p2].
(** TODO: Move this into Separation.v **)
  intros. unfold hprop_imp. intros; repeat (destruct H). destruct H0.
  exists ((x * x0)%heap). exists empty. sep fail auto. exists x. exists x0. sep fail auto. split_prover'. compute.
  split. apply ext_eq. auto. intros. subst.
  compute in H. compute in H2. pose (H p2). pose (H2 p2). destruct H3. destruct H0. compute in H1. compute in H0. rewrite H1 in *. rewrite H0 in *. assumption. 
Qed.

Lemma imp : forall (P Q : Prop) H, 
  (P -> Q)
  -> H * [P] ==> H * [Q].
  sep fail auto.
Qed.

Lemma simp : forall (P : Prop) H1 H2,
  P -> (H1 ==> H2) -> (H1 ==> [P] * H2).
  sep fail auto.
Qed.

Lemma locineq x y B C (w:B) (v:C) : x --> w * y --> v ==> [x <> y] * ??.
  intros; eapply (@himp_trans (x --> w * y --> v * [x <> y])); [ apply himp_disjoint | ]; sep fail auto.
Qed.

Lemma mlocineq x y B C (w:B) (v:C) : x --> w * y ~~> v ==> [Some x <> y] * ??.
  Hint Resolve himp_disjoint.
  intros; unfold maybe_points_to; destruct y;
    [ apply (@himp_trans (x --> w * p --> v * [x <> p])) | ]. sep fail auto.
  apply (@himp_trans (x --> w * p --> v * [Some x <> Some p])).
  apply (@imp (x <> p) (Some x <> Some p) ). congruence.
  sep fail auto.
  pose (Some x <> None). sep fail auto. apply simp. congruence. sep fail auto.
Qed.

(**
Lemma dup_any : forall P Q, P ==> Q * ?? * ?? -> P ==> Q * ??.
  intros. apply (@himp_empty_prem P (Q * ?? * ??)) in H. pose (himp_any_conc __).
  apply himp_comm_prem in H. apply (@himp_split 
**)

Lemma himp_elim_any : forall P Q R, Q ==> R * ?? -> P * Q ==> R * ??.
  sep fail auto. pose (himp_any_conc P). pose (himp_split H h).
Admitted.

Theorem himp_disjoint' : forall  h S T p (a1:S) (a2:T), 
  (p --> a1 * p --> a2)%hprop h -> False.
  intros; unfold hprop_imp; intros. repeat (destruct H). destruct H0. destruct H0. destruct H3. unfold disjoint1 in *. pose (H p). rewrite H0 in y. rewrite H3 in y. trivial.
Qed.

Lemma neqseg : forall p ls q ls',
  llseg (Some p) None ls * llseg q None ls' ==> [Some p <> q] * ??.
  destruct q; destruct ls; destruct ls'; sep fail auto; try congruence. 
  apply (@himp_trans (llseg v0 None ls' * llseg v None ls * p0 --> node a0 v0 * p --> node a v)).   
  sep fail auto.

  destruct (ptr_eq p0 p). subst. apply (@himp_trans ((p --> node a0 v0 * p --> node a v) * (llseg v0 None ls' * llseg v None ls))); [ sep fail simpl | ].
    unfold hprop_imp. intros. destruct H3. destruct H3. destruct H3. destruct H4. pose (@himp_disjoint' x Node Node p (node a0 v0) (node a v)).
    congruence.
  assert (Some p0 <> Some p). congruence.
  sep fail auto. 
Qed.

Lemma somenone_seg : forall p ls,
  llseg (Some p) None ls ==> [ls <> nil] * ??.
  destruct ls; sep fail auto; [ congruence | assert (a :: ls <> nil); [ firstorder | sep fail auto ] ].
Qed.

Lemma add_mlocineq x y B C (w:B) (v:C) P Q :
  (Some x <> y -> (x --> w * y ~~> v * P ==> Q)) ->
  (x --> w * y ~~> v * P ==> Q).
  intros; apply (add_fact (@mlocineq _ _ _ _ _ _) H).
Qed.

Lemma add_locineq x y B C (w:B) (v:C) P Q :
  (x <> y -> (x --> w * y --> v * P ==> Q)) ->
  (x --> w * y --> v * P ==> Q).
  intros; apply (add_fact (@locineq _ _ _ _ _ _) H).
Qed.

Lemma add_neqseg : forall p ls q ls' P Q,
  (Some p <> q -> 
    (llseg (Some p) None ls * llseg q None ls' * P ==> Q))
  -> llseg (Some p) None ls * llseg q None ls' * P ==> Q.
  intros; apply (add_fact (@neqseg _ _ _ _) H).
Qed.

Lemma add_somenoneseg : forall p ls P Q,
  (ls <> nil ->
    (llseg (Some p) None ls * P ==> Q))
  -> llseg (Some p) None ls * P ==> Q.
  intros; apply (add_fact (@somenone_seg _ _) H).
Qed.


Ltac add_mlocneq :=
  try search_prem ltac:(idtac;
    match goal with
      | [|- ?x --> ?xv * ?P ==> _] =>
        match P with 
          | context H [?y ~~> ?yv] => let z := context H [__] in 
            match goal with 
              | [ H: Some x = y -> False |- _ ] => fail 1
              | _ =>
                apply (@himp_trans (x --> xv * y ~~> yv * z)); 
                  [ solve [ sep fail auto ] | apply add_mlocineq; intros ]
            end
        end
    end).

Ltac add_locneq :=
  try search_prem ltac:(idtac;
    match goal with
      | [|- ?x --> ?xv * ?P ==> _] =>
        match P with 
          | context H [?y --> ?yv] => let z := context H [__] in 
            match goal with 
              | [ H: x = y -> False |- _ ] => fail 1
              | _ =>
                apply (@himp_trans (x --> xv * y --> yv * z)); 
                  [ solve [ sep fail auto ] | apply add_locineq; intros ]
            end
        end
    end).

Ltac add_segne :=
  try search_prem ltac:(idtac;fold llseg;
    match goal with
      | [|- llseg ?X None ?XL * ?P ==> _] => 
        match P with 
          | context H [llseg ?Y None ?YL] => let z := context H [__] in 
            match goal with 
              | [ H: X = Y -> False |- _ ] => fail 1
              | _ =>
                apply (@himp_trans (llseg X None XL * llseg Y None YL * z));
                  [ solve [ sep fail auto ] | apply add_neqseg; intros ]
            end
        end
    end).

Ltac add_somenoneseg :=
  try search_prem ltac:(idtac;fold llseg;
    match goal with
      | [|- llseg (Some ?X) None ?XL * ?P ==> _] => 
        match goal with 
          | [ H: XL = nil -> False |- _ ] => fail 1
          | _ => apply add_somenoneseg; intros
        end
    end).


Ltac simplr := repeat (try discriminate;
  match goal with
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
    | [ H : next _ = None |- _ ] => rewrite -> H
    | [ |- context[ptr_eq' ?X ?Y] ] => destruct (ptr_eq' X Y)
  end).

Ltac simpl_prem := fail.
(**  simpl_IfNull. **)


(** simpl_prem ltac:(apply llist_unfold || apply llseg_unfold_nil || apply llseg_unfold_cons || apply llseg_unfold). **)

(**
    match goal with
      | [ |- _ ==> ?RHS ] =>
        match RHS with
          | context[ [Some ?x <> ?y] ] => 
            search_prem ltac:(idtac;
              match goal with
                [|- ?x ~~> ?xv * ?P ==> _] => 
                match findContents y P with 
                  | (?yv, ?P') => 
                    idtac P
                end
              end)
        end
    end.
**)

Ltac expander := try discriminate; ((fold llseg; add_segne; add_somenoneseg; unfold llseg) || add_mlocneq || add_locneq).

Ltac t := unfold llist; unfold llseg; sep fail expander; sep simpl_prem simplr.
Ltac f := fold llseg; fold llist.

(********************)
(** Implementation **)
(********************)
Definition empty : STsep __ (fun r:LinkedList => llseg r r nil).
  refine ({{Return None}});
    t. 
Qed.

Definition cons : forall (v : A) (r : LinkedList) (q : [LinkedList]) (m : [list A])
    (T : Type) (vt : [T]),
  STsep (q ~~ m ~~ vt ~~ llseg r q m * q ~~> vt)
        (fun r:LinkedList => q ~~ m ~~ vt ~~ llseg r q (v :: m) * q ~~> vt * [r <> None]).
  intros;
  refine (l <- New (node v r); {{Return (Some l)}});
    t.
Qed.

Definition single : forall (v : A),
  STsep __ (fun r:LinkedList => llseg r None (v :: nil)).
  refine (fun v => {{cons v None [None] [nil] [0]}});
    t.
Qed.

Definition freeHead : forall (p : LinkedList) (q : [LinkedList]) (b : [A]) (ls : [list A]),
  STsep (ls ~~ q ~~ b ~~ llseg p q (b :: ls))
        (fun r => ls ~~ q ~~ llseg r q ls).
  intros;
  refine (
    IfNull p Then
      {{!!!}}
    Else
      Assert (ls ~~ q ~~ b ~~ Exists nde :@ Node, p --> nde * [b = data nde] * llseg (next nde) q ls);;
      nde <- !p;
      Free p;;
      {{Return (next nde)}});
    t.
Qed.

Definition copy : forall (p' : LinkedList) (q : LinkedList) (ls' : [list A])
  (T : Type) (vt : [T]),
  STsep (ls' ~~ vt ~~ llseg p' q ls' * q ~~> vt)
        (fun r:LinkedList => ls' ~~ vt ~~ llseg p' q ls' * llseg r q ls' * q ~~> vt).
  intros.
  refine (Fix2
    (fun p ls   => ls ~~ vt ~~ llseg p q ls * q ~~> vt)
    (fun p ls r => ls ~~ vt ~~ llseg p q ls * llseg r q ls * q ~~> vt)
    (fun self p ls =>
      if ptr_eq' p q then
        {{Return q}}
      else
        IfNull p Then
          {{!!!}}
        Else
          Assert (ls ~~ vt ~~ Exists nde :@ Node, [Some p <> q] * p --> nde * [head ls = Some (data nde)] * llseg (next nde) q (tail ls) * q ~~> vt);;
          nde <- !p;
          rr <- self (next nde) (ls ~~~ tail ls) <@> (ls ~~ [Some p <> q] * p --> nde * [head ls = Some (data nde)]);
          res <- cons (data nde) rr [q] (ls ~~~ tail ls) vt <@> (ls ~~ [Some p <> q] * p --> nde * [head ls = Some (data nde)] * llseg (next nde) q (tail ls));
          {{Return res}}) p' ls');
  solve [ t | hdestruct ls; t ].
Qed.

Fixpoint insertAt_model (ls : list A) (a : A) (idx : nat) {struct ls} : list A :=
  match ls with
    | nil    => a :: ls
    | f :: r => match idx with
                  | 0 => a :: f :: r
                  | S idx' => f :: insertAt_model r a idx'
                end
  end.

Definition insertAt : forall (p' : LinkedList) (a : A) (idx' : nat) (ls' : [list A]),
  STsep (ls' ~~ llist p' ls')
        (fun r:LinkedList => ls' ~~ llist r (insertAt_model ls' a idx')).
  intros.
  refine (Fix3
    (fun p ls idx => ls ~~ llist p ls)
    (fun p ls idx (r:LinkedList) => ls ~~ llist r (insertAt_model ls a idx))
    (fun self p ls idx =>
      IfNull p Then
        Assert (ls ~~ [ls = nil] * llist p nil);;
        {{cons a p [None] ls [1] <@> (ls ~~ [ls = nil])}}
      Else
        Assert (ls ~~ [ls <> nil] * llist (Some p) ls);;
        if nat_eq idx 0 then
          r <- cons a (Some p) [None] ls [0] <@> _;
          {{Return r}}  
        else
          Assert (ls ~~ [ls <> nil] * Exists nde :@ Node, p --> nde * [head ls = Some (data nde)] * llist (next nde) (tail ls));;
          nde <- !p; 
          Assert (ls ~~ [ls <> nil] * p --> nde * [head ls = Some (data nde)] * llist (next nde) (tail ls));;
          zz <- self (next nde) (ls ~~~ tail ls) (pred idx) <@> (ls ~~ [ls <> nil] * p --> nde * [head ls = Some (data nde)]);
          p ::= node (data nde) zz;;
          {{Return (Some p)}}
      ) p' ls' idx');
  solve [ t | hdestruct ls; t | hdestruct ls; t; destruct idx; t ].
Qed.

Definition append : forall (p' : LinkedList) (q : LinkedList)
  (lsp' lsq : [list A]), 
  STsep (lsp' ~~ lsq ~~ llist p' lsp' * llist q lsq)
        (fun r:LinkedList => lsp' ~~ lsq ~~ llist r (lsp' ++ lsq)).
  intros.
  refine (Fix2 
    (fun p lsp   => lsp ~~ lsq ~~ llist p lsp * llist q lsq)
    (fun p lsp r => lsp ~~ lsq ~~ llist r (lsp ++ lsq))
    (fun self p lsp =>
      IfNull p Then 
        {{Return q}}
      Else
        Assert (lsp ~~ lsq ~~ Exists nde :@ Node, p --> nde * [head lsp = Some (data nde)] * llist (next nde) (tail lsp) * llist q lsq * [Some p <> q]);;
        nde <- !p;
        let d := data nde in
        Assert (lsp ~~ lsq ~~ p --> nde * llist (next nde) (tail lsp) * llist q lsq * 
                  [head lsp = Some (data nde)] * [Some p <> q]);;
        zz <- self (next nde) (lsp ~~~ tail lsp) <@> 
               (lsp ~~ lsq ~~ p --> nde * [head lsp = Some (data nde)]  *
                                 [Some p <> q] * [Some p <> q]);
        p ::= node d zz;;
        {{Return (Some p)}}
    ) p' lsp'); clear self;
  solve [t | hdestruct lsp; t | hdestruct lsp; [ t | match goal with 
                                                       | [ H : ?p = Some _ |- _ ] => rewrite H
                                                     end; t ] ].
Qed.

Section Remove.

  Parameter eq_a : forall (a b : A), {a = b} + {a <> b}.

  Fixpoint removeFirst_model (ls : list A) (a : A) : list A :=
    match ls with
      | nil => nil
      | f :: r => if eq_a f a then r else f :: (removeFirst_model r a)
    end.


  Definition removeFirst : forall (p' : LinkedList) (a : A) (ls' : [list A]),
    STsep (ls' ~~ llist p' ls')
          (fun r:LinkedList => ls' ~~ llist r (removeFirst_model ls' a)).
    intros.
    refine (Fix2
      (fun p ls => ls ~~ llist p ls)
      (fun p ls r => ls ~~ llist r (removeFirst_model ls a))
      (fun self p ls =>
        IfNull p As p' Then
          {{Return p}}
        Else
          Assert (ls ~~ Exists nde :@ Node, p' --> nde * [head ls = Some (data nde)] * llist (next nde) (tail ls) * [ls <> nil]);;
          nde <- !p';
          if eq_a (data nde) a then 
            Free p';;
            {{Return (next nde)}}
          else 
            Assert (ls ~~ p' --> nde * [head ls = Some (data nde)] * llist (next nde) (tail ls) * [ls <> nil]);;
            res <- self (next nde) (ls ~~~ tail ls) <@> (ls ~~ p' --> nde * [head ls = Some (data nde)] * [ls <> nil]);
            p' ::= node (data nde) res;;
            {{Return p}}            
      ) p' ls'); clear self;
    solve [ t | hdestruct ls; t | hdestruct ls; t; match goal with
                                                     | [ |- context[eq_a ?X ?Y] ] => destruct (eq_a X Y)
                                                   end; t ].
  Qed.

  Fixpoint filter_model : forall (ls : list A) (a : A) : list A :=
    match ls with 
      | nil => nil
      | f :: r => if eq_a f a then filter_model r a else f :: filter_model r a
    end.

End Remove.

End LINKED_LIST_SEG.

