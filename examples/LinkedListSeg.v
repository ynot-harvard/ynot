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

Lemma head_some_nonil : forall x y,
  head x = Some y
  -> x <> nil.
  destruct x; intros; simpl in *; congruence.
Qed.
Hint Resolve eta_node head_tail head_some_nonil.

(** Folding and Unfolding **)
Lemma llist_unfold : forall ls hd,
  llist hd ls ==> llseg hd None ls.
  sep fail simpl.
Qed.

Lemma llseg_unfold_nil : forall hd tl,
  llseg hd tl nil ==> [hd = tl].
  sep fail simpl.
Qed.

Lemma llseg_unfold_cons : forall hd tl ls v,
  llseg hd tl (v :: ls) ==> Exists p :@ ptr, [hd = Some p] * Exists nde :@ Node,
    p --> nde * [nde = node v (next nde)] * llseg (next nde) tl ls.
  destruct ls; destruct hd; destruct tl; sep fail simpl. 
Qed.

Lemma llseg_unfold_some_cons : forall p tl ls v,
  llseg (Some p) tl (v :: ls) ==> Exists nde :@ Node,
    p --> nde * [nde = node v (next nde)] * llseg (next nde) tl ls.
  destruct ls; destruct tl; sep fail simpl. 
Qed.

Lemma llseg_unfold_some : forall p tl ls,
  (Some p <> tl)
  -> llseg (Some p) tl ls ==> Exists nde :@ Node,
     p --> nde * [head ls = Some (data nde)] * llseg (next nde) tl (tail ls).
  destruct ls; sep fail simpl. 
Qed.

Lemma llseg_unfold_same : forall p ls,
  llseg p p ls ==> [ls = nil].
  destruct ls; sep fail simpl.
Qed.

Lemma llseg_unfold_head_none : forall p l,
  llseg None p l ==> [p = None] * [l = nil].
  destruct l; sep fail simpl.
Qed.

Lemma llseg_unfold_tail_none : forall p l,
  p <> None
  -> llseg p None l ==> [l <> nil] * Exists p' :@ ptr, [p = Some p'] * 
  Exists nde :@ Node, p' --> nde * llseg (next nde) None (tail l) * [head l = Some (data nde)].
  destruct l; destruct p; sep fail ltac:(try congruence).
Qed.

Lemma combine : forall nde ls p tl,
  Some p <> tl
  -> head ls = Some (data nde) 
  -> p --> nde * llseg (next nde) tl (tail ls) ==> llseg (Some p) tl ls.
  unfold llseg; destruct ls; intros; 
    [ inversion H0
    | sep fail auto; destruct nde; inversion H0; reflexivity ].
Qed.

Lemma empty_seg : forall p, __ ==> llseg p p nil.
  sep fail simpl.
Qed.

(** Not Quite unfolding lemmas **)
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

(** disjointness **)
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
  search_prem ltac:(idtac;
    match goal with
      | [|- ?x --> ?xv * ?P ==> _] =>
        match P with 
          | context H [?y ~~> ?yv] => let z := context H [__] in 
            match goal with 
              | [ H: Some x = y -> False |- _ ] => fail 1
              | [ H: Some x <> y |- _ ] => fail 1
              | [ H: y <> Some x |- _ ] => fail 1
              | [ H: y = Some x -> False |- _ ] => fail 1
              | _ =>
                apply (@himp_trans (x --> xv * y ~~> yv * z)); 
                  [ solve [ sep fail auto ] | apply add_mlocineq; intros ]
            end
        end
    end).

Ltac add_locneq :=
  search_prem ltac:(idtac;
    match goal with
      | [|- ?x --> ?xv * ?P ==> _] =>
        match P with 
          | context H [?y --> ?yv] => let z := context H [__] in 
            match goal with 
              | [ H: x = y -> False |- _ ] => fail 1
              | [ H: x <> y |- _ ] => fail 1
              | [ H: y = x -> False |- _ ] => fail 1
              | [ H: y <> x |- _ ] => fail 1
              | _ =>
                apply (@himp_trans (x --> xv * y --> yv * z)); 
                  [ solve [ sep fail auto ] | apply add_locineq; intros ]
            end
        end
    end).

Ltac add_segne :=
  search_prem ltac:(idtac;fold llseg;
    match goal with
      | [|- llseg ?X None ?XL * ?P ==> _] => 
        match P with 
          | context H [llseg ?Y None ?YL] => let z := context H [__] in 
            match goal with 
              | [ H: X = Y -> False |- _ ] => fail 1
              | [ H: X <> Y |- _ ] => fail 1
              | [ H: Y = X -> False |- _ ] => fail 1
              | [ H: Y <> X |- _ ] => fail 1
              | _ =>
                apply (@himp_trans (llseg X None XL * llseg Y None YL * z));
                  [ solve [ sep fail auto ] | apply add_neqseg; intros ]
            end
        end
    end).

Ltac add_somenoneseg :=
  search_prem ltac:(idtac;fold llseg;
    match goal with
      | [|- llseg (Some ?X) None ?XL * ?P ==> _] => 
        match goal with 
          | [ H: XL = nil -> False |- _ ] => fail 1
          | [ H: XL <> nil |- _ ] => fail 1
          | [ H: nil = XL -> False |- _ ] => fail 1
          | [ H: nil <> XL |- _ ] => fail 1
          | _ => apply add_somenoneseg; intros
        end
    end).

Ltac merge :=
  repeat match goal with 
           | [ |- ?PREM ==> ?CONC ] =>
             match PREM with
               | context H [?X --> ?XV] =>
                 match context H [__] with
                   | context H' [llseg (next XV) ?TL ?LS] => 
                     let H'' := context H' [__] in 
                       apply (@himp_trans (llseg (Some X) TL ((data XV) :: LS) * H''));
                         [ solve [ sep fail simpl ] | ]
                 end
             end
         end.


Ltac print_goal := idtac "GOAL <<<<<<<<<<<<<<<<<<<<<<<<<<";
  match goal with
    [ |- ?H ] => idtac H
  end.
Ltac print_state := idtac "STATE <<<<<<<<<<<<<<<<<<<<<<<";
  try match goal with
        [ H : ?P |- _ ] => idtac H ":" P; fail
      end;
  match goal with
    [ |- ?H ] => idtac H
  end.

Ltac extend P tk := idtac;
  match goal with
    | [ H : P |- _ ] => fail 1
    | _ => tk
  end.

Ltac ondemand_subst := idtac;
  repeat match goal with 
           | [ H : ?X = ?Y |- context[?X] ] => 
             match Y with 
               | [_]%inhabited => fail 1
               | _ => rewrite -> H
             end
         end.

Ltac extend_eq l r tac :=
  match l with
    | r => fail 1
    | _ => 
      match goal with 
        | [ H : l = r |- _ ] => fail 2
        | [ H : r = l |- _ ] => fail 2
        | _ => tac
      end
  end.


Ltac simplr'' := (idtac "simplr''"; simpl; congruence || discriminate
  || (add_segne; idtac "S1")
  || (add_somenoneseg; idtac "S2")
  || (add_mlocneq; idtac "S3")
  || (add_locneq; idtac "S4")
  || match goal with
       | [ H : ?X = ?X |- _ ] => clear H
       | [ H : [?X]%inhabited = [?Y]%inhabited |- _ ] => extend_eq X Y ltac:(let nm := fresh "eq" in pose (nm := pack_injective H))
       | [ H : Some ?X = Some ?Y |- _ ] => extend_eq X Y ltac:(inversion H)
       | [ H : ?X = Some ?Y |- _ ] => 
         match X with 
           | Some _ => fail 1
           | _ => rewrite -> H
         end
       | [ H : next _ = None |- _ ] => rewrite -> H
       | [ H : next _ = Some _ |- _ ] => rewrite -> H
       | [ H : [?x]%inhabited = [?y]%inhabited |- _ ] =>
         match x with
           | y => fail
           | _ => extend_eq x y ltac:(assert (x = y); [ apply pack_injective; assumption | ])
         end
       | [ H : ?X = None |- context[?X ~~> _] ] => rewrite -> H
       | [ H : None = ?X |- context[?X ~~> _] ] => rewrite <- H
       | [ H : ?X = nil |- _ ] => rewrite -> H
       | [ H : nil = ?X |- _ ] => rewrite <- H
     end 
  || match goal with 
       | [ |- ?PREM ==> ?CONC ] =>
         match PREM with 
           | context[match ?X with
                       | nil => _
                       | _ :: _ => _
                     end] => destruct X
           | context[match ?X with
                       | None => _
                       | Some _ => _
                     end] => destruct X
           | context[ptr_eq' ?X ?Y] => destruct (ptr_eq' X Y)
           | context[llseg ?X ?X ?Y] => destruct Y; [ discriminate | ]
         end
         || match CONC with
              | context [llseg _ _ (match ?LS with 
                                      | nil => _
                                      | _ :: _ => _
                                    end)] =>
                match goal with
                  | [ H : LS <> nil |- _ ] => destruct LS; [ discriminate | ]
                  | [ H : head LS = Some _ |- _ ] => 
                    destruct LS; [ pose (head_some_nonil H); discriminate | ]
                end 
              | context [llseg _ _ ?LS] =>
                match goal with 
                  | [ H : head LS = Some ?HD |- _ ] => 
                    let RW := fresh "list_eq" in
                      assert (LS = HD :: (tail LS)) as RW; [ solve [ auto | fail 1 ] | rewrite -> RW; simpl ]
                end
              | context[ [?X]%hprop ] => 
                match X with
                  | ?Y = ?Y => fail 1
                  | ?X = ?Y => extend_eq X Y ltac:(assert (X); [ solve [ congruence | firstorder ] || fail 1 | ])
                end
            end
       (** ETA NODE APPLICATIONS **)
       | [ |- ?V = node ?X ?Y ] =>
         match V with
           | node _ _ => fail 1
           | _ => 
             match goal with 
               [ H: V = node _ _ |- _ ] => rewrite -> H; try reflexivity
             end
         end
       | [ |- ?V = node ?X (next ?V) ] =>
         match goal with
           | [ H : X = data V |- _ ] => solve [ rewrite -> H; apply eta_node ]
           | [ H : data V = X |- _ ] => solve [ rewrite <- H; apply eta_node ]
         end
       | [ |- ?V = node (data ?V) ?X ] =>
         match goal with
           | [ H : X = next V |- _ ] => solve [ rewrite -> H; apply eta_node ]
           | [ H : next V = X |- _ ] => solve [ rewrite <- H; apply eta_node ]
         end
       | [ |- ?V = node ?X ?Y ] =>
         match goal with
           | [ H : Y = next V |- _ ] => rewrite -> H
           | [ H : next V = Y |- _ ] => rewrite <- H
         end;
         match goal with
           | [ H : X = data V |- _ ] => solve [ rewrite -> H; apply eta_node ]
           | [ H : data V = X |- _ ] => solve [ rewrite <- H; apply eta_node ]
         end
     end).

Ltac simplr := simpl; repeat simplr''.

Ltac unfolder := simpl_prem ltac:(
       (apply llseg_unfold_nil; idtac "nil")
    || (apply llseg_unfold_some_cons; idtac "some_cons")
    || (apply llseg_unfold_same; idtac "same")
    || (apply llseg_unfold_cons; idtac "cons")
    || (apply llseg_unfold_head_none; idtac "head_none")
    || (apply llseg_unfold_some; idtac "some"; solve [ congruence ])
    || (apply llseg_unfold_tail_none; solve [ congruence ])).

Ltac expander :=
     (add_segne; idtac "S1")
  || (add_somenoneseg; idtac "S2")
  || (add_mlocneq; idtac "S3")
  || (add_locneq; idtac "S4").

Ltac simp_prem := discriminate || (repeat (ondemand_subst || unfolder || expander)).

Ltac t := unfold llist; simpl_IfNull; sep simp_prem simplr; sep fail auto.
Ltac f := fold llseg; fold llist.

Ltac rsep expander tac := unfold llist; intros;
  try equater; try inhabiter; expander; unpack_conc;
    repeat match goal with
             | [ H1 : ?X = [?Y]%inhabited, H2 : inhabit_unpack ?X ?XV = [?Z]%inhabited |- _ ==> ?CONC ] => 
               match CONC with
                 | context[Z] =>
                   let l := fresh "eq" in
                     rewrite -> H1 in H2; simpl in H2; pose (l := pack_injective H2); rewrite <- l
               end
           end; ondemand_subst; canceler; 
    solve [ sep fail idtac 
          | sep fail tac; 
            match goal with
              | [ |- _ ==> ?CONC ] => 
                match CONC with 
                  | context [llseg _ _ (?X ++ _)] => destruct X
                end
            end; sep fail tac ].

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
    IfNull p Then {{!!!}}
    Else nde <- !p;
         Free p;;
         {{Return (next nde)}});
  t.
Qed.

Definition append' : forall (pr' : ptr) (nde' : Node) (q : LinkedList) (lsp' lsq : [list A]),
  STsep (lsp' ~~ lsq ~~ pr' --> nde' * llist (next nde') lsp' * llist q lsq)
        (fun _:unit => lsp' ~~ lsq ~~ Exists r :@ LinkedList, pr' --> node (data nde') r * llist r (lsp' ++ lsq)).
  intros;
  refine (Fix3
    (fun pr nde lsp => lsp ~~ lsq ~~ pr --> nde * llist (next nde) lsp * llist q lsq)
    (fun pr nde lsp (_:unit) => lsp ~~ lsq ~~ Exists r :@ LinkedList, pr --> node (data nde) r * llist r (lsp ++ lsq))
    (fun self pr nde lsp =>
      IfNull (next nde) As p
      Then {{pr ::= node (data nde) q}}
      Else nde' <- !p;
           {{self p nde' (lsp ~~~ tail lsp) <@> _}}
    ) pr' nde' lsp');
  rsep simp_prem t.
Qed.

Definition append : forall (p : LinkedList) (q : LinkedList) (lsp lsq : [list A]), 
  STsep (lsp ~~ lsq ~~ llist p lsp * llist q lsq)
        (fun r:LinkedList => lsp ~~ lsq ~~ llist r (lsp ++ lsq)).
  intros;
  refine (
    IfNull p As p'
    Then {{Return q}}
    Else nde <- !p';
         append' p' nde q (lsp ~~~ tail lsp) lsq <@> _;;
         {{Return p}});
  rsep simp_prem t.
Qed.

Definition copy : forall (p' : LinkedList) (q : LinkedList) (ls' : [list A]) (T : Set) (vt : [T]),
  STsep (ls' ~~ vt ~~ llseg p' q ls' * q ~~> vt)
        (fun r:LinkedList => ls' ~~ vt ~~ llseg p' q ls' * llseg r q ls' * q ~~> vt).
  intros;
  refine (Fix2
    (fun p ls   => ls ~~ vt ~~ llseg p q ls * q ~~> vt)
    (fun p ls r => ls ~~ vt ~~ llseg p q ls * llseg r q ls * q ~~> vt)
    (fun self p ls =>
      if ptr_eq' p q then
        {{Return q}}
      else
        IfNull p Then {{!!!}}
        Else nde <- !p;
             rr <- self (next nde) (ls ~~~ tail ls) <@> (ls ~~ [Some p <> q] * p --> nde * [head ls = Some (data nde)]);
             res <- cons (data nde) rr [q] (ls ~~~ tail ls) vt <@> (ls ~~ [head ls = Some (data nde)] * llseg (Some p) q ls);
             {{Return res}}) p' ls'); clear self.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  rsep simp_prem simplr.
  t.
  t.
  t.
  sep simp_prem idtac.
Qed.

Fixpoint insertAt_model (ls : list A) (a : A) (idx : nat) {struct idx} : list A :=
  match idx with
    | 0 => a :: ls
    | S idx' => match ls with
                  | nil    => a :: ls
                  | f :: r => f :: insertAt_model r a idx'
                end
  end.
(**
Definition insertAt' : forall (p' : ptr) (idx' : nat) (a : A) (ls' : [list A]),
  STsep (ls' ~~ llist (Some p') ls')
        (fun _:unit => ls' ~~ llist (Some p') (insertAt_model ls' a (S idx'))).
  intros;
  refine (Fix3 
    (fun p ls idx => ls ~~ llist (Some p) ls)
    (fun p ls idx (_:unit) => ls ~~ llist (Some p) (insertAt_model ls a (S idx)))
    (fun self p ls idx =>
      nde <- !p;
      if nat_eq 0 idx then
        nelem <- New (node a (next nde));
        p ::= node (data nde) (Some nelem);;
        {{Return tt}}
      else
        IfNull next nde As nxt Then 
          nelem <- New (node a (next nde));
          p ::= node (data nde) (Some nelem);;
          {{Return tt}}
        Else
          {{self nxt (ls ~~~ tail ls) (pred idx) <@> (ls ~~ p --> nde * [head ls = Some (data nde)])}}) p' ls' idx'); clear self.
(**  solve [ t | match goal with 
                | [ |- context[insertAt_model nil _ ?IDX] ] => destruct IDX; simpl
              end; t ].
**)
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  match goal with 
    | [ |- context[insertAt_model nil _ ?IDX] ] => destruct IDX; simpl
  end; t.
  t.
  t. match goal with 
    | [ |- context[insertAt_model nil _ ?IDX] ] => destruct IDX; simpl
  end; t. 
  destruct idx; t.
Qed.

Definition insertAt : forall (p : LinkedList) (a : A) (idx : nat) (ls : [list A]),
  STsep (ls ~~ llist p ls)
        (fun r:LinkedList => ls ~~ llist r (insertAt_model ls a idx)).
  intros;
  refine (
    IfNull p Then
      {{cons a p [None] ls [1] <@> (ls ~~ [ls = nil])}}
    Else
(**        Assert (ls ~~ [ls <> nil] * llist (Some p) ls);; **)
      if nat_eq idx 0 then
        {{cons a (Some p) [None] ls [0] <@> (__)}}
(**          {{Return r}}  **)
      else
(**          Assert (ls ~~ [ls <> nil] * Exists nde :@ Node, p --> nde * [head ls = Some (data nde)] * llist (next nde) (tail ls));; **)
(**          Assert (ls ~~ [ls <> nil] * p --> nde * [head ls = Some (data nde)] * llist (next nde) (tail ls));; **)
        insertAt' p (pred idx) a ls <@> __;;
        {{Return (Some p)}}).
  t.
  t. destruct idx; t.
  t.
  t.
  t.
  t.
  t.
  t.
  destruct idx; t.
  destruct idx; t.
Qed.
**)
Section Remove.

  Parameter eq_a : forall (a b : A), {a = b} + {a <> b}.

  Fixpoint removeFirst_model (ls : list A) (a : A) : list A :=
    match ls with
      | nil => nil
      | f :: r => if eq_a f a then r else f :: (removeFirst_model r a)
    end.

  Definition removeFirst' : forall (pr' : ptr) (p' : LinkedList) (pr_a' a : A) (ls' : [list A]),
    STsep (ls' ~~ llist p' ls' * pr' --> node pr_a' p')
          (fun _:unit => ls' ~~ Exists p'' :@ LinkedList, llist p'' (removeFirst_model ls' a) * pr' --> node pr_a' p'').
    intros;
    refine (Fix4
      (fun pr pr_a p ls => ls ~~ llist p ls * pr --> node pr_a p)
      (fun pr pr_a p ls r => ls ~~ Exists p'' :@ LinkedList, llist p'' (removeFirst_model ls a) * pr --> node pr_a p'')
      (fun self pr pr_a p ls =>
        IfNull p As p' Then
          {{Return tt}}
        Else
          nde <- !p';
          if eq_a (data nde) a then 
            pr ::=  node pr_a (next nde);;
            Free p';;
            {{Return tt}}
          else 
            {{self p' (data nde) (next nde) (ls ~~~ tail ls) <@> (ls ~~ [head ls = Some (data nde)] * [ls <> nil] * [p = Some p'] * pr --> node pr_a p)}}
        ) pr' pr_a' p' ls'); clear self.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t. destruct x; [ t | simpl; destruct (eq_a a (data v0)); t ].
    t. 
    t; destruct x; t; destruct (eq_a (data nde) a); t.
  Qed.

  Definition removeFirst : forall (p : LinkedList) (a : A) (ls : [list A]),
    STsep (ls ~~ llist p ls)
          (fun r:LinkedList => ls ~~ llist r (removeFirst_model ls a)).
    intros;
    refine (
      IfNull p As p' Then
        {{Return p}}
      Else
(**       Assert (ls ~~ Exists nde :@ Node, p' --> nde * [head ls = Some (data nde)] * llist (next nde) (tail ls) * [ls <> nil]);; **)
        nde <- !p';
        if eq_a (data nde) a then 
          Free p';;
          {{Return (next nde)}}
        else
          removeFirst' p' (next nde) (data nde) a (ls ~~~ tail ls) <@> (ls ~~ [head ls = Some (data nde)]);;
          {{Return p}}
      ).
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t; destruct x; [ t | t; destruct (eq_a (data v0) (data v0)); t ].
    t.
    t.
    t.
    t; destruct x; [ t | simpl; destruct (eq_a a0 a); t ].
  Qed.

  Fixpoint filter_model (ls : list A) (a : A) : list A :=
    match ls with 
      | nil => nil
      | f :: r => if eq_a f a then filter_model r a else f :: filter_model r a
    end.

  Definition filter' : forall (pr' : ptr) (p' : LinkedList) (pr_a' a : A) (ls' : [list A]),
    STsep (ls' ~~ llist p' ls' * pr' --> node pr_a' p')
          (fun (_:unit) => ls' ~~ Exists r :@ LinkedList, llist r (filter_model ls' a) * pr' --> node pr_a' r).
    intros;
    refine (Fix4
      (fun pr pr_a p ls => ls ~~ llist p ls * pr --> node pr_a p)
      (fun pr pr_a p ls (_:unit) => ls ~~ Exists r :@ LinkedList, llist r (filter_model ls a) * pr --> node pr_a r)
      (fun self pr pr_a p ls =>
        IfNull p As p' Then
          {{Return tt}}
        Else
          nde <- !p';
          if eq_a (data nde) a then 
            pr ::=  node pr_a (next nde);; 
            Free p';;
            {{self pr pr_a       (next nde) (ls ~~~ tail ls) <@> _ (ls ~~ [head ls = Some (data nde)] * [p = Some p'])}}
          else 
            {{self p' (data nde) (next nde) (ls ~~~ tail ls) <@> (ls ~~ [head ls = Some (data nde)] * [p = Some p'] * pr --> node pr_a p)}}
        ) pr' pr_a' p' ls').
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t; destruct x; [ t | simpl; destruct (eq_a a (data nde)); t ].
    t.
    t.
    t; destruct x; [ t | simpl; destruct (eq_a a0 a); t ].
  Qed.
  
  Definition filter : forall (p : LinkedList) (a : A) (ls : [list A]),
    STsep (ls ~~ llist p ls)
          (fun r:LinkedList => ls ~~ llist r (filter_model ls a)).
    intros;
    refine (
      IfNull p As p' Then 
        {{Return p}}
      Else
        nde <- !p';
        {{filter' p' (next nde) (data nde) a (ls ~~~ tail ls) <@> (ls ~~ [head ls = Some (data nde)])}};;
        if eq_a (data nde) a then
          nde <- !p';
          Free p';;
          {{Return (next nde)}}
        else
          {{Return p}}).
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t. destruct x. t. simpl. destruct (eq_a a (data nde)); t.
    t.
    t. destruct x. t. simpl. destruct (eq_a a0 a); t.
  Qed.    

End Remove.


End LINKED_LIST_SEG.

