Require Import Ynot.
Require Import List.
Require Import Peano_dec.

Set Implicit Arguments.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Section LinkedListSegModel.
 Variable A : Set.
 Require Export List.
 Set Implicit Arguments.

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
 
 Fixpoint insertAt_model (ls : list A) (a : A) (idx : nat) {struct idx} : list A :=
   match idx with
     | 0 => a :: ls
     | S idx' => match ls with
                   | nil    => a :: ls
                   | f :: r => f :: insertAt_model r a idx'
                 end
  end.

Inductive action : Type :=
  | Keep : action
  | Del : action
  | Update : A -> action.

  Fixpoint process_model (ls : list A) (p : A -> action) : list A :=
    match ls with
      | nil => nil
      | f :: r => 
        match p f with
          | Keep => f :: (process_model r p)
          | Del => process_model r p
          | Update f' => f' :: (process_model r p)
        end
    end.

  Fixpoint foldr_model (T : Type) (p : A -> T -> T) (ls : list A) (t : T) {struct ls} : T :=
    match ls with
      | nil => t
      | f :: r => p f (foldr_model p r t)
    end.

 Variable eq_a : forall (a b : A), {a = b} + {a <> b}.

  Fixpoint removeFirst_model (ls : list A) (a : A) : list A :=
    match ls with
      | nil => nil
      | f :: r => if eq_a f a then r else f :: (removeFirst_model r a)
    end.

  Fixpoint filter_model (ls : list A) (a : A) : list A :=
    match ls with 
      | nil => nil
      | f :: r => if eq_a f a then filter_model r a else f :: filter_model r a
    end.
End LinkedListSegModel.

Definition ptr_eq' : forall (p q : option ptr), {p = q} + {p <> q}.
  decide equality. apply ptr_eq_dec.
Qed.

Definition maybe_points_to (p : option ptr) : hprop :=
  match p with
    | None   => __
    | Some p => p -->?
  end%hprop.

Notation "x ~~>?" := (maybe_points_to x) (at level 38).

Record LinkedListSeg (A : Set) := mkList
  { LinkedList : Set := option ptr
  ; llseg : LinkedList -> LinkedList -> list A -> hprop
  ; llist := fun (p: LinkedList) (m : list A) => llseg p None m
  ; empty : STsep __ (fun r:LinkedList => llseg r None nil)
  ; cons : forall (v : A) (r : LinkedList) (q : [LinkedList]) (m : [list A]),
    STsep (q ~~ m ~~ llseg r q m * q ~~>?)
          (fun r:LinkedList => q ~~ m ~~ llseg r q (v :: m) * q ~~>?)
  ; single : forall (v : A),
    STsep __ (fun r:LinkedList => llseg r None (v :: nil))
  ; freeList : forall (p' q : LinkedList) (ls' : [list A]),
    STsep (ls' ~~ llseg p' q ls')
          (fun _:unit => __)
  ; freeHead : forall (p : LinkedList) (q : [LinkedList]) (b : [A]) (ls : [list A]),
    STsep (ls ~~ q ~~ b ~~ llseg p q (b :: ls))
          (fun r => ls ~~ q ~~ llseg r q ls)
  ; append : forall (p q : LinkedList) (lsp lsq : [list A]),
    STsep (lsp ~~ lsq ~~ llist p lsp * llist q lsq)
          (fun r:LinkedList => lsp ~~ lsq ~~ llist r (lsp ++ lsq))
  ; copy : forall (p q : LinkedList) (ls : [list A]),
    STsep (ls ~~ llseg p q ls * q ~~>?)
          (fun r:LinkedList => ls ~~ llseg p q ls * llseg r q ls * q ~~>?)
  ; insertAt : forall (p : LinkedList) (a : A) (idx : nat) (ls : [list A]),
    STsep (ls ~~ llist p ls)
          (fun r:LinkedList => ls ~~ llist r (insertAt_model ls a idx))
  ; elements : forall (p q : LinkedList) (ls : [list A]),
    STsep (ls ~~ llseg p q ls)
          (fun r:list A => ls ~~ [r = ls] * llseg p q ls)
  ; nil_empty : forall p q, llseg p q nil ==> [p = q]
  ; removeFirst : forall (eq_a : forall (a b : A), {a = b} + {a <> b})
    (p : LinkedList) (a : A) (ls : [list A]),
    STsep (ls ~~ llist p ls)
          (fun r:LinkedList => ls ~~ llist r (removeFirst_model eq_a ls a))
  ; filter : forall (eq_a : forall (a b : A), {a = b} + {a <> b})
    (p : LinkedList) (a : A) (ls : [list A]),
    STsep (ls ~~ llist p ls)
          (fun r:LinkedList => ls ~~ llist r (filter_model eq_a ls a))
  ; process : forall (p q : LinkedList) (up : A -> action A) (ls : [list A]),
    STsep (ls ~~ llseg p q ls)
          (fun r:LinkedList => ls ~~ llseg r q (process_model ls up))
  ; foldr_f : forall (T : Type) (p q : LinkedList) (f : A -> T -> T) (ls : [list A]) (t : T),
    STsep (ls ~~ llseg p q ls)
          (fun r:T => ls ~~ llseg p q ls * [r = foldr_model f ls t])
  ; foldl : forall (T  : Type) (p q : LinkedList) (I : T -> list A -> hprop)
    (c : forall (a : T) (v : A) (m : [list A]),
         STsep (m ~~ I a m)
               (fun a':T => m ~~ I a' (m ++ (v :: nil))))
    (ls : [list A]) (a : T),
    STsep (ls ~~ llseg p q ls * I a nil)
          (fun r:T => ls ~~ llseg p q ls * I r ls)
  ; foldr : forall (T  : Type) (p q : LinkedList) (I : T -> list A -> hprop)
    (c : forall (a : T) (v : A) (m : [list A]),
         STsep (m ~~ I a m)
               (fun a':T => m ~~ I a' (v :: m)))
    (ls : [list A]) (a : T),
    STsep (ls ~~ llseg p q ls * I a nil)
          (fun r:T => ls ~~ llseg p q ls * I r ls)
  }.

Section HeapLinkedList.
  Variable A : Set.

  Require Import Ynot.

  (** Representation ********************************************************)

  Definition t : Set := A.
  Definition LinkedList' : Set := option ptr.

  Record Node : Set := node {
    data: t;
    next: LinkedList'
  }.
  
  Fixpoint llseg' (s e : LinkedList') (m : list t) {struct m} : hprop :=
    match m with 
      | nil => [s = e]
      | v :: r => [s <> e] *
        match s with
          | None => [False]
          | Some p => Exists p' :@ LinkedList', p --> node v p' * llseg' p' e r
        end
    end.
  
  Definition llist' (s : LinkedList') (m : list t) : hprop := llseg' s None m.

  (** Lemmas & Tactics ******************************************************)

  Lemma eta_node : forall nde, nde = node (data nde) (next nde).
    destruct nde; reflexivity.
  Qed.
  
  Lemma head_tail : forall l (f:A) r,
    head l = Some f -> r = tail l -> l = f :: r.
    destruct l; intros;[ discriminate | simpl in *; congruence ] .
  Qed.

  Lemma head_some_nonil : forall x (y:A),
    head x = Some y
    -> x <> nil.
    destruct x; intros; simpl in *; congruence.
  Qed.

  Lemma app_nil : forall T (x: list T), x ++ nil = x.
    induction x; firstorder.
  Qed.
  
  Hint Resolve eta_node head_tail head_some_nonil.

  (**  Unfolding **)
  Lemma llseg'_unfold_nil : forall hd tl,
    llseg' hd tl nil ==> [hd = tl].
    sep fail simpl.
  Qed.

  Lemma llseg'_unfold_cons : forall hd tl ls v,
    llseg' hd tl (v :: ls) ==> Exists p :@ ptr, [hd = Some p] * Exists nde :@ Node,
    p --> nde * [nde = node v (next nde)] * llseg' (next nde) tl ls.
    destruct ls; destruct hd; destruct tl; sep fail simpl. 
  Qed.

  Lemma llseg'_unfold_some_cons : forall p tl ls v,
    llseg' (Some p) tl (v :: ls) ==> Exists nde :@ Node,
    p --> nde * [nde = node v (next nde)] * llseg' (next nde) tl ls.
    destruct ls; destruct tl; sep fail simpl. 
  Qed.
  
  Lemma llseg'_unfold_some : forall p tl ls,
    (Some p <> tl)
    -> llseg' (Some p) tl ls ==> Exists nde :@ Node,
       p --> nde * [head ls = Some (data nde)] * llseg' (next nde) tl (tail ls).
    destruct ls; sep fail simpl. 
  Qed.

  Lemma llseg'_unfold_same : forall p ls,
    llseg' p p ls ==> [ls = nil].
    destruct ls; sep fail simpl.
  Qed.

  Lemma llseg'_unfold_head_none : forall p l,
    llseg' None p l ==> [p = None] * [l = nil].
    destruct l; sep fail simpl.
  Qed.

  Lemma llseg'_unfold_tail_none : forall p l,
    p <> None
    -> llseg' p None l ==> [l <> nil] * Exists p' :@ ptr, [p = Some p'] * 
    Exists nde :@ Node, p' --> nde * llseg' (next nde) None (tail l) * [head l = Some (data nde)].
    destruct l; destruct p; sep fail ltac:(try congruence).
  Qed.
  
  (** Folding Lemmas **)
  Lemma combine : forall nde ls p tl,
    Some p <> tl
    -> head ls = Some (data nde) 
    -> p --> nde * llseg' (next nde) tl (tail ls) ==> llseg' (Some p) tl ls.
    unfold llseg'; destruct ls; intros; 
      [ inversion H0
        | sep fail auto; destruct nde; inversion H0; reflexivity ].
  Qed.
  
  Lemma combine' : forall nde ls p a n,
    a = data nde -> n = next nde
    -> llseg' n None ls * p --> nde ==> llseg' (Some p) None (a :: ls).
    unfold llseg'; intros; assert (Some p <> None); try congruence; sep fail idtac.
  Qed.

  Hint Resolve combine combine'.
  
  Lemma locineq x y (B C : Set) (w:B) (v:C) : x --> w * y --> v ==> [x <> y] * ??.
    intros; eapply (@himp_trans (x --> w * y --> v * [x <> y])); [ apply himp_disjoint | ]; sep fail auto.
  Qed.

  Lemma mlocineq x y (B : Set) (w:B) : x --> w * y ~~>? ==> [Some x <> y] * ??.
    Hint Resolve himp_disjoint.
    intros; unfold maybe_points_to; destruct y;
      [ apply (@himp_trans (x --> w * p -->? * [x <> p])) | sep fail ltac:(auto; try congruence) ].
    unfold ptsto_any. inhabiter; unpack_conc.
    apply (@himp_trans (p --> v0 * x --> w * [p <> x])). apply himp_disjoint. sep fail auto.
    sep fail ltac:(auto; try congruence).
  Qed.
  
  Lemma neqseg : forall p ls q ls',
    llseg' (Some p) None ls * llseg' q None ls' ==> [Some p <> q] * ??.
    destruct q; [ | sep fail ltac:(auto; try congruence) ].
    destruct ls; [ sep fail ltac:(auto; try congruence) | ].
    destruct ls'; [ sep fail ltac:(auto; try congruence) | ].
    simpl; inhabiter.
    apply (@himp_trans ((llseg' v0 None ls' * llseg' v None ls) * (p0 --> node t1 v0 * p --> node t0 v))); [ sep fail auto | ].
    apply (@himp_trans ([Some p <> Some p0] * (?? * ??))); [ | apply himp_frame; apply himp_split_any ].
    apply himp_comm_conc. apply himp_assoc_conc1. apply himp_split. sep fail auto. apply himp_comm_conc.
    apply (@himp_trans (p0 --> node t1 v0 * p --> node t0 v * [p0 <> p])); [ apply himp_disjoint | sep fail ltac:(auto; try congruence) ].
  Qed.

  Lemma somenone_seg : forall p ls,
    llseg' (Some p) None ls ==> [ls <> nil] * ??.
    destruct ls; sep fail auto; [ congruence | assert (t0 :: ls <> nil); [ firstorder | sep fail auto ] ].
  Qed.
  
  Lemma add_mlocineq x y (B : Set) (w:B) P Q :
    (Some x <> y -> (x --> w * y ~~>? * P ==> Q)) ->
    (x --> w * y ~~>? * P ==> Q).
    intros; apply (add_fact (@mlocineq x y B w) H).
  Qed.
  
  Lemma add_locineq x y (B C : Set) (w:B) (v:C) P Q :
    (x <> y -> (x --> w * y --> v * P ==> Q)) ->
    (x --> w * y --> v * P ==> Q).
    intros; apply (add_fact (@locineq x y B C w v) H).
  Qed.
  
  Lemma add_neqseg : forall p ls q ls' P Q,
    (Some p <> q -> 
      (llseg' (Some p) None ls * llseg' q None ls' * P ==> Q))
    -> llseg' (Some p) None ls * llseg' q None ls' * P ==> Q.
    intros; apply (add_fact (@neqseg _ _ _ _) H).
  Qed.

  Lemma add_somenoneseg : forall p ls P Q,
    (ls <> nil ->
      (llseg' (Some p) None ls * P ==> Q))
    -> llseg' (Some p) None ls * P ==> Q.
    intros; apply (add_fact (@somenone_seg _ _) H).
  Qed.

  Ltac add_mlocneq :=
    search_prem ltac:(idtac;
      match goal with
        | [|- ?x --> ?xv * ?P ==> _] =>
          match P with 
            | context H [?y ~~>?] => let z := context H [__] in 
              match goal with 
                | [ H: Some x = y -> False |- _ ] => fail 1
                | [ H: Some x <> y |- _ ] => fail 1
                | [ H: y <> Some x |- _ ] => fail 1
                | [ H: y = Some x -> False |- _ ] => fail 1
                | _ => apply (@himp_trans (x --> xv * y ~~>? * z)); 
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
                | _ => apply (@himp_trans (x --> xv * y --> yv * z)); 
                  [ solve [ sep fail auto ] | apply add_locineq; intros ]
              end
          end
      end).
  
  Ltac add_segne :=
    search_prem ltac:(idtac;fold llseg';
      match goal with
        | [|- llseg' ?X None ?XL * ?P ==> _] => 
          match P with 
            | context H [llseg' ?Y None ?YL] => let z := context H [__] in 
              match goal with 
                | [ H: X = Y -> False |- _ ] => fail 1
                | [ H: X <> Y |- _ ] => fail 1
                | [ H: Y = X -> False |- _ ] => fail 1
                | [ H: Y <> X |- _ ] => fail 1
                | _ => apply (@himp_trans (llseg' X None XL * llseg' Y None YL * z));
                  [ solve [ sep fail auto ] | apply add_neqseg; intros ]
              end
          end
      end).

  Ltac add_somenoneseg :=
    search_prem ltac:(idtac;fold llseg';
      match goal with
        | [|- llseg' (Some ?X) None ?XL * ?P ==> _] => 
          match goal with 
            | [ H: XL = nil -> False |- _ ] => fail 1
            | [ H: XL <> nil |- _ ] => fail 1
            | [ H: nil = XL -> False |- _ ] => fail 1
            | [ H: nil <> XL |- _ ] => fail 1
            | _ => apply add_somenoneseg; intros
          end
      end).
  
  Ltac ondemand_subst := idtac;
    repeat match goal with 
             | [ H : ?X = ?Y |- context[?X] ] => 
               match Y with 
               | [_]%inhabited => fail 1
                 | _ => rewrite -> H
             end
             | [ H : [?X]%inhabited = [?Y]%inhabited |- context[?Y] ] =>
               let p := fresh "eq" in
                 progress (pose (p := pack_injective H); (rewrite <- p; clear p || clear p))
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

  Ltac expander := add_segne || add_somenoneseg || add_mlocneq || add_locneq.

  Ltac simplr'' := (apply combine' || congruence || discriminate || reflexivity 
    || (simpl; expander || apply combine (** || apply empty_seg **)
    || match goal with
         | [ H : ?X = ?X |- _ ] => clear H
         | [ H : Some ?X = Some ?Y |- _ ] => extend_eq X Y ltac:(inversion H)
         | [ H : ?X = Some ?Y |- _ ] => 
           match X with 
             | Some _ => fail 1
             | _ => rewrite -> H
           end
         | [ H : next _ = None |- _ ] => rewrite -> H
         | [ H : next _ = Some _ |- _ ] => rewrite -> H
         | [ H : ?X = None |- context[?X ~~>?] ] => rewrite -> H
         | [ H : None = ?X |- context[?X ~~>?] ] => rewrite <- H
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
             | context[llseg' ?X ?X ?Y] => destruct Y; [ discriminate | ]
           end
           || match CONC with
                | context [llseg' _ _ (match ?LS with 
                                        | nil => _
                                        | _ :: _ => _
                                      end)] =>
                  match goal with
                    | [ H : LS <> nil |- _ ] => destruct LS; [ discriminate | ]
                    | [ H : head LS = Some _ |- _ ] => 
                      destruct LS; [ pose (head_some_nonil H); discriminate | ]
                  end 
                | context [llseg' _ _ ?LS] =>
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
         | [ H : ?V = node ?D ?N |- ?D = data ?V ] => rewrite -> H; reflexivity
       end)).

  Ltac simplr := repeat simplr''.

  Ltac llseg'_unfolding := 
    match goal with 
      [ |- ?T ==> _ ] =>
      match T with
        | llseg' _ _ nil => apply llseg'_unfold_nil
        | llseg' (Some _) _ (_ :: _) => apply llseg'_unfold_some_cons
        | llseg' (Some _) _ _ => apply llseg'_unfold_some; try solve [congruence]
        | llseg' _ _ (_ :: _) => apply llseg'_unfold_cons
        | llseg' ?p ?p _ => apply llseg'_unfold_same
        | llseg' None _ _ => apply llseg'_unfold_head_none
        | llseg' _ None _ => apply llseg'_unfold_tail_none ; solve [congruence]
      end
    end.

  Ltac unfolder := simpl_prem ltac:(idtac; llseg'_unfolding).

  Ltac simp_prem := discriminate || (repeat (ondemand_subst || unfolder || expander)).

  Ltac t := unfold llist'; simpl_IfNull; sep simp_prem simplr; sep fail auto.
  Ltac f := fold llseg'; fold llist'.

  Ltac rsep expander tac := unfold llist'; intros;
    try equater; try inhabiter; try unpack_conc; try canceler; try expander;
      repeat match goal with
               | [ H1 : ?X = [?Y]%inhabited, H2 : inhabit_unpack ?X ?XV = [?Z]%inhabited |- _ ==> ?CONC ] => 
                 match CONC with
                 | context[Z] =>
                   let l := fresh "eq" in
                     rewrite -> H1 in H2; simpl in H2
                 end
             end; ondemand_subst; canceler;
      solve [ sep fail idtac | tac ].
  Debug Off.
  (** Implementation *********************************************************)
  Definition empty' : STsep __ (fun r:LinkedList' => llseg' r None nil).
    refine ({{Return None}});
      t.  
  Qed.

  Definition cons' : forall (v : A) (r : LinkedList') (q : [LinkedList'])
    (m : [list t]),
    STsep (q ~~ m ~~ llseg' r q m * q ~~>?)
          (fun r:LinkedList' => 
              q ~~ m ~~ llseg' r q (v :: m) * q ~~>?).
    refine (fun v r q m =>
      l <- New (node v r);
      {{ Return (Some l) }});
      t.
  Qed.

  Definition single' : forall (v : t),
    STsep __ (fun r:LinkedList' => llseg' r None (v :: nil)).
    refine (fun v => {{ cons' v None [None] [nil] }});
      t.
  Qed.

  Definition freeHead' : forall (p : LinkedList') (q : [LinkedList']) (b : [t])
    (ls : [list t]),
    STsep (ls ~~ q ~~ b ~~ llseg' p q (b :: ls))
          (fun r => ls ~~ q ~~ llseg' r q ls).
    refine (fun p q b ls =>
      IfNull p Then {{!!!}}
      Else nde <- !p;
           Free p;;
           {{Return (next nde)}});
    t.
  Qed.

  Definition freeList' : forall (p' q : LinkedList') (ls' : [list t]),
    STsep (ls' ~~ llseg' p' q ls')
          (fun _:unit => __).
    refine (fun p' q ls' =>
      Fix2 (fun p ls => ls ~~ llseg' p q ls)
           (fun p ls (_:unit) => __)
           (fun self p ls =>
             if ptr_eq' p q then 
               {{Return tt}}
             else
               IfNull p Then
                 {{!!!}}
               Else
                 nde <- !p;
                 Free p;;
                 self (next nde) (ls ~~~ tail ls))
           p' ls');
    clear self; t.
  Qed.

  Definition elements' : forall (p q : LinkedList') (ls : [list A]),
    STsep (ls ~~ llseg' p q ls)
          (fun r:list A => ls ~~ [r = ls] * llseg' p q ls).
    refine (fun p q ls =>
      Fix2 (fun p ls => ls ~~ llseg' p q ls)
           (fun p ls (r : list A) => ls ~~ [r = ls] * llseg' p q ls)
           (fun self p ls =>
             if ptr_eq' p q then
               {{Return nil}}
             else 
               IfNull p Then
                 {{!!!}}
               Else 
                 nde <- !p;
                 rr <- self (next nde) (ls ~~~ tail ls) <@> (ls ~~ p --> nde * [head ls = Some (data nde)]);
                 {{Return (data nde :: rr)}})
           p ls);
    try clear self; solve [ t ].
  Qed.

  Section append.

    Ltac q := sep fail simplr; 
      try match goal with
            | [ |- _ ==> ?CONC ] => 
              match CONC with 
                | context [llseg' _ _ (?X ++ _)] => destruct X
              end
          end; sep fail simplr.
    
    Definition append_help' : forall (pr' : ptr) (nde' : Node) (q : LinkedList')
      (lsp' lsq : [list t]),
      STsep (lsp' ~~ lsq ~~ pr' --> nde' * llist' (next nde') lsp' * llist' q lsq)
            (fun _:unit => lsp' ~~ lsq ~~ Exists r :@ LinkedList', 
                pr' --> node (data nde') r * llist' r (lsp' ++ lsq)).
      refine (fun pr' nde' q lsp' lsq =>
        Fix3 (fun pr nde lsp => 
               lsp ~~ lsq ~~ pr --> nde * llist' (next nde) lsp * llist' q lsq)
             (fun pr nde lsp (_:unit) => 
               lsp ~~ lsq ~~ Exists r :@ LinkedList', pr --> node (data nde) r * 
               llist' r (lsp ++ lsq))
             (fun self pr nde lsp =>
               IfNull (next nde) As p Then
                 {{pr ::= node (data nde) q}}
               Else 
                 nde' <- !p;
                 {{self p nde' (lsp ~~~ tail lsp) <@> _}})
             pr' nde' lsp');
      solve [ rsep simp_prem q ].
    Qed.

    Definition append' : forall (p q : LinkedList') (lsp lsq : [list t]), 
      STsep (lsp ~~ lsq ~~ llist' p lsp * llist' q lsq)
            (fun r:LinkedList' => lsp ~~ lsq ~~ llist' r (lsp ++ lsq)).
      refine (fun p q lsp lsq =>
        IfNull p As p' Then
          {{Return q}}
        Else 
          nde <- !p';
          append_help' p' nde q (lsp ~~~ tail lsp) lsq <@> _;;
          {{Return p}});
      rsep simp_prem q.
    Qed.

  End append.

  Definition copy' : forall (p' q : LinkedList') (ls' : [list t]),
    STsep (ls' ~~ llseg' p' q ls' * q ~~>?)
          (fun r:LinkedList' => ls' ~~ llseg' p' q ls' * llseg' r q ls' * q ~~>?).
    refine (fun p' q ls' =>
      Fix2 (fun p ls   => ls ~~ llseg' p q ls * q ~~>?)
           (fun p ls r => ls ~~ llseg' p q ls * llseg' r q ls * q ~~>?)
           (fun self p ls =>
             if ptr_eq' p q then
               {{Return q}}
             else
               IfNull p Then
                 {{!!!}}
               Else 
                 nde <- !p;
                 rr <- self (next nde) (ls ~~~ tail ls) <@> _;
                 res <- cons' (data nde) rr [q] (ls ~~~ tail ls) <@> _;
                 {{Return res}}) p' ls');
    clear self; solve [ rsep simp_prem simplr | t ].
  Qed.

  Definition insertAt_help' : forall (p' : ptr) (idx' : nat) (a : A) 
    (ls' : [list t]),
    STsep (ls' ~~ llist' (Some p') ls')
          (fun _:unit => 
              ls' ~~ llist' (Some p') (insertAt_model ls' a (S idx'))).
    refine (fun p' idx' a ls' =>
      Fix3 (fun p ls idx => ls ~~ llist' (Some p) ls)
           (fun p ls idx (_:unit) =>
             ls ~~ llist' (Some p) (insertAt_model ls a (S idx)))
           (fun self p ls idx =>
             nde <- !p;
             if eq_nat_dec 0 idx then
               nelem <- New (node a (next nde));
               p ::= node (data nde) (Some nelem);;
               {{Return tt}}
             else
               IfNull next nde As nxt Then 
                 nelem <- New (node a (next nde));
                 p ::= node (data nde) (Some nelem);;
                 {{Return tt}}
               Else
                 {{self nxt (ls ~~~ tail ls) (pred idx) <@> 
                     (ls ~~ p --> nde * [head ls = Some (data nde)])}})
           p' ls' idx');
    clear self; solve [ t | t; destruct idx; t ].
  Qed.

  Definition insertAt' : forall (p : LinkedList') (a : t) (idx : nat)
    (ls : [list t]),
    STsep (ls ~~ llist' p ls)
          (fun r:LinkedList' => ls ~~ llist' r (insertAt_model ls a idx)).
    refine (fun p a idx ls =>
      IfNull p Then 
        {{ cons' a p [None] ls <@> (ls ~~ [ls = nil]) }}
      Else 
        if eq_nat_dec idx 0 then
          {{ cons' a (Some p) [None] ls <@> __ }}
        else
          insertAt_help' p (pred idx) a ls <@> __;;
          {{ Return (Some p) }});
    solve [ t | destruct idx; t ].
  Qed.

  Section Process.

    Ltac q := t;
      match goal with 
        | [ |- context[llseg' _ _ (process_model ?X _)] ] => 
          match X with
            | tail _ => fail 1
            | _ => destruct X;
              [ match goal with
                  | [ H : head nil = Some _ |- _ ] => inversion H
                end
              | t; match goal with
                     | [ H : _ = Keep _ |- _ ] => rewrite H
                     | [ H : _ = Del _ |- _ ] => rewrite H
                     | [ H : _ = Update _ |- _ ] => rewrite H
                   end; t ]
          end
      end.

    Definition process_help' : forall (prev' : ptr) (prev_a' : t) (up : t -> action t)
      (p' q : LinkedList') (ls' : [list A]),
      STsep (ls' ~~ llseg' p' q ls' * prev' --> node prev_a' p')
            (fun (_:unit) => ls' ~~ Exists r :@ LinkedList', 
                llseg' r q (process_model ls' up) * prev' --> node prev_a' r).
      refine (fun prev' prev_a' up p' q ls' =>
        Fix4 (fun prev prev_a p ls => ls ~~ llseg' p q ls * prev --> node prev_a p)
             (fun prev prev_a p ls (_:unit) => ls ~~ Exists r :@ LinkedList', 
               llseg' r q (process_model ls up) * prev --> node prev_a r)
             (fun self prev prev_a p ls =>
               if ptr_eq' p q then
                 {{ Return tt }}
               else
                 IfNull p As p' Then
                   {{ !!! }}
                 Else
                   nde <- !p';
                   match up (data nde) as act 
                     return STsep (ls ~~ llseg' (next nde) q (tail ls) * prev --> node prev_a (Some p') * 
                                    p' --> node (data nde) (next nde) * [up (data nde) = act] * [head ls = Some (data nde)])
                                  (fun (_:unit) => ls ~~ Exists r :@ LinkedList', 
                                    llseg' r q (process_model ls up) * prev --> node prev_a r)
                 with
                 | Keep => 
                   {{self p' (data nde) (next nde) (ls ~~~ tail ls) <@> 
                     (ls ~~ [head ls = Some (data nde)] * [p = Some p'] * 
                       prev --> node prev_a p * [up (data nde) = Keep t])}}
                 | Del =>
                   prev ::=  node prev_a (next nde);; 
                   Free p';;
                   {{self prev prev_a (next nde) (ls ~~~ tail ls) <@> 
                     (ls ~~ [head ls = Some (data nde)] * [p = Some p'] * [up (data nde) = Del t])}}
                 | Update val' =>
                   p' ::= node val' (next nde);;
                   {{self p' val' (next nde) (ls ~~~ tail ls) <@>
                     (ls ~~ prev --> node prev_a p * [head ls = Some (data nde)] * [up (data nde) = Update val'])}}
               end
      ) prev' prev_a' p' ls');
      solve [ q ].
    Qed.

    Definition process' : forall (p q : LinkedList') (up : A -> action t) (ls : [list A]),
      STsep (ls ~~ llseg' p q ls)
            (fun r:LinkedList' => ls ~~ llseg' r q (process_model ls up)).
      refine (fun p q up ls =>
        if ptr_eq' p q then
          {{ Return p }}
        else
          IfNull p As p' Then
            {{ !!! }}
          Else
            nde <- !p';
            {{ process_help' p' (data nde) up (next nde) q (ls ~~~ tail ls) <@> 
                 (ls ~~ [head ls = Some (data nde)]) }};;
            match up (data nde) as act 
              return STsep (ls ~~ Exists r :@ LinkedList', p' --> node (data nde) r * 
                              llseg' r q (process_model (tail ls) up) * [head ls = Some (data nde)] * [up (data nde) = act])
                           (fun (r:LinkedList') => ls ~~ llseg' r q (process_model ls up))
              with
              | Keep => {{ Return p }}
              | Del =>
                nde <- !p';
                Free p';;
                {{ Return (next nde) }}
              | Update val' =>
                nde <- !p';
                p' ::= node val' (next nde);;
                {{ Return (Some p') }}
            end); 
      solve [ q ].
    Qed.
  End Process.

  Section Fold.

    Definition foldr_f' : forall (T : Type) (p q : LinkedList') (f : A -> T -> T) (ls : [list A]) (t : T),
      STsep (ls ~~ llseg' p q ls)
            (fun r:T => ls ~~ llseg' p q ls * [r = foldr_model f ls t]).
      refine (fun T p q f ls t =>
        Fix2 (fun p ls => ls ~~ llseg' p q ls)
             (fun p ls res => ls ~~ llseg' p q ls * [res = foldr_model f ls t])
             (fun self p ls =>
               if ptr_eq' p q then
                 {{ Return t }}
               else
                 IfNull p As p' Then
                   {{ !!! }}
                 Else
                   nde <- !p';
                   r <- self (next nde) (ls ~~~ tail ls) <@> (ls ~~ p' --> nde * [head ls = Some (data nde)]) ;
                   {{ Return (f (data nde) r) }})
             p ls); try clear self;
      solve [ t ].
    Qed.

    Definition foldl' : forall (T  : Type) (p q : LinkedList') (I : T -> list A -> hprop)
      (c : forall (a : T) (v : A) (m : [list A]),
           STsep (m ~~ I a m)
                 (fun a':T => m ~~ I a' (m ++ (v :: nil))))
      (ls' : [list A]) (a : T),
      STsep (ls' ~~ llseg' p q ls' * I a nil)
            (fun r:T => ls' ~~ llseg' p q ls' * I r ls').
      refine (fun T p q I c ls' a =>
        {{ Fix4 (fun acc beg p ls => ls' ~~ beg ~~ ls ~~ llseg' p q ls * I acc beg * [ls' = beg ++ ls])
                (fun _   beg p ls res => ls' ~~ beg ~~ ls ~~ llseg' p q ls * I res ls' * [ls' = beg ++ ls])
                (fun self acc beg p ls =>
                  if ptr_eq' p q then
                    {{ Return acc }}
                  else
                    IfNull p As p' Then
                      {{ !!! }}
                    Else
                      nde <- !p' ;
                      acc' <- @c acc (data nde) beg <@> (ls ~~ beg ~~ ls' ~~ [head ls = Some (data nde)] * llseg' (next nde) q (tail ls) * 
                                                           [ls' = beg ++ ls] * p' --> nde) (** sep forgets information **);
                      res <- self acc' (inhabit_unpack2 beg ls (fun beg ls => match ls with 
                                                                                | nil => nil
                                                                                | a :: b => beg ++ (a :: nil)
                                                                              end)) (next nde) (ls ~~~ tail ls) <@> (ls ~~ [head ls = Some (data nde)] * _) ;
                      {{Return res}} )
                a (inhabits (@nil A)) p ls'}}); try clear self;
      solve [ t 
            | t; rewrite app_nil; t
            | t; rewrite app_ass; t
            | t; destruct x; simpl in *; [ discriminate | rewrite app_ass; simpl in *; t ]].
    Qed.

    Definition foldr' : forall (T  : Type) (p q : LinkedList') (I : T -> list A -> hprop)
      (c : forall (a : T) (v : A) (m : [list A]),
           STsep (m ~~ I a m)
                 (fun a':T => m ~~ I a' (v :: m)))
      (ls' : [list A]) (a : T),
      STsep (ls' ~~ llseg' p q ls' * I a nil)
            (fun r:T => ls' ~~ llseg' p q ls' * I r ls').
      refine (fun T p q I c ls' a =>
        {{ Fix2 (fun p ls => ls ~~ llseg' p q ls * I a nil)
                (fun p ls res => ls ~~ llseg' p q ls * I res ls)
                (fun self p ls =>
                  if ptr_eq' p q then
                    {{ Return a }}
                  else
                    IfNull p As p' Then
                      {{ !!! }}
                    Else
                      nde <- !p' ;
                      rr  <- self (next nde) (ls ~~~ tail ls) <@> ((ls ~~ [head ls = Some (data nde)]) * _) ;
                      res <- @c rr (data nde) (ls ~~~ tail ls) <@> (ls ~~ llseg' p q ls * [head ls = Some (data nde)]);
                      {{Return res}})
                p ls'}}); try clear self;
      solve [ t ].
    Qed.

  End Fold.


  Section Remove.
    Variable eq_a : forall (a b : A), {a = b} + {a <> b}.
    Ltac q := t; 
      match goal with
        | [ |- context[llseg' _ _ (filter_model _ ?X _)] ] => 
          match X with
            | tail _ => fail 1
            | _ => destruct X; simpl; 
              try match goal with
                    | [ |- context[eq_a ?X ?Y] ] => destruct (eq_a X Y)
                  end; t
          end
        | [ |- context[llseg' _ _ (removeFirst_model _ ?X _)] ] => 
          match X with
            | tail _ => fail 1
            | _ => destruct X; simpl; 
              try match goal with
                    | [ |- context[eq_a ?X ?Y] ] => destruct (eq_a X Y)
                  end; t
          end
      end.

    Definition removeFirst_help' : forall (pr' : ptr) (p' : LinkedList') 
      (pr_a' a : t) (ls' : [list t]),
      STsep (ls' ~~ llist' p' ls' * pr' --> node pr_a' p')
            (fun _:unit => ls' ~~ Exists p'' :@ LinkedList', 
                llist' p'' (removeFirst_model eq_a ls' a) * pr' --> node pr_a' p'').
      refine (fun pr' p' pr_a' a ls' =>
        Fix4 (fun pr pr_a p ls => ls ~~ llist' p ls * pr --> node pr_a p)
             (fun pr pr_a p ls r => ls ~~ Exists p'' :@ LinkedList', 
               llist' p'' (removeFirst_model eq_a ls a) * pr --> node pr_a p'')
             (fun self pr pr_a p ls =>
               IfNull p As p' Then
                 {{ Return tt }}
               Else nde <- !p';
                 if eq_a (data nde) a then 
                   pr ::=  node pr_a (next nde);;
                   Free p';;
                   {{ Return tt }}
                 else 
                   {{ self p' (data nde) (next nde) (ls ~~~ tail ls) <@> 
                        (ls ~~ [head ls = Some (data nde)] * [ls <> nil] * 
                          [p = Some p'] * pr --> node pr_a p) }}
             ) pr' pr_a' p' ls');
      clear self; q.
    Qed.

    Definition removeFirst' : forall (p : LinkedList') (a : t) (ls : [list t]),
      STsep (ls ~~ llist' p ls)
            (fun r:LinkedList' => ls ~~ llist' r (removeFirst_model eq_a ls a)).
      refine (fun p a ls =>
        IfNull p As p' Then
          {{ Return p }}
        Else nde <- !p';
          if eq_a (data nde) a then 
            Free p';;
            {{ Return (next nde) }}
          else
            removeFirst_help' p' (next nde) (data nde) a (ls ~~~ tail ls) <@>
               (ls ~~ [head ls = Some (data nde)]);;
            {{ Return p }});
      q.
    Qed.

    Definition filter_help' : forall (pr' : ptr) (p' : LinkedList') (pr_a' a : t)
      (ls' : [list t]),
      STsep (ls' ~~ llist' p' ls' * pr' --> node pr_a' p')
            (fun (_:unit) => ls' ~~ Exists r :@ LinkedList', 
                llist' r (filter_model eq_a ls' a) * pr' --> node pr_a' r).
      refine (fun pr' p' pr_a' a ls' =>
        Fix4 (fun pr pr_a p ls => ls ~~ llist' p ls * pr --> node pr_a p)
             (fun pr pr_a p ls (_:unit) => ls ~~ Exists r :@ LinkedList', 
               llist' r (filter_model eq_a ls a) * pr --> node pr_a r)
             (fun self pr pr_a p ls =>
               IfNull p As p' Then
                 {{Return tt}}
               Else
                 nde <- !p';
                 if eq_a (data nde) a then 
                   pr ::=  node pr_a (next nde);; 
                   Free p';;
                   {{ self pr pr_a (next nde) (ls ~~~ tail ls) <@> 
                        (ls ~~ [head ls = Some (data nde)] * [p = Some p']) }}
                 else 
                   {{ self p' (data nde) (next nde) (ls ~~~ tail ls) <@> 
                        (ls ~~ [head ls = Some (data nde)] * [p = Some p'] * pr --> node pr_a p) }}
             ) pr' pr_a' p' ls');
      try clear self; q.
    Qed.
  
    Definition filter' : forall (p : LinkedList') (a : t) (ls : [list t]),
      STsep (ls ~~ llist' p ls)
            (fun r:LinkedList' => ls ~~ llist' r (filter_model eq_a ls a)).
      refine (fun p a ls =>
        IfNull p As p' Then 
          {{Return p}}
        Else
          nde <- !p';
          {{ filter_help' p' (next nde) (data nde) a (ls ~~~ tail ls) <@> 
              (ls ~~ [head ls = Some (data nde)]) }};;
          if eq_a (data nde) a then
            nde <- !p';
            Free p';;
            {{ Return (next nde) }}
          else
            {{ Return p }});
      q.
    Qed.

  End Remove.

  Definition HeapLinkedListSeg := mkList
    llseg' empty' cons' single' freeList' freeHead' append' copy'
    insertAt' elements' llseg'_unfold_nil removeFirst' filter' process' 
    foldr_f' foldl' foldr'.

End HeapLinkedList.

  