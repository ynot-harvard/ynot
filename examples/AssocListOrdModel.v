Require Import Ynot.
Require Import AssocListModel.

Set Implicit Arguments.

Module Type BINARY_TREE_ASSOCIATION.
  Variable key_t : Set.
  Variable key_eq_dec : forall (k1 k2:key_t), {k1=k2} + {k1<>k2}.
  Notation "k1 =! k2" := (key_eq_dec k1 k2) (at level 70, right associativity).
  Variable key_lt : key_t -> key_t -> Prop.
  Notation "k1 < k2" := (key_lt k1 k2).
  Variable key_lt_imp_ne : forall k1 k2, k1 < k2 -> k1 <> k2.
  Variable key_lt_trans : forall k1 k2 k3, k1 < k2 -> k2 < k3 -> k1 < k3.
  Variable key_cmp : forall (k1 k2:key_t), {k1 < k2} + {k1 = k2} + {k2 < k1}.
  Variable value_t : key_t -> Set.
End BINARY_TREE_ASSOCIATION.

Module AssocListOrdModel(A : BINARY_TREE_ASSOCIATION).
  Import A.
  Module AL := AssocList(A).
  Export AL.

  (* generally useful tactics *)
  Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ => idtac
  end.

  Ltac extend pf :=
    let t := type of pf in
      notHyp t; generalize pf; intro.
  
  Definition key_lte_dec k1 k2 : {k1 < k2 \/ k1=k2} + {k2 < k1}
    := match key_cmp k1 k2 with
         | inleft (left k1_lt_k2) => left _ (or_introl _ k1_lt_k2)
         | inleft (right k1_eq_k2) => left _ (or_intror _ k1_eq_k2)
         | inright k1_gt_k2 => right _ k1_gt_k2
       end.
  Notation "k1 <=! k2" := (key_lte_dec k1 k2) (at level 70, right associativity).

  Notation "'Compare' e 'WhenLt' e1 'WhenEq' e2 'WhenGt' e3" :=
    (match e with
       | inleft cm => if cm then e1 else e2
       | inright _ => e3
     end) (no associativity, at level 90).

  Fixpoint filter (p : key_t -> bool) (l : alist_t) {struct l}:= 
    match l with
      | nil => nil
      | (k,,v)::l' => 
        if (p k) then filter p l' else (k,,v)::(filter p l') 
    end.

  Notation "'filter_lte' k" := 
    (filter (fun k' => if k' <=! k then true else false)) (no associativity, at level 10).

  Notation "'filter_gte' k" := 
    (filter (fun k' => if k <=! k' then true else false)) (no associativity, at level 10).

  (* generally, we will have that lookup k = Some v in pivot *)
  Notation "k 'filters' l" := ((filter_lte k l) ++ (filter_gte k l)) (no associativity, at level 10).
  Definition pivot k v l := ((k,,v) :: ((k filters l))).
  Implicit Arguments pivot [].


  Ltac simpler := 
    repeat (progress ((repeat (
      match goal with
        | [H1: ?e, H2: ?e |- _] => clear H2 || clear H1
        | [H1: ?a = ?b, H2:?b = ?a |- _] => clear H2 || clear H1
        | [ |- context[if ?e1 <=! ?e2 then _ else _] ] => 
          destruct (e1 <=! e2) ; try congruence ; try solve [assert False; intuition]; try subst
        | [ |- context[if ?e1 =! ?e2 then _ else _] ] => 
          destruct (e1 =! e2) ; try congruence ; try solve [assert False; intuition]; try subst
        | [ |- context[if ?e1 then _ else _] ] => 
          case_eq (e1) ; intros; try congruence ; try solve [assert False; intuition]; try subst
        | [H1:?k1 < ?k2 |- _] => elim (key_lt_imp_ne H1); congruence
        | [H1:?k1 < ?k2, H2:?k2 < ?k3 |- _] => extend (key_lt_trans H1 H2)
      end)); AL.simpler)).

  Ltac t := repeat (progress (simpler; simpl in *; auto; intuition; autorewrite with AssocListModel)).

  (* maybe I should just use key_cmp directly? *)
  Lemma key_cmp_direct : forall k k', (if k <=! k' then true else false) = (if key_cmp k k' then true else false).
    intros. destruct (key_cmp k k'); t. 
  Qed.

  Lemma key_lt_imp_ne' : forall k1 k2, k1 < k2 -> k2 <> k1.
  Proof. intros; pose (key_lt_imp_ne H); auto. Qed.
  Hint Resolve key_lt_imp_ne key_lt_imp_ne'.
  
  (* interactions of filter *)
  Lemma lookup_filter_gte_eq(k:key_t)(l:alist_t) : 
    lookup k (filter_gte k l) = None.
  Proof. induction l; t. Qed.

  Lemma lookup_filter_lte_eq(k:key_t)(l:alist_t) : 
    lookup k (filter_lte k l) = None.
  Proof. induction l; t. Qed.

  Lemma lookup_filter_gte(k1 k2:key_t)(l:alist_t) : 
    k1 < k2 -> lookup k1 (filter_gte k2 l) = lookup k1 l.
  Proof. induction l; t. Qed.

  Lemma lookup_filter_lte(k1 k2:key_t)(l:alist_t) : 
    k2 < k1 -> lookup k1 (filter_lte k2 l) = lookup k1 l.
  Proof. induction l; t. Qed.
  Hint Rewrite lookup_filter_gte_eq lookup_filter_lte_eq : AssocListModel.
  Hint Rewrite lookup_filter_gte lookup_filter_lte using solve[t] : AssocListModel.

  Lemma filter_lookup_none f k l : lookup k l = None -> lookup k (filter f l) = None.
  Proof. induction l; t. Qed.
  Hint Resolve filter_lookup_none.

  Lemma filter_lookup_some_false f k v l : lookup k (filter f l) = Some v -> f k = false.
  Proof. induction l; t. Qed.

  Lemma filter_lookup_some f k v l : lookup k (filter f l) = Some v -> lookup k l = Some v.
  Proof. induction l; t; [| destruct (f x); t].
    case_eq (f k); intro eq1; rewrite eq1 in H0; t.
    rewrite (filter_lookup_some_false _ _ H0) in eq1. congruence.
  Qed.

  Lemma filter_perm f l l' : Permutation l l' -> Permutation (filter f l) (filter f l').
  Proof. induction 1; t; eauto. Qed.
  Hint Resolve filter_perm.

  Lemma filter_distinct f l : distinct l -> distinct (filter f l).
  Proof. induction l; t. Qed.
  Hint Resolve filter_distinct.

  Lemma filter_remove f k l : (filter f (remove k l)) = remove k (filter f l).
  Proof. induction l; t. Qed.
  Hint Rewrite filter_remove : AssocListModel.

  Lemma filter_nil f : filter f nil_al = nil_al.
  Proof. auto. Qed.
  Hint Rewrite filter_nil : AssocListModel.

  Lemma remove_filter_lte_lt k1 k2 l : k1 < k2 -> remove k1 (filter_lte k2 l) = filter_lte k2 l.
  Proof. induction l; t. Qed.
  Hint Rewrite remove_filter_lte_lt using solve[t] : AssocListModel.

  Lemma remove_filter_gte_gt k1 k2 l : k2 < k1 -> remove k1 (filter_gte k2 l) = filter_gte k2 l.
  Proof. induction l; t. Qed.
  Hint Rewrite remove_filter_gte_gt using solve[t] : AssocListModel.

  Lemma remove_filter_lte_eq k1 k2 l : k1 = k2 -> remove k1 (filter_lte k2 l) = filter_lte k2 l.
  Proof. induction l; t. Qed.
  Hint Rewrite remove_filter_lte_eq using solve[t] : AssocListModel.

  Lemma remove_filter_gte_eq k1 k2 l : k1 = k2 -> remove k1 (filter_gte k2 l) = filter_gte k2 l.
  Proof. induction l; t. Qed.
  Hint Rewrite remove_filter_gte_eq using solve[t] : AssocListModel.  

  Lemma insert_filter_lte_gt k1 k2 (v:value_t k1) l : k2 < k1 -> (filter_lte k2 (insert v l)) = insert v (filter_lte k2 l).
  Proof. unfold insert; induction l; t. Qed.
  Hint Rewrite insert_filter_lte_gt using solve[t] : AssocListModel.

  Lemma insert_filter_gte_lt k1 k2 (v:value_t k1) l : k1 < k2 -> (filter_gte k2 (insert v l)) = insert v (filter_gte k2 l).
  Proof. unfold insert; induction l; t. Qed.
  Hint Rewrite insert_filter_gte_lt using solve[t] : AssocListModel.

  Lemma filter_swap f1 f2 l : filter f1 (filter f2 l) = filter f2 (filter f1 l).
  Proof. induction l; t. Qed.

  (* generally, we will have that lookup k = Some v *)
  Lemma pivot_distinct : forall k v l, distinct l -> distinct (pivot k v l).
  Proof. Hint Rewrite lookup_app_none1 using solve[t] : AssocListModel.
    intros; constructor; t. induction l; t.
    eapply distinct_perm. apply Permutation_cons_app; apply Permutation_refl.
    constructor; t.
  Qed.

  Lemma filter_lookup_false_eq f k l : f k = false -> lookup k (filter f l) = lookup k l.
  Proof. induction l; t. Qed.

  Lemma lookup_filters k k' l : k <> k' -> lookup k l = lookup k (k' filters l).
  Proof. Hint Rewrite lookup_app_none1 filter_lookup_none using solve[t] : AssocListModel.
    intros. remember (lookup k l) as x. destruct x; t.
    remember (lookup k (filter_lte k' l)) as x. destruct x.
    rewrite (filter_lookup_some _ _ (sym_eq Heqx0)) in Heqx; t. 
    symmetry. eapply lookup_app_some1; eauto.
    t. rewrite filter_lookup_false_eq; t.
    rewrite filter_lookup_false_eq in Heqx0; t. 
  Qed.

  Lemma pivot_perm k v l : distinct l -> lookup k l = Some v -> Permutation l (pivot k v l).
  Proof. Hint Resolve lookup_filters. intros. 
         apply distinct_look_perm; t.
         pose (pivot_distinct v l H); firstorder.
  Qed.

  Lemma remove_perm_filters k v l: distinct l -> lookup k l = Some v -> 
    Permutation (remove k l) ((filter_lte k l)++(filter_gte k l)).
  Proof. intros. pose (remove_perm k (pivot_perm l H H0)).
    eapply perm_trans. apply p. t.
  Qed.
 
End AssocListOrdModel.