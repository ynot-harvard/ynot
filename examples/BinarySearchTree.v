(* A simple binary search tree implementation, implementing the finite map
 * interface. 
 *)
Require Import Ynot.
Require Import FiniteMap.

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

Module BinaryTreeModel(A : BINARY_TREE_ASSOCIATION).
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

  Ltac simpler := 
    repeat (progress ((repeat (
      match goal with
        | [H1: ?e, H2: ?e |- _] => clear H2 || clear H1
        | [H1: ?a = ?b, H2:?b = ?a |- _] => clear H2 || clear H1
        | [H: Some _ = Some _ |- _] => inversion H; clear H
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

  (* interactions of filter *)

  Lemma lookup_filter_gte(k1 k2:key_t)(l:alist_t) : 
    k1 < k2 -> lookup k1 (filter_gte k2 l) = lookup k1 l.
  Proof. induction l; t. Qed.

  Lemma lookup_filter_lte(k1 k2:key_t)(l:alist_t) : 
    k2 < k1 -> lookup k1 (filter_lte k2 l) = lookup k1 l.
  Proof. induction l; t. Qed.
  Hint Rewrite lookup_filter_gte using solve[t] : AssocListModel.
  Hint Rewrite lookup_filter_lte using solve[t] : AssocListModel.

  Lemma filter_lookup_none f k l : lookup k l = None -> lookup k (filter f l) = None.
  Proof. induction l; t. Qed.
  Hint Resolve filter_lookup_none.

  Lemma filter_perm f l l' : Permutation l l' -> Permutation (filter f l) (filter f l').
  Proof. induction 1; t; eauto. Qed.
  Hint Resolve filter_perm : AssocListModel.

  Lemma filter_distinct f l : distinct l -> distinct (filter f l).
  Proof. induction l; t. Qed.
  Hint Resolve filter_distinct : AssocListModel.

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

(*
  Lemma insert_filter_lte_lt k1 k2 (v:value_t k1) l : k1 < k2 -> (filter_lte k2 (insert v l)) = (filter_lte k2 l).
  Proof. unfold insert; induction l; t. Qed.

  Lemma insert_filter_gte_gt k1 k2 (v:value_t k1) l : k2 < k1 -> (filter_gte k2 (insert v l)) = (filter_gte k2 l).
  Proof. unfold insert; induction l; t. Qed.

  Lemma insert_filter_lte_eq k1 k2 (v:value_t k1) l : k1 = k2 -> (filter_lte k2 (insert v l)) = (filter_lte k2 l).
  Proof. unfold insert; induction l; t. Qed.

  Lemma insert_filter_gte_eq k1 k2 (v:value_t k1) l : k1 = k2 -> (filter_gte k2 (insert v l)) = (filter_gte k2 l).
  Proof. unfold insert; induction l; t. Qed.
*)    
  End BinaryTreeModel.
  
Module BinaryTree(BT : BINARY_TREE_ASSOCIATION). (* : FINITE_MAP with Module A := BT. *)
  Module A := BT.
  Module AL := BinaryTreeModel(BT).
  Import AL.
  
  Open Local Scope stsepi_scope.
  Open Local Scope hprop_scope.

  Module AT <: FINITE_MAP_AT with Module A:=A with Module AL:=AL.
    Module A := A.
    Module AL := AL.
    Import A AL.

  (* the imperative model *)
    Definition ref(A:Set) := ptr.

    (* A node in the binary tree *)
    Record node_t : Set := 
      Node { node_key : key_t ; node_value : value_t node_key ; 
        node_left : ptr ; node_right : ptr }.

    Definition n_left(n:node_t) : ref(option node_t) := node_left n.
    Definition n_right(n:node_t) : ref(option node_t) := node_right n.
   (* A binary tree is implemented as a ref to an optional node *)
    Definition fmap_t := ref(option node_t).

  (* The rep predicate -- note that I had to call this rep' to avoid 
   * a problem exporting this from the module.  Anyway, when the list is
   * empty, the tree represents it only when it points to None.  When the
   * tree points to Some node with key k and value v, then looking up k in
   * the list should yield v, and the node's left and right sub-trees must  
   * represent the result of filtering out all keys less-than-or-equal/
   * greater-then-or-equal to k. *)
  Inductive rep' : fmap_t -> alist_t -> hprop := 
  | Rep_none : forall x, (x --> None(A:=node_t)) ==> rep' x nil_al
  | Rep_some : forall x k (v:value_t k) xleft xright l,
      x --> Some(Node v xleft xright) * 
      rep' xleft (filter_gte k l) * rep' xright (filter_lte k l)
      * [lookup k l = Some v]
      ==> rep' x l.

  Hint Constructors rep'.
  Definition rep := rep'.

  (* Unwind the definition of rep' when we know the node that the tree 
   * points to. *)
  Definition node_rep(nopt:option node_t)(l:alist_t) : hprop := 
    match nopt with
    | None => [l = nil_al]
    | Some n => rep' (node_left n) (filter_gte (node_key n) l) * 
      rep' (node_right n) (filter_lte (node_key n) l) * 
      [lookup (node_key n) l = Some (node_value n)]
    end.

  (* Used to eliminate rep' from a premise in an implication *)
  Lemma repinv(x:fmap_t)(l:AL.alist_t)(Q R:hprop) : 
    (x --> None(A:=node_t) * [l = nil_al] * Q ==> R) -> 
    (forall k v xl xr, 
      (x --> Some(Node v xl xr) * rep' xl (filter_gte k l) * 
        rep' xr (filter_lte k l) * [lookup k l = Some v]) * Q ==> R) -> 
    rep' x l * Q ==> R.
  Proof. intros x l Q R H1 H2 h H.
    destruct H as [h1 [h2 [H3 [H4 H5]]]]. 
    destruct H4. apply H1. exists h0. exists h2. sep fail auto.
    generalize h0 H. change (x --> None(A:=node_t) ==> 
    x --> None(A:=node_t) * [nil_al = nil_al]). sep fail auto.
    apply (H2 k v xleft xright). exists h0. eauto. 
  Qed.

  Lemma rep2node_prem(x:fmap_t)(l:AL.alist_t) P Q: 
   (Exists n :@ option node_t, x --> n * node_rep n l * P) ==> Q -> rep' x l * P ==> Q.
  Proof. intros; apply (himp_apply H); apply repinv; sep fail auto. Qed.

  Lemma rep2node_conc(x:fmap_t)(l:AL.alist_t) P Q: 
   P ==> (Exists n :@ option node_t, x --> n * node_rep n l * Q) -> P ==> rep' x l * Q.
  Proof. intros. eapply himp_trans. eexact H. sep fail auto. destruct v; sep fail auto. destruct n.
    pose (@Rep_some x node_key0 node_value0 node_left0 node_right0 l).  simpl.
    apply (himp_apply h). sep fail auto.
  Qed.

  End AT.

  Module T:=FINITE_MAP_T(A)(AT).
  Import A AT.
    
  Ltac unfolder := idtac; apply rep2node_prem.
  Ltac impsimpler := search_conc ltac:(apply rep2node_conc).
  Ltac t := unfold rep; unfold_local; repeat progress 
    (sep ltac:(idtac; search_prem unfolder) AL.simpler; auto; impsimpler; autorewrite with AssocListModel; simpler).

  (* The new operation: just allocate a ref and initialize it with None *)
  Definition new : T.new.
    refine( f <- New (None(A:=node_t))
          ; {{ Return f }})
    ; t. Defined.

  (* The free operation -- we must loop over the tree and free each node *)
  Definition free_loop(free : T.free) : T.free.
    intros free f l.
    refine (n <- ! f 
         ; Free f  
         ;; IfNull n 
              Then {{Return tt}}
              Else free (n_left n) (l ~~~ (filter_gte (node_key n) l)) <@> _
                ;; free (n_right n) (l ~~~ (filter_lte (node_key n) l)))
    ; t; t. Qed.

  Definition free : T.free := Fix2 _ _ free_loop.

  Definition lookup_loop (lookup_loop:T.lookup) : T.lookup.
    intros lookup_loop f k l.

    refine (n <- ! f
         ; IfNull n
           Then {{ Return None }}
           Else let l_left := (l ~~~ (filter_gte (node_key n) l)) in
                let l_right := (l ~~~ (filter_lte (node_key n) l)) in
                Compare BT.key_cmp k (node_key n)
                WhenLt {{lookup_loop (node_left n) k l_left <@> _
                  <@> (f --> Some n * (l_right ~~ rep' (node_right n) l_right) * 
                    (l ~~ [AL.lookup (node_key n) l = Some (node_value n)]))}}
                WhenEq {{Return Some(AL.coerce _ (node_value n))}}
                WhenGt {{lookup_loop (node_right n) k l_right
                  <@> (f --> Some n * (l_left ~~ rep' (node_left n) l_left) *
                    (l ~~ [AL.lookup (node_key n) l = Some (node_value n)]))}})
  ; t. Qed.

  Definition lookup : T.lookup := Fix3 _ _ lookup_loop.

  Definition insert_loop (insert_loop:T.insert) : T.insert.
    intros insert_loop f k v l.
    
    refine 
         (n <- ! f ; 
          IfNull n
          Then nleft <- New None(A:=node_t) 
             ; nright <- New None(A:=node_t)
             ; {{ f ::= Some (Node v nleft nright) }}
          Else let l_left := (l ~~~ (filter_gte (node_key n) l)) in
               let l_right := (l ~~~ (filter_lte (node_key n) l)) in
            Compare BT.key_cmp k (node_key n)
            WhenLt {{insert_loop (node_left n) k v l_left
              <@> (f --> Some n * (l_right ~~ rep' (node_right n) l_right) * 
                (l ~~ [AL.lookup (node_key n) l = Some (node_value n)]))}}
            WhenEq {{ f ::= Some (Node v (node_left n) (node_right n)) }}
            WhenGt {{insert_loop (node_right n) k v l_right
              <@> (f --> Some n * (l_left ~~ rep' (node_left n) l_left) *
              (l ~~ [AL.lookup (node_key n) l = Some (node_value n)]))}}); 
         t.
  Qed.

  Definition insert : T.insert := (Fix4 _ _ _ _ _ _ insert_loop).

End BinaryTree.