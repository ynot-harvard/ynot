(* This files defines a module for an association type with a decidable equality on the keys
  and an AssocList functor that provides a basic model of a functional association list based on
  the provided association.  It is used as the model for FiniteMaps *)

Require Import Ynot.
Set Implicit Arguments.

(*************************************************************************)
(* Module that defines an association with decidable equality on the key *)
(*************************************************************************)
Module Type ASSOCIATION.
  Variable key_t : Set.
  Variable value_t : key_t -> Set.  (* note that value types depend on the keys *)
  Variable key_eq_dec : forall (k1 k2:key_t), {k1 = k2} + {k1 <> k2}.
  Notation "k1 =! k2" := (key_eq_dec k1 k2) (at level 70, right associativity).
End ASSOCIATION.

(*********************************************)
(* The functional model -- association lists *)
(*********************************************)
Module AssocList(A : ASSOCIATION).
Require Export List.
  Export A.
  Notation "( x ,, y )" := (@existT _ _ x y) : core_scope.
  Notation "` x" := (projT1 x) (at level 10): core_scope.

  Require Import Eqdep_dec.
  Module DecKey : DecidableType with Definition U:=A.key_t with Definition eq_dec:=A.key_eq_dec. 
    Definition U := A.key_t.
    Definition eq_dec := A.key_eq_dec.
  End DecKey.
  Module DecKeyFacts := DecidableEqDep(DecKey).

  Definition key_eq_irr : (forall (k:A.key_t)(p:k = k), p = refl_equal k) := DecKeyFacts.UIP_refl.

  (* because of the dependency of values on keys, we don't just use normal lists *)
  Definition alist_t := list (sigT A.value_t).

  Definition nil_al := @nil (sigT A.value_t).
  Fixpoint remove(k:A.key_t)(l:alist_t) {struct l} : alist_t := 
    match l with
    | nil => nil
    | (k',, v')::l' => if k =! k' then remove k l'
                          else (k',, v')::(remove k l')
    end.

  Definition insert(k:A.key_t)(v:A.value_t k)(l:alist_t) := (k,, v)::(remove k l).
  Lemma insert_eq k v l : (k,,v)::(remove k l) = insert v l.
  Proof. reflexivity. Qed.
  Hint Rewrite insert_eq : AssocListModel.

  Definition coerce(k1 k2:A.key_t)(H:k1 = k2)(v:A.value_t k1) : A.value_t k2.
    intros. rewrite H in v. apply v.
  Defined.

  Ltac uncoerce :=
    let rev_hyps := repeat 
      match goal with
        | [H: _ = _ |- _ ] => 
          match goal with
            | [H2: context [H]|- _ ] => revert H2
          end 
      end 
      in let gen_eqs := repeat 
        match goal with
          | [H: _ = _ |- _ ] => 
            match goal with
              | [|- context [H]] => generalize H
            end 
        end 
        in let refl_eqs := repeat 
          match goal with
            [|- forall (x : ?a = ?a), _] => 
            let H2 := (fresh "H") in 
              intro H2; rewrite (key_eq_irr H2); clear H2
          end in
          rev_hyps; gen_eqs; subst; refl_eqs; simpl.

  Fixpoint lookup(k:A.key_t)(l:alist_t) {struct l} : option(A.value_t k) := 
    match l with
    | nil => None
    | (k',, v'):: l' => 
      match k' =! k with
      | left k_eq_k' => Some (coerce k_eq_k' v')
      | right k_neq_k' => lookup k l'
      end
    end.

    Fixpoint distinct (l:alist_t) : Prop :=
      match l with
        | nil => True
        | (k,,v)::ls => lookup k ls = None /\ distinct ls
      end.
    
    Ltac simpler := try discriminate; try uncoerce;
      repeat (progress ((repeat 
        match goal with
        | [H: _ = _ |- context [coerce ?pf _]] => equate pf H || equate pf (sym_eq H)
        | [H:?e = ?e |- _] => clear H
        | [|- context [match ?k1 =! ?k2 with 
                         | left _ => _ 
                         | right _ => _ end]] =>
        case_eq (k1 =! k2) ; intros; try congruence ; try solve [assert False; intuition]; try subst 
        | [H:context [match ?k1 =! ?k2 with 
                         | left _ => _ 
                         | right _ => _ end] |- _] =>
        destruct (k1 =! k2) ; try congruence ; try solve [assert False; intuition]; try subst
        |[H: sigT _ |- _] => destruct H
        |[|- ?a::_ = ?a::_ ]=> f_equal
      end))).

  Ltac t := repeat progress (simpler; simpl in *; autorewrite with AssocListModel; auto).

  (* interactions of lookup and the other operations *)
  Lemma lookup_remove_eq k l : lookup k (remove k l) = None.
  Proof. induction l; t. Qed.

  Lemma lookup_remove_neq k k' l : k <> k' -> lookup k (remove k' l) = lookup k l.
  Proof. induction l; t. Qed.

  Lemma lookup_insert_eq k v l : lookup k (insert v l) = Some v.
  Proof. induction l; t. Qed.

  Lemma lookup_insert_neq k k' (v:value_t k') l : k <> k' -> lookup k (insert v l) = lookup k l.
  Proof. induction l; t. Qed.
  Hint Rewrite lookup_remove_eq lookup_insert_eq : AssocListModel.
  Hint Rewrite lookup_remove_neq lookup_insert_neq using solve[t] : AssocListModel.

  Lemma lookup_none_remove k l : lookup k l = None -> remove k l = l.
  Proof. induction l; t. Qed.

  Lemma lookup_none_perm k l l' : Permutation l l' -> lookup k l = None -> lookup k l' = None.
  Proof. induction 1; t. Qed.

  (* interactions of distinct and the other operations *)
  Lemma distinct_remove k l : distinct l -> distinct (remove k l).
  Proof. induction l; t; intuition. Qed.

  Lemma distinct_insert k (v:A.value_t k) l : distinct l -> distinct (insert v l).
  Proof. induction l; t; intuition. Qed.

  Hint Resolve lookup_none_remove lookup_none_perm distinct_remove distinct_insert. 

  Lemma distinct_perm l l' : Permutation l l' -> distinct l -> distinct l'.
  Proof. induction 1; t; intuition (congruence||eauto). Qed.

  Hint Resolve distinct_remove distinct_perm Permutation_sym Permutation_refl.

  Lemma lookup_dis_perm k l l' : Permutation l l' -> distinct l -> lookup k l = lookup k l'.
  Proof. induction 1; t; intuition try congruence. rewrite H2. eauto. Qed.

  Lemma remove_perm k l l' : Permutation l l' -> Permutation (remove k l) (remove k l').
  Proof.  Hint Constructors Permutation. induction 1; t; eauto. Qed.
  Hint Resolve lookup_dis_perm remove_perm.

  Lemma insert_perm k l l' (v:A.value_t k) : Permutation l l' -> Permutation (insert v l) (insert v l').
  Proof. unfold insert; t. Qed.

  Lemma remove_swap k k' l : remove k (remove k' l) = remove k' (remove k l).
  Proof. induction l; t. Qed.

  Lemma insert_swap k (v:A.value_t k) k' (v':A.value_t k') l : k <> k' -> 
    Permutation (insert v (insert v' l)) (insert v' (insert v l)).
  Proof. intros. Hint Constructors Permutation. unfold insert; t. rewrite remove_swap. auto. Qed.
  Hint Resolve remove_swap insert_perm insert_swap.

End AssocList.
