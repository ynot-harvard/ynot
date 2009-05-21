Require Import GradebookModel List Bool.

(* This gives a more logical definition of the spec. 
   It's missing the mutate part, but has the config part. 
   It exists to back up a single claim in the paper that
   specs don't need to resemble programs. *)
Module LogicalGradebookModel.
  Export GradebookModel.

  (* The computational style shown above is useful for proof
     automation, but we can easily show it equivalent to
     a more logical style of definition. *)
  Definition correct_cfg' (cfg: Config) := forall id, 
(*    (In id (students cfg) -> (~In id (tas cfg) /\ ~In id (profs cfg))) /\
    (In id (tas cfg) -> (~In id (students cfg) /\ ~In id (profs cfg))) /\
    (In id (profs cfg) -> (~In id (tas cfg) /\ ~In id (students cfg))) /\ *)
    (In id (students cfg) \/ In id (tas cfg) \/ In id (profs cfg) -> 
      exists hash, lookup id (hashes cfg) = Some hash) /\
    (In id (students cfg) \/ In id (tas cfg) ->
      exists section, lookup id (sections cfg) = Some section).

  (** Proofs **)

  Lemma excludesWeaken : forall l a b, excludes l (a :: b) = true -> excludes l b = true.
    induction l.
      firstorder.
      intros. unfold excludes in H. remember (in_dec a (a0 :: b)) as InD. destruct InD. inversion H. fold excludes in H.
        pose (IHl a0 b H). unfold excludes. unfold in_dec in HeqInD. destruct (id_dec a a0); try congruence. unfold excludes in e. rewrite e.
      unfold in_dec. rewrite <- HeqInD. trivial.
  Qed.

  Lemma denoteIn : forall T (x : T) (l : list T), In x l -> exists a, exists b, l = a ++ x :: b.
    induction l.
      firstorder.
      intros. destruct H. exists (@nil T). exists l. simpl. subst. auto.
        destruct (IHl H). destruct H0. exists (a :: x0). exists x1. simpl. subst. auto.
  Qed.

  Lemma excludes_app : forall a b c, excludes (a ++ b) c = excludes a c && excludes b c.
    induction a.
      firstorder.
      simpl. intros. destruct (in_dec a c). auto. auto.
  Qed.

  Lemma denoteExcludes : forall (l1 l2 : list ID),
    excludes l1 l2 = true -> (forall i, In i l1 -> ~In i l2).
    induction l1.
      solve [ firstorder ].
      intros. destruct (denoteIn _ _ _ H0). destruct H1. rewrite H1 in H. rewrite excludes_app in H.
      isTrue (excludes (i :: x0) l2) H. unfold andb in H. destruct (excludes x l2); discriminate.
      simpl in H2. remember (in_dec i l2) as RM. destruct RM; try congruence.

      Lemma denoteNotInDec : forall i l2,
        false = in_dec i l2 -> ~In i l2.
        unfold not. induction l2.
          firstorder.
          simpl. destruct (id_dec i a). firstorder. firstorder.
      Qed.
      apply denoteNotInDec; auto.
  Qed.

  Lemma total_dec_app : forall T (a b : list ID) (c : list (ID * T)), total_dec (a ++ b) c = total_dec a c && total_dec b c.
    intros; induction a.
      auto.
      intros; simpl. destruct (lookup a c). rewrite IHa. auto. auto.
  Qed.

  Lemma denoteTotalDec : forall (T:Set) k l (m : list (ID * T)), 
    In k l -> total_dec l m = true -> exists v, lookup k m = Some v.
    intros. induction l.
      inversion H.
      unfold In in H. destruct H.
        unfold total_dec in H0.
        remember (lookup a m) as RM. destruct RM. subst. exists t. firstorder. inversion H0.
        simpl in H0. destruct (lookup a m); [ | discriminate ]. apply IHl; assumption. 
  Qed.

  Lemma denotation_total_dec : forall (T:Set) a (b : list (ID * T)),
    (forall id, In id a -> exists h, lookup id b = Some h) -> total_dec a b = true.
    induction a.
      firstorder.
      intros. simpl. remember (lookup a b) as RM. destruct RM. apply IHa. intros. apply H. unfold In. right. auto.
      assert (In a (a :: a0)). unfold In; left; auto. pose (H a H0). destruct e. congruence.
  Qed.

  Lemma denotation_excludes : forall X Y, (forall id, In id X -> ~In id Y) -> excludes X Y = true.
    induction X.
      firstorder.
      intros. simpl. pose (H a (in_eq _ _)). remember (in_dec a Y) as RM. destruct RM.
        symmetry in HeqRM. pose (denoteInDec _ _ HeqRM). congruence.
        apply IHX. intros. pose (H id).
        apply n0. 
        remember (id_dec id a) as RM'. destruct RM'. rewrite e in *. apply in_eq. unfold In. right. auto.
  Qed.

  Theorem cfg_correct_eqiv : forall cfg,
    correct_cfg cfg = true <-> correct_cfg' cfg.
  Proof.
    split; intros.
    (** -> **)
    unfold correct_cfg,disjoint_dec in H. repeat rewrite total_dec_app in H. all. simpl in F. all.
    unfold correct_cfg'. intros.
    split; intros.
    destruct H0;
      [ eapply denoteTotalDec; eassumption
      | destruct H0; eapply denoteTotalDec; eassumption ].
    destruct H0; eapply denoteTotalDec; eassumption.

    (** <- **)
    unfold correct_cfg',correct_cfg in *. repeat rewrite total_dec_app. unfold disjoint_dec. simpl.
    each; ((apply denotation_total_dec; firstorder)).   
  Qed.

End LogicalGradebookModel.
