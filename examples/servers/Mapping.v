Require Import GradebookModel.
Require Import List.

Set Implicit Arguments.

Module Type GradeBook.

  Parameter T : Type.
(*
  Parameter Teq : forall (c : Config) (a b : T), Prop.

  Parameter T_eq : forall (c : Config) (a b : T), {Teq c a b} + {~Teq c a b}.
*)

  Parameter GetImpl : Config -> T -> ID -> Assignment -> Grade.
  Parameter SetImpl : Config -> T -> ID -> Assignment -> Grade -> T.
  Parameter AvgImpl : Config -> T -> Assignment -> nat * Grade.
(*
  Parameter GetSubst : forall (c : Config) (l r : T) (s : ID) (a : Assignment), 
    Teq c l r
    -> In s (students c)
    -> validAssignment c a = true
    -> GetImpl c l s a = GetImpl c r s a.
  Parameter SetSubst : forall (c : Config) (l r : T) (s : ID) (a : Assignment) (g : Grade), 
    Teq c l r
    -> In s (students c)
    -> validAssignment c a = true
    -> Teq c (SetImpl c l s a g) (SetImpl c r s a g).
  Parameter AvgSubst : forall (c : Config) (l r : T) (a : Assignment),
    Teq c l r
    -> validAssignment c a = true
    -> AvgImpl c l a = AvgImpl c r a.  
*)
End GradeBook.

Module Type GradeBookIso.
  Declare Module S : GradeBook.
  Declare Module T : GradeBook.

  Parameter f : Config -> S.T -> T.T.
  Parameter g : Config -> T.T -> S.T.

  Parameter GetCorrect : forall (c : Config) (t : S.T) (s : ID) (a : Assignment),
    In s (students c)
    -> a < length (totals c)
    -> S.GetImpl c t s a = T.GetImpl c (f c t) s a.
(*
  Parameter SetCorrect : forall (c : Config) (t : S.T) (s : ID) (a : Assignment) (gr : Grade),
    In s (students c)
    -> validAssignment c a = true
    -> S.Teq c (S.SetImpl c t s a gr) (g c (T.SetImpl c (f c t) s a gr)).
*)

  Parameter SetCorrect : forall (c : Config) (t : S.T) (s : ID) (a : Assignment) (gr : Grade),
    In s (students c)
    -> a < length (totals c)
    -> S.SetImpl c t s a gr = g c (T.SetImpl c (f c t) s a gr).

  Parameter AvgCorrect : forall (c : Config) (t : S.T) (a : Assignment),
    a < length (totals c)
    -> S.AvgImpl c t a = T.AvgImpl c (f c t) a.

End GradeBookIso.

Module GradeBookSpec <: GradeBook.
  Require Import Sumbool.
  Require Import Peano_dec.
  Require Import List.

  Definition T := ID -> Assignment -> Grade.
  (*
     Definition Teq (c : Config) (l r : T) :=
     forall (s : ID) (a : Assignment),
     In s (students c) -> validAssignment c a = true -> l s a = r s a.
     *)
  Definition GetImpl (c : Config) (t : T) (s : ID) (a : Assignment) := t s a.
  Definition SetImpl (c : Config) (t : T) (s : ID) (a : Assignment) (g : Grade) :=
    fun s' a' => if sumbool_and _ _ _ _ (id_dec s s') (eq_nat_dec a a') then g else t s' a'.

  Definition AvgImpl (c : Config) (t : T) (a : Assignment) :=
    fold_left (fun acc s => (1 + fst acc, (t s a) + snd acc)) (students c) (0,0).

(*
  Theorem GetSubst : forall (c : Config) (l r : T) (s : ID) (a : Assignment), 
    Teq c l r
    -> In s (students c)
    -> validAssignment c a = true
    -> GetImpl c l s a = GetImpl c r s a.
  Proof.
    unfold Teq; firstorder.
  Qed.
    
  Theorem SetSubst : forall (c : Config) (l r : T) (s : ID) (a : Assignment) (g : Grade), 
    Teq c l r
    -> In s (students c)
    -> validAssignment c a = true
    -> Teq c (SetImpl c l s a g) (SetImpl c r s a g).
  Proof.
    unfold Teq, SetImpl. intros. rewrite H; auto.
  Qed.

  Theorem AvgSubst : forall (c : Config) (l r : T) (a : Assignment),
    Teq c l r
    -> validAssignment c a = true
    -> AvgImpl c l a = AvgImpl c r a.
  Proof.
    Hint Resolve in_eq.
    unfold Teq, AvgImpl, validAssignment. destruct c. simpl students. simpl totals. clear. generalize (0,0).
    induction students0.
      reflexivity.
      intros. simpl. rewrite H; auto.
      cut (forall (s : ID) (a : Assignment),
       In s students0 ->
       (if lt_dec a (length totals0) then true else false) = true ->
       l s a = r s a). intro.
      apply (@IHstudents0 (S (fst p), r a a0 + snd p) l r a0 H1 H0).
      intros. apply H; try right; auto.
  Qed.
*)
End GradeBookSpec.

Module GradeBookImplModel <: GradeBook.
  Require Import Bool Peano_dec.
  Require Import Store.
  Export StoreModel.

  Definition T := Table 3.

  (** We could relax this to equality up to permutation 
  Definition Teq (c : Config) (l r : T) := l = r. *)

  Definition get_q (s : ID) (a : Assignment) (tpl : Tuple 3) :=
    match tpl with 
      | (s',(a',_)) => if id_dec s s' then if eq_nat_dec a a' then true else false else false
    end.
  Definition GetImpl (c : Config) (t : T) (s : ID) (a : Assignment) :=
    match select (get_q s a) t with
      | nil => 0
      | (_,(_,(gr,_))) :: _ => gr
    end.

  Definition set_q (s : ID) (a : Assignment) (g : Grade) (tpl : Tuple 3) :=
    match tpl with 
      | (s',(a',(g',_))) => 
        if id_dec s s' then 
          if eq_nat_dec a a' 
            then Some (s',(a',(g,tt)))
            else Some (s',(a',(g',tt)))
          else Some (s',(a',(g',tt)))
    end.
  Definition SetImpl (c : Config) (t : T) (s : ID) (a : Assignment) (g : Grade) : T :=
    update (set_q s a g) t.


  Definition avg_filt_q (a : Assignment) (tpl : Tuple 3) :=
    match tpl with
      | (_,(a',_)) => if eq_nat_dec a a' then true else false
    end.
  Definition avg_q (acc : nat * Grade) (tpl : Tuple 1) :=
    (1 + fst acc, fst tpl + snd acc).
  Lemma good_col : 2 < 3. omega. Qed.
  Definition AvgImpl (c : Config) (t : T) (a : Assignment) :=
    aggregate avg_q (0,0) (@project 3 1 (GET_COL good_col) (select (avg_filt_q a) t)).
(*
  Theorem GetSubst : forall (c : Config) (l r : T) (s : ID) (a : Assignment), 
    Teq c l r
    -> In s (students c)
    -> validAssignment c a = true
    -> GetImpl c l s a = GetImpl c r s a.
  Proof.
    unfold Teq; intros; subst; auto.
  Qed.
    
  Theorem SetSubst : forall (c : Config) (l r : T) (s : ID) (a : Assignment) (g : Grade), 
    Teq c l r
    -> In s (students c)
    -> validAssignment c a = true
    -> Teq c (SetImpl c l s a g) (SetImpl c r s a g).
  Proof.
    unfold Teq; intros; subst; auto.
  Qed.

  Theorem AvgSubst : forall (c : Config) (l r : T) (a : Assignment),
    Teq c l r
    -> validAssignment c a = true
    -> AvgImpl c l a = AvgImpl c r a.
  Proof.
    unfold Teq; intros; subst; auto.
  Qed.
*)
End GradeBookImplModel.

Module ImplCorrect : GradeBookIso with Module S := GradeBookSpec 
                                  with Module T := GradeBookImplModel.
  Require Import Axioms.
  Require Import Bool Sumbool List Peano_dec.
  Require Import Store.
  Require Import RSep.
  Export StoreModel.

  Module S := GradeBookSpec.
  Module T := GradeBookImplModel.

  (** Mapping Function **)
  Definition f (c : Config) (lt : S.T) : T.T := 
    flat_map (fun s =>
      map (fun i => (s,(i,(lt s i,tt)))) (seq 0 (length (totals c)))) (students c).

  Definition g (c : Config) (lt : T.T) : S.T :=
    fun i a => T.GetImpl c lt i a.

  (** Lemmas **)
  Lemma assign_valid_assign : forall lst (t : S.T) (s : ID) (a : Assignment) g,
    In (s,(a,(g,tt))) (map (fun i => (s,(i,(t s i,tt)))) lst) -> g = t s a.
  Proof.
    induction lst.
      simpl. intros; destruct H.
      simpl. intros. destruct H. inversion H; auto.
      apply IHlst; auto.
  Qed.
  Lemma select_app : forall (n : nat) (p : Tuple n -> bool) (tbl1 tbl2 : Table n), 
    select p (tbl1 ++ tbl2) = (select p tbl1) ++ (select p tbl2).
  Proof.
    induction tbl1.
      reflexivity.
      induction tbl2.
      simpl; norm_list; reflexivity.
      simpl; norm_list.
        rewrite IHtbl1. destruct (p a); reflexivity.
  Qed.
  Lemma map_len : forall h x,
    x < h -> forall T (f:nat->T), In (f x) (map f (seq 0 h)).
  Proof.
    intros h x H1 H2. assert (In x (seq 0 h)).
    pose (seq_length h 0). rewrite <- e in H1. pose (@nth_In _ x (seq 0 h) h H1). rewrite (@seq_nth h 0 x h) in i. auto. rewrite <- e. auto.
    intros. apply in_map. auto.
  Qed.

  Lemma decideable_in : forall T (dec : forall a b : T, {a = b} + {a <> b}) (a x : T) b,
    In x (a :: b) -> a = x \/ (x <> a /\ In x b).
    intros. destruct (dec x a); auto. 
    right. destruct H. congruence. auto.
  Qed.

  (** Mapping Properties **)
  Theorem GetCorrect : forall (c : Config) (t : S.T) (s : ID) (a : Assignment),
    In s (students c)
    -> a < length (totals c)
    -> S.GetImpl c t s a = T.GetImpl c (f c t) s a.
  Proof.
    unfold ID, Assignment, Grade.
    unfold S.GetImpl. unfold T.GetImpl.
    intros. unfold f. destruct c. simpl. induction students0.
      simpl in *. inversion H.
      simpl. unfold ID,Assignment,Grade. simpl in H. pose (decideable_in id_dec). simpl in o. apply o in H. clear o.
      pose (select_app (T.get_q s a) 
        (map (fun i : Assignment => (a0, (i, (t a0 i, tt))))
          (seq 0 (length totals0)))
        (flat_map
          (fun s0 : ID =>
           map (fun i : Assignment => (s0, (i, (t s0 i, tt))))
             (seq 0 (length totals0))) students0)). simpl in *. unfold ID, Assignment,Grade in *. rewrite e. clear e.
      destruct H.
        subst. pose (assign_valid_assign (seq 0 (length totals0)) t s a). unfold validAssignment in H0. simpl in H0.
          cut (a < length totals0). intro.
          pose (@map_len (length totals0) a H _ (fun i : nat => (s, (i, (t s i, tt))))).
            simpl in i.
            match goal with 
              | [ |- _ = match ?X ++ _ with 
                           | nil => _
                           | _ :: _=> _
                         end ] => remember X as HD
            end. destruct HD.
            symmetry in HeqHD. pose (select_all _ _ HeqHD (s, (a, (t s a, tt))) i). elimtype False. simpl in i0. apply i0.
            clear. 
            repeat match goal with
                     | [ |- (if ?X then _ else _) = true ] => destruct X
                   end; try (congruence || discriminate).
            symmetry in HeqHD. destruct t0. destruct t0. destruct p. destruct (eq_nat_dec n0 a). destruct (id_dec n s). subst.
              pose (e n1). simpl. symmetry. apply e0. destruct (select_just _ _ HeqHD (s,(a,(n1,u))) (in_eq _ _)). destruct u. auto.
              match goal with 
                | [ H : select _ _ = ?X :: _ |- _ ] => 
                  destruct (select_just _ _ H X (in_eq _ _));
                  match goal with 
                    | [ H' : T.get_q _ _ _ = true |- _ ] => simpl in H'
                  end;
                  repeat match goal with 
                           | [ H'' : (if ?X then _ else _) = true |- _ ] => destruct X
                         end
              end; try (congruence || discriminate).
              match goal with 
                | [ H : select _ _ = ?X :: _ |- _ ] => 
                  destruct (select_just _ _ H X (in_eq _ _));
                  match goal with 
                    | [ H' : T.get_q _ _ _ = true |- _ ] => simpl in H'
                  end;
                  repeat match goal with 
                           | [ H'' : (if ?X then _ else _) = true |- _ ] => destruct X
                         end
              end; try (congruence || discriminate).
              auto.
         destruct H.
           remember (select (T.get_q s a) (map (fun i : nat => (a0, (i, (t a0 i, tt)))) (seq 0 (length totals0)))) as LST. unfold Grade in *. rewrite <- HeqLST. symmetry in HeqLST. destruct LST.
             norm_list. apply IHstudents0; auto.
             destruct (@select_just _ _ _ _ HeqLST t0 (in_eq _ _)).
             destruct t0. destruct t0. destruct p. simpl in H2.
             cut (a0 = n). intro. subst; destruct (id_dec s n); congruence.
             pose (in_map_iff (fun i : nat => (a0, (i, (t a0 i, tt)))) (seq 0 (length totals0)) (n, (n0, (n1, u)))). destruct i.
               apply H4 in H3. destruct H3. destruct H3. inversion H3. auto.
  Qed.

  Theorem SetCorrect : forall (c : Config) (t : S.T) (s : ID) (a : Assignment) (gr : Grade),
    In s (students c)
    -> a < length (totals c)
    ->  (S.SetImpl c t s a gr) = (g c (T.SetImpl c (f c t) s a gr)).
  Proof.
  Admitted.

(*    
  Theorem SetCorrect : forall (c : Config) (t : S.T) (s : ID) (a : Assignment) (gr : Grade),
    In s (students c)
    -> a < length (totals c)
    -> S.Teq c (S.SetImpl c t s a gr) (g c (T.SetImpl c (f c t) s a gr)).
  Proof.
    unfold ID, Assignment, Grade. unfold T.SetImpl, S.SetImpl, g, T.GetImpl.
    intros. 
  Admitted.
*)
  Theorem AvgCorrect : forall (c : Config) (t : S.T) (a : Assignment),
    a < length (totals c)
    -> S.AvgImpl c t a = T.AvgImpl c (f c t) a.
  Proof.
  Admitted.

End ImplCorrect.
