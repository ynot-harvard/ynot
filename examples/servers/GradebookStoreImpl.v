Require Import Ynot RSep.
Require Import GradebookModel GradebookApp.
Require Import GradebookTableImpl Store.

Set Implicit Arguments.

Module GradesStoreMapping.
 Export StoreModel.

  Fixpoint Tuple2List' n : Tuple n -> list Grade :=
    match n as n return Tuple n -> list Grade with
      | 0 => fun _ => nil
      | S n => fun x => (fst x) :: (Tuple2List' n (snd x))
    end.

  Definition Tuple2List n (x: Tuple (S n)) :=
    match x with
      | (id, gr) => (id, Tuple2List' n gr)
    end.

  Fixpoint Table2List n (x: Table (S n)) {struct x} : list (ID * list Grade) :=
   match x with
     | nil => nil
     | a :: b => Tuple2List a :: Table2List b
   end.

  Fixpoint List2Tuple' (x: list Grade) n {struct n} : Tuple n :=
    match n as n return Tuple n with
      | S n' => match x with
                  | a :: b => (a, List2Tuple' b n')
                  | nil => (0, List2Tuple' nil n')
               end
      | 0 => tt
    end.

  Definition List2Tuple (x: (ID * list Grade)) n : Tuple (S n) :=
    match x with
      | (id, gr) => List2Tuple' (id :: gr) (S n)
    end.
     
  Fixpoint List2Table (l: list (ID * list Grade)) n {struct l} : Table (S n) :=
   match l with
     | nil => nil
     | a :: b => List2Tuple a n :: List2Table b n
   end.

   Lemma List2Tuple'_Tuple2List' : forall n t,
     List2Tuple' (Tuple2List' n t) n = t.
     induction n.
     intros; destruct t; auto.
     intros. simpl. rewrite IHn. destruct t. auto.
   Qed.


 Lemma List2Tuple_Tuple2List : forall n a,
   List2Tuple (Tuple2List a) n = a.
   destruct n.
   intros; unfold List2Tuple,Tuple2List. simpl. destruct a. destruct t. auto.
   intros. unfold List2Tuple,Tuple2List. destruct a.
   simpl. rewrite List2Tuple'_Tuple2List'. destruct t; auto.
 Qed.

 Lemma List2Table_Table2List : forall n l,
   List2Table (Table2List l) n = l.
   induction l. reflexivity.
   simpl.
   rewrite List2Tuple_Tuple2List. rewrite IHl. trivial.
 Qed.

(* *)

  Fixpoint nthget' {n} a { struct a }: Tuple n -> option nat :=
    match a with
      | 0 => match n return Tuple n -> option nat with
               | 0 => fun _ => None
               | S n' => fun x => Some (fst x)
             end
      | S a' => match n as n return Tuple n -> option nat with
                  | 0 => fun _ => None 
                  | S n'  => fun x => nthget' a' (snd x)
                end
    end.

  Fixpoint nthget n a (l: Table n) {struct l} := 
    match l with
      | nil => None
      | x :: _ => Some (nthget' (S a) x)
    end.

  Fixpoint nthset (size : nat) (idx v' : nat) (tpl : Tuple size) {struct size} : Tuple size :=
    match size as size return Tuple size -> Tuple size with
      | 0 => fun tpl => tpl
      | S n' => fun tpl => match idx with 
                             | 0 => (v', snd tpl)
                             | S idx' => (fst tpl, nthset n' idx' v' (snd tpl))
                           end
    end tpl.

  Definition set_query (size : nat) (id : ID) (assign : Assignment) (grade : Grade) (x1 : Tuple (S size)) :=
    if id_dec id (fst x1)
    then Some (fst x1, nthset size assign grade (snd x1))
    else Some x1.

  Definition get_query x cfg := 
    (fun p: Tuple (S (length (totals cfg))) => 
      match p with | (aa,b) => if id_dec aa x then true else false end).

  Lemma lookup_select : forall l c x x0,
    lookup x l = Some x0
    -> exists t, select (get_query x c) (List2Table l (length (totals c))) = List2Table ((x,x0) :: t) _.
    induction l.
      intros; simpl; discriminate.
      intros. simpl in H. simpl. destruct a. simpl.
      remember (id_dec x i) as RM. destruct RM. destruct (id_dec i x); try congruence. rewrite e in *. inversion  H. rewrite H1 in *.
      exists (Table2List (select (get_query i c) (List2Table l (length (totals c))))).
      rewrite List2Table_Table2List. trivial.
      destruct (id_dec i x); try congruence. simpl in IHl. apply IHl; auto.
  Qed.

  Lemma grade_count : forall c l,
    store_inv l c = true 
    -> forall x x0, lookup x l = Some x0
      -> length x0 = length (totals c).
    intros. unfold store_inv in *. isTrue (store_inv1 l c) H. pose (inv_bounded l c x H1 H0). apply bounded_length. auto.
  Qed.

  Lemma gg_ret : forall w' l0 n assign,
    n = length l0
    -> nthget' assign (List2Tuple' l0 n) = Some w'
    -> nth_get assign l0 = Some w'.
    induction l0.
      simpl. intros. subst. simpl in *. destruct assign; simpl in *; congruence.
      simpl. intros. subst. simpl in *. destruct assign; simpl in *. auto. eapply IHl0; eauto.
  Qed.

Lemma private_lookup : forall x l c user pass assign grade, 
   (private c (GetGrade user pass x assign) = true \/
    private c (SetGrade user pass x grade assign) = true) ->
    store_inv l c = true -> 
    exists g', lookup x l = Some g'.
 unfold store_inv in *; unfold private in *; intros. destruct H; all;
  apply (in_dec_total_dec l x c ); trivial.
Qed. 

  (** GetGrade Properties **)
(*
  Lemma GetGrade_private_lookup : forall c id pass x a l,
    private c (GetGrade id pass x a) = true ->
    store_inv l c = true -> 
    exists g', lookup x l = Some g'.
    intros. simpl in H.
    all. unfold store_inv in H0. all.
.    apply (in_dec_total_dec l x c); auto.
  Qed.
*)
  Theorem GetGrade_store : forall T user pass id assign x (t: Config * T),
    List2Table (snd x) (length (totals (fst t))) = List2Table (snd (snd (mutate (GetGrade user pass id assign) x)))
        (length (totals (fst t))).
  Proof.
    intros. unfold mutate. destruct x. exhaustive ltac:(firstorder).
  Qed.
  Theorem GetGrade_RET_ret : forall T user pass id assign x (t : (Config * T)) w',
    fst x = fst t
    -> store_inv (snd x) (fst t) = true
    -> private (fst t) (GetGrade user pass id assign) = true
    -> nthget assign (select (get_query id (fst t)) (List2Table (snd x) (length (totals (fst t))))) = Some (Some w')
    -> RET w' = fst (mutate (GetGrade user pass id assign) x).
  Proof.
    intros. unfold mutate. destruct x. try rewrite simpl_fst in *; try rewrite simpl_snd in *. rewrite <- H in *.
    rewrite H1. remember (lookup id l) as RM. destruct RM. symmetry in HeqRM. destruct (lookup_select l c id HeqRM). rewrite H3 in H2.
    simpl in H2. inversion H2.
    
    rewrite (@gg_ret w' l0 (length (totals c)) assign); auto.
  
    symmetry. eapply grade_count; eauto. pose private_lookup.
    destruct (private_lookup id l c user pass assign 0 (or_introl _ H1)); auto.
    congruence.
  Qed.
  Theorem GetGrade_private_valid : forall (T:Type) x (t:Config * T) user pass id assign,
    fst t = fst x
    -> store_inv (snd x) (fst x) = true
    -> private (fst t) (GetGrade user pass id assign) = true
    -> nthget assign (select (get_query id (fst t)) (List2Table (snd x) (length (totals (fst t))))) = None
    -> False.
  Proof.
    intros. unfold mutate. destruct x. try rewrite simpl_fst in *; try rewrite simpl_snd in *. rewrite <- H in *.
    assert (exists g', lookup id l = Some g'). eapply (  (private_lookup id l (fst t) user pass assign 0 (or_introl _ H1))); eauto.
    destruct H3.
    destruct (lookup_select _ (fst t) _ H3). rewrite H4 in H2. simpl in H2. congruence.
  Qed.
  Theorem GetGrade_BAD_ret : forall T user pass id assign x (t : (Config * T)),
    fst x = fst t
    -> store_inv (snd x) (fst t) = true
    -> private (fst t) (GetGrade user pass id assign) = true
    -> nthget assign (select (get_query id (fst t)) (List2Table (snd x) (length (totals (fst t))))) = Some None
    -> ERR_BADGRADE = fst (mutate (GetGrade user pass id assign) x).
  Proof.
    intros. unfold mutate. destruct x. try rewrite simpl_fst in *; try rewrite simpl_snd in *. rewrite <- H in *. rewrite H1.
    assert (exists g', lookup id l = Some g'). eapply (private_lookup id l c user pass assign 0 (or_introl _ H1)); eauto.
    destruct H3. rewrite H3.
    destruct (lookup_select _ c _ H3). rewrite H4 in H2. simpl in H2. 
    simpl in *. all. inversion H2.
  
    Lemma gg_bad : forall l0 n assign, 
      n = length l0
      -> nthget' assign (List2Tuple' l0 n) = None
      -> nth_get assign l0 = None.
      induction l0.
        intros; subst; simpl in *; congruence.
        intros. subst; simpl in *. destruct assign; simpl in *; try congruence. eapply IHl0; eauto.
    Qed.
    rewrite (@gg_bad x (length (totals c)) assign); auto. symmetry. eapply grade_count; eauto.
  Qed.

  (** SetGrade Properties **)

  Theorem SetGrade_OK_store : forall x user pass id assign grade,
    store_inv (snd x) (fst x) = true
    -> private (fst x) (SetGrade user pass id assign grade) = true
    -> inbounds grade assign (totals (fst x)) = true
    -> (update (set_query id assign grade)
      (List2Table (snd x) (length (totals (fst x))))) =
    (List2Table (snd (snd (mutate (SetGrade user pass id assign grade) x)))
      (length (totals (fst x)))).
  Proof.
    intros. unfold mutate. destruct x. rewrite simpl_fst in *. rewrite simpl_snd in *.
      rewrite H0. rewrite H1. destruct (private_lookup id l c user pass assign grade (or_intror _ H0)). trivial. rewrite H2.
      simpl. unfold store_inv in H. all.

      Lemma proof' : forall c x grade assign id l,
        lookup id l = Some x
        -> length x = length (totals c)
        -> noduples (students c) l = true
        -> update (set_query id assign grade)
        (List2Table l (length (totals c))) =
        List2Table (insert id (nth_set grade assign x) l) (length (totals c)).
        induction l.
          simpl. congruence.
          intros. remember (id_dec id (fst a)) as RM. destruct RM.
            simpl in H. destruct a. simpl in e. unfold set_query. simpl.
            destruct (id_dec id i); try congruence.
            destruct (id_dec i id); try congruence. simpl. 
            simpl in H1. remember (lookup i l) as RM'; destruct RM'; try congruence.
            repeat inv auto.
            Lemma nthset_nth_set : forall grade l0 n assign,
              n = length l0
              -> nthset n assign grade (List2Tuple' l0 n) = List2Tuple' (nth_set grade assign l0) n.
              induction l0.
                intros; subst; reflexivity.
                intros. subst. simpl. destruct assign. inv auto. inv auto. 
            Qed.
            inversion H. rewrite <- H4 in *. apply nthset_nth_set; auto.
            pose (denoteLookupNone _ HeqRM').
            Lemma updateNone : forall id assign grade c l,
              (forall (x : ID) (t' : list Grade), In (x, t') l -> x <> id)
              -> update (set_query id assign grade) (List2Table l (length (totals c))) =
                 List2Table l (length (totals c)).
              induction l.
                firstorder.
                intros. unfold set_query. simpl. destruct a. simpl. destruct (id_dec id i). pose (H i l0 (in_eq  _ _)); congruence.
                simpl in H. assert (forall (x : ID) (t' : list Grade), In (x, t') l -> x <> id). intros. eapply H; eauto.
                pose (IHl H0). unfold set_query in e. simpl in e. rewrite e. auto.
            Qed.
            pose (e2 := @updateNone i assign grade c l n). unfold set_query in e2. simpl in e2. rewrite e1 in *; auto.
         
          simpl. unfold set_query. destruct a. simpl. simpl in HeqRM, n. rewrite <- HeqRM. destruct (id_dec i id); try congruence.
          simpl. inv auto. apply IHl; auto. simpl in H. rewrite <- HeqRM in H. auto. simpl in H1. destruct (lookup i l); try congruence. all; auto.
       Qed.
     apply proof'. auto. eapply grade_count; eauto. unfold store_inv. each; auto. auto.
  Qed.

  Theorem SetGrade_OK_ret : forall x user pass id assign grade,
    store_inv (snd x) (fst x) = true
    -> private (fst x) (SetGrade user pass id assign grade) = true
    -> inbounds grade assign (totals (fst x)) = true
    -> OK = fst (mutate (SetGrade user pass id assign grade) x).
  Proof.
    intros. unfold mutate. destruct x. rewrite simpl_fst in *. rewrite simpl_snd in *.
      rewrite H0. rewrite H1. destruct (private_lookup id l c user pass assign grade (or_intror _ H0)). trivial. rewrite H2.
      auto.
  Qed.

  Theorem SetGrade_BAD_store : forall x user pass id assign grade,
    store_inv (snd x) (fst x) = true
    -> private (fst x) (SetGrade user pass id assign grade) = true
    -> inbounds grade assign (totals (fst x)) = false
    -> List2Table (snd (snd (mutate (SetGrade user pass id assign grade) x)))
    (length (totals (fst x))) = List2Table (snd x) (length (totals (fst x))).
  Proof.
    intros. unfold mutate. destruct x. simpl in *. rewrite H0. rewrite H1. reflexivity.
  Qed.

  Theorem SetGrade_BAD_ret : forall x user pass id assign grade,
    store_inv (snd x) (fst x) = true
    -> private (fst x) (SetGrade user pass id assign grade) = true
    -> inbounds grade assign (totals (fst x)) = false
    -> ERR_BADGRADE = fst (mutate (SetGrade user pass id assign grade) x).
    intros; unfold mutate. destruct x. rewrite simpl_fst in *. rewrite simpl_snd in *.
      rewrite H0. rewrite H1. auto.
  Qed.

  (** Average Properties **)

  Lemma project_preserves_length : forall n n' F l, 
    length l = length (@project (S n) n' F (List2Table l n)).
    induction l. reflexivity. simpl. rewrite IHl. auto.
  Qed.

  Fixpoint fn (tbl: Table 1) : list Grade :=
    match tbl with
      | nil => nil
      | (a :: b) => ((fst a :: fn b))
    end.

  Lemma fn_preserves_length : forall (l:Table 1), length l = length (fn l). 
    induction l; auto.  simpl. rewrite <- IHl. trivial.
  Qed.

  Lemma NoEntriesNoStudents : forall T (s:list ID), total_dec s (@nil (ID * T)) = true -> s = nil.
    intros. simpl in *. destruct s. trivial. simpl in H; discriminate.
  Qed.

  Lemma lm2 : forall l c, store_inv l c = true -> length l = length (students c).
    unfold store_inv. intros. all. clear F1. destruct c. simpl in *. unfold config_inv in H. all. clear H F1. simpl in F2.
    generalize dependent students0.
    clear tas0 profs0 sections0 hashes0 totals0.
    remember (length l) as RM. generalize dependent l.
    induction RM. 
      intros. destruct l. pose (NoEntriesNoStudents _ _ F0). rewrite e. auto. simpl in *; congruence.
      intros. remember l as ll. destruct ll; try (simpl in *; congruence). simpl in *. inversion HeqRM.
    

      Fixpoint remove (T : Type) (d : forall (a b : T), {a = b} + {a <> b}) (l : list T) (t : T) {struct l} : list T :=
        match l with
          | nil => nil
          | a :: b => if d a t then remove d b t else a :: remove d b t
        end.

      pose (IHRM ll H0 (remove id_dec students0 (fst p))). rewrite <- H0. rewrite e.

      Lemma nodup_totals : forall s p ll,
        unique id_dec s = true
        -> noduples s (p :: ll) = true
        -> total_dec s (p :: ll) = true
        -> noduples (remove id_dec s (fst p)) ll = true /\
           total_dec (remove id_dec s (fst p)) ll = true.

       intros. destruct p. simpl in *. remember (lookup i ll) as RM. destruct RM; try congruence.
       Lemma noduples_remove : forall ll s x,
         lookup x ll = None -> noduples s ll = true -> noduples (remove id_dec s x) ll = true.
            induction ll.
              reflexivity.
              intros. simpl. destruct a. rewrite simpl_fst in *. cut (lookup i ll = None). intro. rewrite H1.
              each. simpl in H0. rewrite H1 in H0. all.
              Lemma in_dec_in : forall i s x,
                in_dec i s = true -> i <> x -> in_dec i (remove id_dec s x) = true.
                induction s. 
                  simpl; congruence.
                  intros. simpl. destruct (id_dec a x). unfold in_dec in H. rewrite e in *. destruct (id_dec i x); try congruence. auto.
                  simpl. destruct (id_dec i a); try congruence. apply IHs; auto. simpl in H. destruct (id_dec i a); try congruence.
              Qed.
              apply in_dec_in; auto. unfold not. intro. subst. simpl in H. destruct (id_dec x x); congruence.
              apply IHll; auto. unfold lookup in H. destruct (id_dec x i); try congruence. auto.
              simpl in H0. rewrite H1 in H0. all; auto. simpl in H0. destruct (lookup i ll); try congruence.
        Qed.
        split. all. apply noduples_remove; auto.
        Lemma total_dec_remove : forall T s i (l:T) ll,
          unique id_dec s = true
          -> total_dec s ((i,l) :: ll) = true
          -> total_dec (remove id_dec s i) ll = true.
          induction s.
            reflexivity.
            intros. simpl in *. remember (id_dec a i) as RM. destruct RM. remember (In_dec id_dec a s) as RM'. destruct RM'; try congruence.
            rewrite <- e in *. eapply IHs; eauto.

            destruct (In_dec id_dec a s); try congruence. simpl. destruct (lookup a ll); try congruence. eapply IHs; eauto.
        Qed.
        eapply total_dec_remove; eauto.
      Qed.

      Lemma remove_notin : forall T dec (x : T) s,
        ~In x s
        -> s = remove dec s x.
        induction s.
          simpl; auto.
          simpl. intros. destruct (dec a x). subst. tauto. rewrite <- IHs; auto.
      Qed.
  
      Lemma remove_unique : forall T dec (x:T) s,
        unique dec s = true
        -> In x s 
        -> length s = S (length (remove dec s x)).
        induction s.
          simpl; intros. inversion H0.
          intros. simpl. inv auto. destruct H0. subst.
            destruct (dec x x); try congruence. simpl in H. destruct (In_dec dec x s); try congruence.
            rewrite <- remove_notin; auto.
            destruct (dec a x). simpl in H. destruct (In_dec dec a s); try congruence. rewrite <- remove_notin; auto. subst; auto.
            apply IHs; auto. simpl in H. destruct (In_dec dec a s); try congruence.
      Qed.
      rewrite (@remove_unique _ id_dec (fst p) students0); auto.
      destruct (lookup (fst p) ll); try congruence. all. apply denoteInDec; auto.
      destruct (@nodup_totals students0 p ll F2 F F0); auto.
      destruct (@nodup_totals students0 p ll F2 F F0); auto.
      Lemma remove_preserves_unique : forall T dec (x :T) s,
        unique dec s = true -> unique dec (remove dec s x) = true.
        induction s.
          auto.
          intros. simpl. simpl in H. destruct (In_dec dec a s); try congruence. destruct (dec a x).
            apply IHs; auto.
            simpl. rewrite IHs; auto.
            destruct (In_dec dec a (remove dec s x)); auto.
            Lemma remove_not : forall T dec (a x : T) s,
              ~In a s -> ~In a (remove dec s x).
              induction s; [ auto | ] .
              intuition. simpl in H0. simpl in H. destruct (dec a0 x). subst.
              contradiction. simpl in H0. destruct H0. subst. auto. auto.
            Qed.
            apply (remove_not dec a x) in n. contradiction.
      Qed.
    apply remove_preserves_unique; auto.
  Qed.

  Lemma lm3 : forall l ,
    aggregate (fun (a : nat) (x0 : Tuple 1) => fst x0 + a) 0 l = sum_all (fn l).
    induction l. auto. simpl in *. rewrite IHl. trivial.
  Qed.


  Opaque GET_COL.
  Lemma lm4 : forall l c assign pfx2,
    store_inv l c = true ->
    Some(fn
      (project (@GET_COL (S (length (totals c))) (S assign) pfx2)
        (List2Table l (length (totals c))))) = proj assign l.
    intros. assert (forall (x : ID) (x0 : list Grade), lookup x l = Some x0 -> length x0 = length (totals c)). intros; eapply grade_count; eauto.
    unfold store_inv in H. assert (config_inv c = true). all; auto.  rewrite H1 in H.
    assert (
        (andb (andb (store_inv1 l c) (total_dec (students c) l))
           (noduples (students c) l)) = true).  all; each; auto.  clear H.  rename H2 into H. clear H1. all. clear F. clear F0. generalize dependent H0. intro.
    induction l.
      simpl. trivial.
      Lemma nth_get_less' : forall (T : Type) id l a (t:list T) pfx2,
      length l = length t
      -> a < length l
      -> nth_get a l = Some (fst (@GET_COL (S (length t)) (S a) pfx2 (List2Tuple (id,l) (length t)))).
        induction l.
      simpl. intros. elimtype False. omega.
      intros. rewrite GET_COL_projs. rewrite <- H.
      destruct a0; auto.
          simpl. Opaque GET_COL. simpl in *. destruct t. simpl in H. congruence.
          simpl in H.  inversion H. rewrite H2 in H0.
          pose (@IHl a0 t0 H0). rewrite e; auto. rewrite GET_COL_projs. simpl. rewrite H2. auto. omega.       
      Qed.
      unfold proj. Opaque GET_COL. simpl. fold proj. rewrite <- IHl.
      pose (H0 (fst a) (snd a)). 
      assert (length (snd a) = length (totals c)). apply e; destruct a; compute; destruct (id_dec i i); auto. congruence.
      rewrite (@nth_get_less' _ (fst a) (snd a) assign (totals c) pfx2); auto. destruct a. auto.
      rewrite H1; omega. intros. simpl in H. destruct (lookup (fst a) l); try congruence. all. auto. intros. apply (H0 x). simpl. destruct a. destruct (id_dec x i); auto.
      simpl in H. subst; rewrite H1 in H. congruence.
    Qed.

  Theorem AvgRet : forall v x1 y l c assign user pass
    (pfx2: assign < length (totals c))
    (H1 : y = aggregate (fun (a : nat) (x0 : Tuple 1) => fst x0 + a) 0 x1)
    (H2 : v = RET (divcheck0 y (length (students c))))
    (H3 : x1 = project (GET_COL (Lt.lt_n_S _ _ pfx2))
      (List2Table l (length (totals c ))))
    (H4 : store_inv l c = true)
    (H5 : private c (Average user pass assign) = true),
    v = fst (mutate (Average user pass assign) (c, l)).

    intros. unfold mutate. rewrite H5. destruct (validAssignment c assign); try solve [ elimtype False; omega ].
    cut (Some (fn (project (GET_COL (Lt.lt_n_S _ _ pfx2))
      (List2Table l (length (totals c))))) = proj assign l ). intros jj.
    rewrite <- jj. unfold avg.
    cut (y = sum_all (fn (project (GET_COL (Lt.lt_n_S _ _ pfx2)) (List2Table l (length (totals c)))))). intros jj2. rewrite <- jj2.
    cut (length (students c) = length (fn (project (GET_COL (Lt.lt_n_S _ _ pfx2)) (List2Table l (length (totals c)))))). intros jj3. rewrite <- jj3. auto.
    cut (length l = length (students c)). intros jj4. rewrite <- jj4 . 
    rewrite (@project_preserves_length (length (totals c)) 1 (GET_COL (Lt.lt_n_S _ _ pfx2)) l). 
    apply fn_preserves_length.  
    apply (lm2 ). trivial.
    rewrite H1. rewrite <- H3. apply lm3. apply lm4; trivial.
  Qed.


  Theorem AverageStore : forall user pass assign c l,
    List2Table l (length (totals c)) = 
    List2Table (snd (snd (mutate (Average user pass assign) (c,l))))
    (length (totals c)).
  Proof.
    intros. unfold mutate.  exhaustive ltac:(firstorder).
  Qed.

  Theorem AvgBad : forall l c assign user pass  
    (pfx1 : assign >= length (totals c))
    (H1 : store_inv l c = true)
    (H2 : private c (Average user pass assign) = true),
    ERR_BADGRADE = fst (mutate (Average user pass assign) (c,l)).
    intros. unfold mutate. rewrite H2. destruct (validAssignment c assign); auto. elimtype False. omega.
  Qed.

End GradesStoreMapping.

Module GradebookStoreImpl (s: Store) : GradebookImpl.
(* Export GradesTableMapping. *)
  Export GradesStoreMapping.

  Definition T := (Config * s.t)%type.

 Open Scope hprop_scope.

  Definition rep (t: T) (m: (Config * list (ID * (list Grade)))) : hprop 
    := [fst t = fst m] * s.rep (snd t) (List2Table (snd m) (length (totals (fst t)))).

  Open Scope stsepi_scope.

  (* set branch impl *)
  Definition F_set user pass id assign grade m t : 
    STsep (m ~~ rep t m * [store_inv (snd m) (fst m) = true] * 
              [private (fst t) (SetGrade user pass id assign grade) = true])
          (fun r : Status => m ~~ [r  = fst (mutate (SetGrade user pass id assign grade)  m)] * 
              rep t (snd (mutate (SetGrade user pass id assign grade) m)) * [store_inv (snd m) (fst m) = true]).
    intros. unfold T in *. refine (
      let cfg := fst t in
      let st := snd t in
      (match inbounds grade assign (totals cfg) as ib
         return inbounds grade assign (totals cfg) = ib -> _
         with
         | true => fun pf => 
           s.update st (set_query id assign grade) (m ~~~ List2Table (snd m) (length (totals cfg))) <@> _ ;;
           {{ Return OK }}
         | false => fun pf => 
           {{ Return ERR_BADGRADE }}
       end) (refl_equal _)
    ); unfold rep; unfold st; unfold cfg.
    solve [ do 2 rsep fail auto ].
    solve [ rsep fail auto ].
    solve [ rsep fail auto ].

    (** It would be nice to get these with hints. **)
    Hint Resolve SetGrade_OK_store.
    Hint Resolve SetGrade_OK_ret.
    Hint Resolve const_config.
    solve [ rsep fail auto; unfold cfg in *; rewrite H4 in *;
      rewrite <- (SetGrade_OK_ret x user pass id assign grade H2 H3 pf);
      rewrite <- (SetGrade_OK_store _ _ _ _ _ _ H2 H3 pf); rsep fail auto ].
    solve [ rsep fail auto ].

    Hint Resolve SetGrade_BAD_store.
    Hint Resolve SetGrade_BAD_ret.
    solve [ rsep fail auto; unfold cfg in *; rewrite H0 in *;
      rewrite (SetGrade_BAD_store _ _ _ _ _ _ H1 H2 pf);
      rewrite (SetGrade_BAD_ret _ _ _ _ _ _ H1 H2 pf); rsep fail auto ].
  Qed.

  (* type of error computations *)
  Definition F_err_t (e: Status) := STsep __ (fun r => [e = r]).

  Definition F_get : forall user pass id assign m t,
    STsep (m ~~ rep t m * [store_inv (snd m) (fst m) = true] * 
              [private (fst t) (GetGrade user pass id assign) = true])
          (fun r : Status => m ~~ [r  = fst (mutate (GetGrade user pass id assign)  m)] * 
              rep t (snd (mutate (GetGrade user pass id assign) m)) * [store_inv (snd m) (fst m) = true]).
    refine (fun user pass id assign m t =>
      xx <- s.select (snd t) (get_query id (fst t)) (m ~~~ List2Table (snd m)  (length (totals (fst t))) ) <@> _ ;
      match nthget assign xx as R return  nthget assign xx = R  -> _  with 
        | None => fun pf => {{ !!! }}
        | Some w => fun pf => match w as w' return w = w' -> _ with
                                | None =>    fun pf2 =>  {{ Return ERR_BADGRADE }}  
                                | Some w' => fun pf2 =>  {{ Return (RET w') 
                                  <@> (m ~~ [fst t = fst m] * [store_inv (snd m) (fst t) = true] * [private (fst t) (GetGrade user pass id assign) = true]) }}
                              end (refl_equal _)
      end  (refl_equal _ )  ).
    unfold rep; do 2 rsep fail auto.
    rsep fail auto.
    rsep fail auto. rewrite <- H4. rsep fail auto.
    unfold rep; rsep fail auto. rewrite <- H4. rsep fail auto.

    rewrite H0 in pf. rewrite pf2 in pf. auto.
    rewrite (GetGrade_RET_ret user pass id assign x t); auto. rsep fail auto.
    rewrite <- (@GetGrade_store _ user pass id assign x t); auto. rsep fail auto.
    pose (const_config2 x t (GetGrade user pass id assign)). rsep fail auto.
    rsep fail auto.
    unfold rep; rsep fail auto.
    rewrite (GetGrade_BAD_ret user pass id assign x t); auto. rsep fail auto.
    rewrite <- (@GetGrade_store _ user pass id assign x t); auto. rsep fail auto.
    pose (const_config2 x t (GetGrade user pass id assign)). rsep fail auto. rewrite H5; auto. rewrite (pack_injective H0). rewrite H1 in pf. rewrite pf2 in pf. trivial. 
    rsep fail auto.
    elimtype False. apply (@GetGrade_private_valid _ x t user pass id assign); auto. rewrite <- (pack_injective H0) in *. subst. auto.
    rsep fail auto.
  Qed.

Require Import Lt.
Definition F_avg : forall user pass assign m t,
  STsep (m ~~ rep t m * [store_inv (snd m) (fst m) = true] * 
    [private (fst t) (Average user pass assign) = true])
  (fun r : Status => m ~~ [r  = fst (mutate (Average user pass assign)  m)] * 
    rep t (snd (mutate (Average user pass assign) m)) * [store_inv (snd m) (fst m) = true]).
  refine (fun user pass assign m t =>
  match validAssignment (fst t) assign with
    | left pf =>
      x <- s.project (snd t) (@GET_COL _ (S assign) (lt_n_S _ _ pf)) (m ~~~ List2Table (snd m)  (length (totals (fst t)))) <@> _  ;
      y <- s.aggregate (fst x) (fun a (x0: Tuple 1) => (fst x0) + a) 0 (snd x) <@> _ ;
      s.free (fst x) (snd x) <@> _ ;; 
      {{ Return (RET (divcheck0 y (length (students (fst t))))) }}     
    | right pf =>
      {{ Return ERR_BADGRADE }}
  end).
 unfold rep. rsep fail auto. 
 rsep fail auto.
 unfold rep. rsep fail auto.
 unfold rep. rsep fail auto.
 unfold rep. rsep fail auto.
 unfold rep. rsep fail auto.
 unfold rep. rsep fail auto. 
 rsep fail auto.
 unfold rep. rsep fail auto. destruct t. destruct x0. simpl in H3. simpl in H5. subst c0.
 pose (@AvgRet v x1 y l c assign user pass pf H1 H6 H2 H3 H4).
 rewrite e. 
 pose (const_config2  (c, l) (c, l) (Average user pass assign)).
 pose (rr := AverageStore user pass assign c l ). Opaque mutate. simpl.
rewrite rr. rsep fail auto.
 rsep fail auto.
 unfold rep. rsep fail auto. rsep fail auto.
 unfold rep. rsep fail auto. destruct t. destruct x. simpl in H3. simpl in H0. subst c0.
 pose (@AvgBad l c assign user pass pf H1 H2).
 rewrite e. 
 pose (const_config2  (c,l) (c,l) (Average user pass assign) (refl_equal (fst (c,l)))).
 pose (rr := AverageStore user pass assign c l). Opaque mutate. simpl.
 rewrite rr. rsep fail auto.
Qed.

(* The overall computation just stiches the branches together. *)
Definition F : forall (q: Command) m t,
  STsep (m ~~ rep t m * [store_inv (snd m) (fst m) = true] * [private (fst t) q = true])
        (fun r : Status => m ~~ [r  = fst (mutate q m)] * 
               rep t (snd (mutate q m)) * [store_inv (snd m) (fst m) = true]).
refine (fun q m t => 
  match q as q 
    return STsep (m ~~ rep t m * [store_inv (snd m) (fst m) = true] * [private (fst t) q = true])
                 (fun r : Status => m ~~ [r  = fst (mutate q m)] * 
                     rep t (snd (mutate q m)) * [store_inv (snd m) (fst m) = true])
    with 
    | GetGrade id pass x a   =>  F_get id pass x a m t
    | SetGrade id pass x a g =>  F_set id pass x a g m t
    | Average  id pass a     =>  F_avg id pass a m t 
  end). 
Qed.
  
(* Then we just {{ }} it to the proper type for exec. *)
Definition exec' : forall (t : T) (q : ParseCommand) (m : [(Config * list (ID * (list Grade)))]),
  STsep (m ~~ rep t m * [store_inv (snd m) (fst m) = true] ) 
  (fun r : Status => m ~~ [r  = fst (mutate (compileCommand (fst m) q) m)] * 
    rep t (snd (mutate (compileCommand (fst m) q) m)) * [store_inv (snd m) (fst m) = true] ).
refine (fun t q m =>
let q := compileCommand (fst t) q in
{{match private (fst t) q as p'
    return STsep (m ~~ rep t m * [store_inv (snd m) (fst m) = true] * [private (fst t) q = p'])
                 (fun r : Status => m ~~ [r  = fst (mutate q m)] * 
                   rep t (snd (mutate q m)) * [store_inv (snd m) (fst m) = true])
    with
    | true => F q m t 
    | false => {{ Return  ERR_NOTPRIVATE }}
  end}}).
  rsep fail auto.
  unfold q0.
  destruct t. hdestruct m. unfold rep. rsep fail auto. Opaque mutate. simpl in *. subst.
  sep fail auto. Transparent mutate. unfold mutate. destruct (private c0 (compileCommand c0 q)). discriminate.
   simpl in *. sep fail auto.
 unfold rep, q0; rsep fail auto. 
 unfold rep,q0.
 rsep fail auto. cut (fst t = fst x). intro. rewrite H3. rsep fail auto.
 rewrite H1. symmetry. apply const_config.
Qed.

Export ExampleConfig.
  Definition init :
    STsep (__)
          (fun tm : T * [(Config * list (ID * (list Grade)))] => hprop_unpack (snd tm) 
            (fun m => rep (fst tm) m * [store_inv (snd m) (fst m) = true])). 
    refine (
      x <- s.new (S (length (totals test_config))) ;
      s.insert x (n:=(S (length (totals test_config)))) ((4,(65,(63,(75,tt))))::nil) _;;
      s.insert x (n:=(S (length (totals test_config)))) ((5,(68,(76,(80,tt))))::nil) _;;
      s.insert x (n:=(S (length (totals test_config)))) ((6,(70,(80,(94,tt))))::nil) _;;
      {{ Return ((test_config, x), inhabits test_model) }});
    unfold rep; pose test_cfg_inv; rsep fail auto.
    subst. simpl in *. eapply pack_injective in H0. subst. rsep fail auto.
  Qed. 

  Definition cleanup : forall (t : T) (m : [(Config * list (ID * list Grade))]),
    STsep (m ~~ rep t m * [store_inv (snd m) (fst m) = true])
          (fun _:unit => __).
    refine (fun t m => {{s.free (snd t) (m ~~~ List2Table (snd m) (length (totals (fst t)))) }});
    unfold rep; sep fail auto.
  Qed.

End GradebookStoreImpl.

Module some_store : Store := ListStore.
Module the_app' := GradebookStoreImpl some_store.
Module theApp : GradebookType := GradebookApp.Gradebook the_app'.

Require Import GradebookInterface.
Module http_interface := HttpGradebookInterface theApp.

Require Import HttpServer.
Module http_server := HttpServer.HttpAppStateParams theApp http_interface.
Module mod_http := TcpServer.ExecImpl http_server.

Definition http := mod_http.main.

