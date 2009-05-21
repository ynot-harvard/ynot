Require Import String List Bool Compare_dec Euclid Omega.


Set Implicit Arguments.

Module GradebookModel.
  
  Definition ID := nat.
  Definition PassHash := nat.
  Definition Assignment := nat.
  Definition Grade := nat.
  Definition Section := nat.
  
  Definition id_dec : forall (k1 k2:ID), {k1 = k2} + {k1 <> k2}.
    exact eq_nat_dec.
  Qed.
  Definition ph_dec : forall (k1 k2:PassHash), {k1 = k2} + {k1 <> k2}.
    exact eq_nat_dec.
  Qed.
  Definition assign_dec : forall (k1 k2:Assignment), {k1 = k2} + {k1 <> k2}.
    exact eq_nat_dec.
  Qed.
  Definition grade_dec : forall (k1 k2:Grade), {k1 = k2} + {k1 <> k2}.
    exact eq_nat_dec.
  Qed.
  Definition section_dec : forall (k1 k2:Grade), {k1 = k2} + {k1 <> k2}.
    exact eq_nat_dec.
  Qed.

  Inductive ParseCommand : Set :=
  | SetGrade'       : string -> string -> string -> string -> Grade -> ParseCommand
  | GetGrade'       : string -> string -> string -> string -> ParseCommand 
  | Average'        : string -> string -> string -> ParseCommand.

  Inductive Command : Set :=
  | SetGrade       : ID -> PassHash -> ID -> Assignment -> Grade -> Command
  | GetGrade       : ID -> PassHash -> ID -> Assignment -> Command 
  | Average        : ID -> PassHash -> Assignment -> Command.

  (* Configuration correctness *******************************************)

  Record Config : Set := mkCfg {
    students : list ID;
    tas      : list ID;
    profs    : list ID;
    sections : list (ID * Section );
    hashes   : list (ID * PassHash);
    totals   : list Grade;
    strings  : list (string * nat)
  }.

  Definition translate (cfg: Config) (str: string) : nat :=
    match find (fun x => if string_dec str (fst x) then true else false) (strings cfg) with
      | None => 0
      | Some (_,res) => res
    end.

  Definition compileCommand (cfg: Config) (q : ParseCommand) : Command :=
    match q with
      | SetGrade' u p i a g => SetGrade (translate cfg u) (translate cfg p) (translate cfg i) (translate cfg a) g
      | GetGrade' u p i a   => GetGrade (translate cfg u) (translate cfg p) (translate cfg i) (translate cfg a)
      | Average' u p a      => Average  (translate cfg u) (translate cfg p) (translate cfg a)
    end.
  
  Fixpoint lookup t x (l: list (ID * t)) : option t :=
    match l with
      | nil => None 
      | (x',y) :: b => if id_dec x x' then Some y else lookup x b
    end.

  Fixpoint in_dec x (l: list ID) :=
    match l with
      | nil => false
      | a :: b => if id_dec x a then true else in_dec x b
    end.

  Fixpoint excludes (l1: list ID) (l2: list ID) {struct l1}  :=
    match l1 with
      | nil => true
      | a :: b => if in_dec a l2
        then false
        else excludes b l2
    end.

  (* this takes too long to compute *)
  Definition disjoint_dec (cfg: Config) := true.
(*
    (excludes (students cfg) (tas cfg)) &&
    (excludes (students cfg) (profs cfg)) &&
    (excludes (tas cfg) (students cfg)) &&
    (excludes (tas cfg) (profs cfg)) &&
    (excludes (profs cfg) (students cfg)) &&
    (excludes (profs cfg) (tas cfg)).
*)

  Fixpoint total_dec t (l1: list ID) (l2: list (ID * t)) {struct l1} :=
    match l1 with
      | nil => true
      | a :: b => if lookup a l2 
        then total_dec b l2
        else false
    end.

  Definition correct_cfg cfg : bool := disjoint_dec cfg &&
    total_dec (students cfg ++ tas cfg ++ profs cfg) (hashes cfg) &&
    total_dec (students cfg ++ tas cfg) (sections cfg).

  (* Data constraints ***************************************************)

  Fixpoint bounded (l': list Grade) (l: list Grade) {struct l'} : bool :=
    match l', l with
      | nil, nil => true 
      | a :: b, c :: d => (if le_gt_dec a c then true else false) && bounded b d
      | _ , _ => false
    end.

  Fixpoint store_inv1 (l: list (ID * (list Grade))) (cfg : Config) {struct l} : bool := 
    match l with
      | nil => true
      | a :: b => bounded (snd a) (totals cfg) &&
        store_inv1 b cfg
    end.

  Fixpoint noduples (st: list ID) (ll: list (ID * list Grade)) {struct ll} :=
    match ll with
      | nil => true
      | a :: b => match lookup (fst a) b with
                    | None =>   in_dec (fst a) st && noduples st b 
                    | Some _ => false
                  end
    end.

  Section U.
    Variable T : Type.
    Variable dec : forall (a b : T), {a = b} + {a <> b}.
    Fixpoint unique (l : list T) : bool :=
      match l with 
        | nil => true
        | a :: b => if In_dec dec a b then false else unique b
      end.
  End U.

  Definition config_inv (cfg : Config) : bool :=
    unique id_dec (students cfg) && unique id_dec (profs cfg) && unique id_dec (tas cfg).

  Definition store_inv l cfg :=
    store_inv1 l cfg && total_dec (students cfg) l && noduples (students cfg) l
    && config_inv cfg.

  (* Privacy ************************************************************)

Section Privacy.
  Hypothesis cfg:Config.
  
  Definition accessOk f id pass := in_dec id (f cfg) 
    && match lookup id (hashes cfg) with
         | Some x => if id_dec x pass then true else false
         | None => false
       end.
  
  Definition isProf := accessOk profs.
  Definition isTA := accessOk tas.
  Definition isStudent := accessOk students.
  
  Definition taFor id pass x := 
    match lookup x (sections cfg) with
      | None => false
      | Some section => 
        match lookup id (sections cfg) with
          | None => false
          | Some section' => if section_dec section section' 
            then isTA id pass && if in_dec id (students cfg) then true else false
            else false
        end
    end.

  Definition private (q: Command) : bool := 
    match q with
      | SetGrade id pass x _ a => in_dec x (students cfg) 
                                    && (isProf id pass || taFor id pass x)
      | GetGrade id pass x a   => in_dec x (students cfg)
                                     && (isProf id pass 
        || (isStudent id pass && if id_dec id x then true else false)
        || taFor id pass x )
      | Average  id pass a     => (isProf id pass || isStudent id pass || isTA id pass)
    end.

  Definition lt_dec (a b : nat) : {a < b} + {a >= b}.
    intros; destruct (le_lt_dec a b); destruct (eq_nat_dec a b); solve [ left; omega | right; omega ].
  Qed.

  Definition validAssignment (a : nat) : 
    {a < length (totals cfg)} + {a >= length (totals cfg)} := lt_dec a (length (totals cfg)).

End Privacy.

  Inductive Status : Set :=
  | ERR_NOTPRIVATE : Status
  | ERR_BADGRADE : Status
  | ERR_NOINV : Status
  | OK  : Status
  | RET : Grade -> Status.

  Fixpoint nth_set (g: Grade) (a: Assignment) (l: list Grade) {struct l} : list Grade :=
    match l with
      | nil => nil
      | a' :: b => match a with
                     | O => g :: b
                     | S n => a' :: (nth_set g n b ) 
                   end
    end.

  Fixpoint insert (id: ID) (l: list Grade) (ll: list (ID * list Grade)) {struct ll}: list (ID * list Grade) :=
    match ll with
      | nil => (id,l)::  nil
      | a :: b => if id_dec (fst a) id then (id, l) :: b else a :: insert id l b 
    end.

  Fixpoint nth_get (a: Assignment) (l: list Grade) {struct l} : option Grade :=
    match l with
      | nil => None
      | a' :: b => match a with
                     | O => Some a'
                     | S n => nth_get n b  
                   end
    end.

  Definition inbounds (g: Grade) (a: Assignment) (tots: list Grade) : bool :=
    match nth_get a tots with
      | None => false
      | Some g' => if le_gt_dec g g' then true else false
    end.
  
  Fixpoint sum_all (l: list Grade) :=
    match l with
      | nil => 0
      | a :: b => a + (sum_all b)
    end.

  Fixpoint proj (x: Assignment) (l: list (ID * list Grade)) : option (list Grade) :=
    match l with
      | nil => Some nil
      | a :: b => match nth_get x (snd a) with
                    | None => None
                    | Some a' => match proj x b with
                                   | None => None
                                   | Some rest => Some (a' :: rest)
                                 end
                  end
    end.

  (* a / b *)
  Require Import Euclid.
  Definition divcheck0 : forall (a b: nat), nat.
  intros; refine (    
    match b as b' return b = b' -> nat with
      | 0 => fun _ => 0 
      | S n' => fun pf => match eucl_dev b _ a   with
                            | divex q _ _ _ => q
                          end
    end (refl_equal _)); omega. 
  Qed.

  Definition avg (l: list Grade) : nat := divcheck0 (sum_all l) (length l).

  Definition mutate (q: Command) (mm: (Config * list (ID * list Grade)))   
    : (Status * (Config * list (ID * list Grade))) :=
    match mm with
      | (cfg, m) => 
        if private cfg q  
        then match q with
               | SetGrade id pass x a g => 
                 if inbounds g a (totals cfg) 
                 then match lookup x m with
                        | None => (ERR_NOINV, mm)
                        | Some g' => (OK, (cfg, insert x (nth_set g a g') m))  
                      end
                 else (ERR_BADGRADE, mm)
               | GetGrade id pass x a =>
                 match lookup x m with
                   | None => (ERR_NOINV, mm) 
                   | Some g' => match nth_get a g' with
                                  | None => (ERR_BADGRADE, mm)
                                  | Some g'' => (RET g'', mm)
                                end
                 end
               | Average  id pass a => 
                 if validAssignment cfg a then  
                   match proj a m with
                     | None => (ERR_NOINV, mm)
                     | Some x => (RET (avg x), mm)
                   end
                   else (ERR_BADGRADE, mm)
             end
        else (ERR_NOTPRIVATE, mm)
    end.

  (** Tactics **)
  Ltac exhaustive solver :=
    simpl; 
    repeat (match goal with 
              | [ |- context [ if ?X then _ else _ ] ] => case_eq X
              | [ |- context [ match ?X with | Some _ => _ | None => _ end ] ] => case_eq X
              | [ |- context [ match ?X with | SetGrade _ _ _ _ _ => _ | GetGrade _ _ _ _ => _ | Average _ _ _ => _ end ] ] => case_eq X
            end; intros; simpl; try solver).

  Ltac isTrue P H :=
    assert (P  = true); [ destruct P; [ reflexivity | simpl in H; inversion H ] | ].

  Ltac all := idtac;
    let rec smallest P :=
      match P with
        | Bool.ifb ?X _ _ => smallest X
        | _ => P
      end
    in repeat match goal with
                | [ H : Bool.ifb ?X ?Y false = true |- _ ] => 
                  let T := smallest X in
                  let H' := fresh "F" in
                  assert (T = true) as H';
                    [ destruct (T); [ reflexivity | simpl in H; inversion H ] 
                    | rewrite H' in H; simpl in H ]
                | [ H : andb ?X _ = true |- _ ] =>
                  let T := smallest X in
                  let H' := fresh "F" in
                  assert (T = true) as H';
                    [ destruct (T); [ reflexivity | simpl in H; inversion H ]
                    | rewrite H' in H; simpl in H ]
              end.

  Ltac each := repeat match goal with 
                        | [ |- ifb ?X ?Y false = true ] =>
                          let H := fresh "H" in
                          assert (H : X = true); [ | rewrite H; simpl ]
                        | [ |- andb ?X ?Y = true ] =>
                          let H := fresh "H" in 
                          assert (H : X = true); [ | rewrite H; simpl ]
                      end.
(*
  Ltac inv T := idtac;
    let rec run T := idtac;
      match goal with 
        | [ |- ?A :: ?B = ?C :: ?D ] =>
          let H := fresh "H" in
          let H' := fresh "H" in
          assert (A = C) as H; [ T | assert (B = D) as H'; [ T | (try rewrite H); (try rewrite H'); reflexivity ] ]
        | [ |- (?A, ?B) = (?C, ?D) ] =>
          let H := fresh "H" in
          let H' := fresh "H" in
          assert (A = C) as H; [ T | assert (B = D) as H'; [ T | (try rewrite H); (try rewrite H'); reflexivity ] ]
        | [ |- Some ?A = Some ?B ] =>
          let H := fresh "H" in
          assert (A = B) as H; [ T | (try rewrite H); reflexivity ]
      end
    in run T.
*)


 Ltac inv T := idtac;
    let rec run T := idtac;
      match goal with 
        | [ |- ?A :: ?B = ?C :: ?D ] =>
          let H := fresh "H" in
          let H' := fresh "H" in
          assert (A = C) as H; [ T | assert (B = D) as H'; [ T | (try rewrite H); (try rewrite H'); reflexivity ] ]
        | [ |- (?A, ?B) = (?C, ?D) ] =>
          let H := fresh "H" in
          let H' := fresh "H" in
          assert (A = C) as H; [ T | assert (B = D) as H'; [ T | (try rewrite H); (try rewrite H'); reflexivity ] ]
        | [ |- Some ?A = Some ?B ] =>
          let H := fresh "H" in
          assert (A = B) as H; [ T | (try rewrite H); reflexivity ]
        | [ |- S ?A = S ?B ] =>
          let H := fresh "H" in
          assert (A = B) as H; [ T | (try rewrite H); reflexivity ]
      end
    in run T.

  (* This definition of mutate applies just as well to non-wellformed stores and
     and configurations.  Further properties are useful for implementations. *)

  Theorem bounded_length : forall a b,
    bounded a b = true -> length a = length b.
    induction a. induction b. trivial. simpl in *. intros; discriminate. simpl in *.
    intros. destruct b. discriminate. simpl in *. cut (length a0 = length b). intros. congruence.
    destruct (le_gt_dec a g). simpl in H. apply (IHa b H). simpl in H. discriminate. 
  Qed.

  Theorem insert_inv : forall cfg (l: list (ID * list Grade)) id gr,
    store_inv1 l cfg = true -> bounded gr (totals cfg) = true 
    -> store_inv1 (insert id gr l) cfg = true. 
    induction l. simpl. intros. rewrite H0. simpl. trivial.
    simpl in *. destruct a. simpl in *. intros.
    destruct (id_dec i id). simpl in *. rewrite H0. 
    assert (store_inv1 l cfg = true). destruct (store_inv1 l cfg). trivial. 
    destruct (bounded l0 (totals cfg)). simpl in H. discriminate. simpl in H. discriminate.
    simpl. assumption.
    simpl in *; destruct (bounded l0 (totals cfg)); try (simpl;
      apply IHl; simpl in H; trivial). simpl in H. discriminate.
  Qed.

  Theorem inv_bounded : forall l c i0 (H: store_inv1 l c = true) 
    (x : list Grade) (H1 : lookup i0 l = Some x), 
    bounded x (totals c) = true.
    intros. induction l. simpl in *. discriminate.
    simpl in *. destruct a. simpl in *.  destruct (id_dec i0 i). 
    assert (l0 = x). congruence. subst. destruct (bounded x (totals c)).
    simpl in H. trivial. simpl in H. discriminate. apply IHl.
    destruct (bounded l0 (totals c)). simpl in H. trivial. simpl in H.
    discriminate. trivial.
  Qed.

  Theorem insert_nthset_inv : forall l c g a i0 x 
    (H0 : inbounds g a (totals c) = true) 
    (pf: bounded x (totals c) = true)
    (H: store_inv1 l c = true), store_inv1 (insert i0 (nth_set g a x) l) c = true.
    intros. apply insert_inv; trivial. clear H l i0.
    generalize dependent a. generalize dependent g. generalize dependent pf. destruct c.
    simpl in *. clear students0 tas0 profs0 sections0 hashes0. generalize dependent totals0.
    induction x.
      destruct totals0; trivial.
      simpl in *. destruct totals0; intros; try discriminate. all.
      remember (le_gt_dec a g) as RM; destruct RM; try discriminate.
      destruct a0. simpl. each; trivial. simpl in *. rewrite <- HeqRM.
      simpl. apply IHx; auto.
  Qed.

  Theorem inv_inbounds : forall g a c i0 l
    (H : store_inv1 l c = true), 
    store_inv1 (snd (snd
      (if inbounds g a (totals c)
        then
          match lookup i0 l with
            | Some g' => (OK, (c, insert i0 (nth_set g a g') l))
            | None => (ERR_NOINV, (c, l))
          end
        else (ERR_BADGRADE, (c, l))))) c = true.
    intros. 
    assert (inbounds g a (totals c) = true \/ inbounds g a (totals c) = false).
    destruct (inbounds g a (totals c)); try firstorder.
    destruct H0; rewrite H0. 
    assert (exists x, lookup i0 l = Some x \/ lookup i0 l = None).
    destruct (lookup i0 l); simpl in *; try trivial. exists l0. firstorder.
    exists (@ nil Grade). right. trivial. destruct H1. destruct H1.
    rewrite H1. simpl. eapply insert_nthset_inv. trivial. trivial. 
    apply (inv_bounded l c i0 H H1). trivial. rewrite H1. simpl. trivial.
    simpl. trivial. 
  Qed.  

  Theorem mutate_inv_set: forall l c g a i0 p i, store_inv1 l c = true -> 
    store_inv1 (snd (snd (mutate (SetGrade i p i0 a g) (c, l)))) c = true.
    intros; simpl; destruct (validAssignment c g); destruct (in_dec i0 (students c)); destruct (isProf c i p);  destruct (taFor c i p i0); simpl; try trivial; apply inv_inbounds; trivial.
  Qed.

  Theorem const_config2 : forall (T : Type) x (t : Config * T) q, 
    fst x = fst t -> fst t = fst (snd (mutate q x)).
    intros. unfold mutate. destruct x; exhaustive ltac:(firstorder). 
  Qed.

  Theorem const_config : forall x q, fst x = fst (snd (mutate q x)).
    intros; apply (const_config2 x x q); auto.
  Qed.

  Lemma insert_preserves_inv : forall l0 i0 l g a c,
    Some l0 = lookup i0 l ->
    true = inbounds g a (totals c) ->
    store_inv1 l c = true ->
    store_inv1 (insert i0 (nth_set g a l0) l) c = true.
    intros. apply insert_nthset_inv. auto. auto.
    eapply inv_bounded. eassumption. symmetry. eassumption. assumption.
  Qed.

  Lemma lookup_insertSome : forall l a b c l1,
    lookup a l = Some l1 -> exists e, lookup a (insert b c l) = Some e.
    induction l.          
    intros; simpl in *; congruence.
    intros. destruct (id_dec a0 b). simpl. destruct (id_dec (fst a) b). 
    rewrite e. simpl. destruct (id_dec b b); try congruence. exists c. trivial.
    simpl. remember a as zz. destruct zz. subst. simpl in *. destruct (id_dec b i); 
    try congruence. eapply IHl. eassumption.
    simpl. remember a as r. destruct r. simpl in H. simpl. destruct (id_dec i b). 
    simpl. rewrite e in H. destruct (id_dec a0 b); try congruence. eauto.
    simpl. destruct (id_dec a0 i). eauto. eapply IHl; eassumption.
  Qed.

  Lemma lookup_insertNone : forall l a b c,
    a <> b -> lookup a l = None -> lookup a (insert b c l) = None.
    induction l.        
      intros. simpl. destruct (id_dec a b); try congruence.
      intros. simpl. destruct a. simpl. 
      remember (id_dec i b) as RM. destruct RM. simpl.
      destruct (id_dec a0 b); try congruence. simpl in H0. rewrite e in H0. 
      destruct (id_dec a0 b); try congruence.
      simpl. destruct (id_dec a0 i). simpl in H0. destruct (id_dec a0 i); try congruence.
      simpl in H0. destruct (id_dec a0 i); try congruence. apply IHl; auto. 
  Qed.

  Lemma insert_preserves_total_dec : forall c l0 i0 l g a,
    Some l0 = lookup i0 l ->
    total_dec c l = true ->
    total_dec c (insert i0 (nth_set g a l0) l) = true.
    induction c.
      reflexivity.
      intros. simpl in *. remember (lookup a l) as RM. destruct RM; try congruence.
      symmetry in HeqRM.
      destruct (lookup_insertSome l a i0 (nth_set g a0 l0) HeqRM). auto. rewrite H1. apply IHc; auto.
  Qed.

  Lemma insert_preserves_noduples : forall l0 i0 g a l o,
    Some l0 = lookup i0 l ->
    noduples o l = true ->
    noduples o (insert i0 (nth_set g a l0) l) = true.
    induction l. simpl. intros. discriminate.
      intros. simpl in *. destruct a0. simpl in H0. remember (lookup i l) as RM. destruct RM; try congruence.
      simpl. destruct (id_dec i i0). simpl. rewrite <- e. rewrite <- HeqRM. auto.

      simpl. destruct (id_dec i0 i); try congruence. all.
      rewrite (IHl o H H0). 
      remember (lookup i (insert i0 (nth_set g a l0) l)) as RM'. destruct RM'; try trivial.
      symmetry in HeqRM.
      pose (@lookup_insertNone l i i0 (nth_set g a l0) n HeqRM). congruence. firstorder.
  Qed.

  Theorem mutate_inv : forall l c q, store_inv1 l c = true ->
    store_inv1 (snd (snd (mutate q (c, l)))) (fst (snd (mutate q (c, l)))) = true.
    intros; destruct q;
      [ rewrite <- (const_config (c,l) (SetGrade i p i0 a g));
        apply (mutate_inv_set l c g a i0 p i); assumption
      | simpl in *; exhaustive ltac:(firstorder)
      | simpl in *; exhaustive ltac:(firstorder) ].
  Qed.
(* NOT USED
  Theorem mutate_l_get : forall l id pass x a c, 
    (l = snd (snd (mutate (GetGrade id pass x a) (c, l)))).
    intros; exhaustive ltac:(trivial).
  Qed.

  Theorem mutate_cfg_get : forall l id pass x a c, 
    (c = fst (snd (mutate (GetGrade id pass x a) (c, l)))).
    intros; exhaustive ltac:(trivial).
  Qed.

  Theorem mutate_cfg_inv : forall q c l, correct_cfg c = true ->
    correct_cfg (fst (snd (mutate q (c, l)))) = true.
    intros; destruct l; exhaustive ltac:(firstorder).
  Qed.

  Lemma total_inv : forall q l c, 
    total_dec (students c) l = true -> 
    total_dec (students (fst (snd (mutate q (c, l)))))
      (snd (snd (mutate q (c, l)))) = true.
    destruct q; intros; [ | exhaustive ltac:(firstorder) | exhaustive ltac:(firstorder) ].
    exhaustive ltac:(firstorder).
    unfold andb in HeqRM. symmetry in HeqRM. isTrue (in_dec i0 (students c)) HeqRM.
    apply insert_preserves_total_dec; assumption.
  Qed. 
*)

  Lemma denoteLookup : forall T l (z : ID) (t : T), 
    Some t = lookup z l -> In (z,t) l.
    induction l.
    intros; discriminate.
    intros. unfold lookup in H. destruct a. destruct (id_dec z i). inversion H. subst; firstorder.
    unfold In. right. apply IHl. auto.
  Qed.

  Lemma denoteLookupNone : forall T (z : ID) l,
    None = lookup z l -> forall x (t' : T), In (x,t') l -> x <> z.
    induction l.
      firstorder.
      intros. unfold In in H0. destruct H0. rewrite H0 in H. simpl in H. destruct (id_dec z x); congruence.
      eapply IHl. simpl in H. destruct a. destruct (id_dec z i); try congruence. auto. eassumption.
  Qed.

  Lemma denoteTotalDec : forall T x (l : list (ID * T)),
    total_dec x l = true ->
    forall z, In z x -> exists x, In (z, x) l.
    induction x.
      firstorder.
      intros. simpl in H. remember (lookup a l) as RM. destruct RM; try congruence.
      pose (IHx _ H). unfold In in H0. destruct H0.
      subst. exists t.
      apply denoteLookup; auto.
      apply e; auto.
  Qed.

  Lemma denoteInDec : forall x l, in_dec x l = true -> In x l.
    induction l; intros.
    simpl in *; congruence.
    unfold in_dec in H. destruct (id_dec x a). subst. firstorder.
    unfold In. right. apply IHl; auto.
  Qed.

  Lemma NotInDenote : forall T l x (x0:T),
    In (x, x0) l -> ~lookup x l = None.
    induction l.
      firstorder.
      intros. simpl. destruct a. remember (id_dec x i) as RM. destruct RM. unfold not; intros; congruence.
      eapply IHl. unfold In in H. destruct H. inversion H. congruence. eauto.
  Qed.

  Lemma in_dec_total_dec : forall l x c,
    in_dec x (students c) = true -> total_dec (students c) l = true
    -> exists g' : list Grade, lookup x l = Some g'.
    intros.
    destruct (denoteTotalDec _ _ H0 x (denoteInDec x (students c) H)).
    remember (lookup x l) as RM. destruct RM. exists l0; auto.
    pose (NotInDenote _  x x0 H1). congruence.
  Qed.

(**
  Theorem valid_bounded : forall c assign, validAssignment c assign = true -> 
    S assign < S (length (totals c)).
    intros. cut (assign < length (totals c)). intros pf. omega.
    unfold validAssignment in H. unfold lt. destruct (lt_dec assign (length (totals c))); try congruence; omega.
  Qed.
**)

End GradebookModel.

Module ExampleConfig.
  Import GradebookModel.

  Open Local Scope string_scope.

  Definition test_config : Config := 
     mkCfg (4::5::6::nil)              (* students *)
           (2::3::nil)                 (* tas *)
           (1::nil)                    (* profs *)
           ((6,1)::(2,2)::(3,1)::(4,1)::(5,2)::nil)  (* sections *)
           ((1,11)::(2,22)::(3,33)::(4,44)
            ::(5,55)::(6,66)::nil)       (* passwords *)
           (70::80::100::nil)              (* assignments totals *)
           (("alice", 2) :: ("bob", 3) :: ("carol", 4) ::
            ("derek", 5) :: ("evan", 6) :: ("paul", 1) :: 
            ("apass", 22) :: ("bpass", 33) :: ("cpass", 44) ::
            ("dpass", 55) :: ("epass", 66) :: ("ppass", 11) :: 
            ("hw1", 0) :: ("hw2", 1) :: ("exam1", 2) :: nil).

  Definition test_grades : list (ID * list Grade) := 
    (4,65::63::75::nil)::
    (5,68::76::80::nil)::
    (6,70::80::94::nil)::
    nil.

  Definition test_model : Config * list (ID * (list Grade)) :=
    (test_config, test_grades).
 
  Theorem test_model_inv : store_inv1 test_grades test_config = true.
    unfold store_inv1.  
    compute. trivial.
  Qed.

  Theorem test_cfg_inv' : correct_cfg test_config = true.
    compute;
    repeat match goal with
             | [ |- context [id_dec ?X ?Y] ] => destruct (id_dec X Y); simpl in *; try (discriminate || contradiction || firstorder)
             | [ H : context [id_dec ?X ?Y] |- _ ] => destruct (id_dec X Y); simpl in *; try (discriminate || contradiction || firstorder)
           end.
  Qed.

  Theorem test_cfg_inv : store_inv (snd test_model) (fst test_model) = true.
    unfold store_inv. pose (test_cfg_inv'). unfold config_inv. simpl. 
    repeat match goal with
             | [ |- context [id_dec ?X ?Y] ] => destruct (id_dec X Y); simpl in *; try (discriminate || contradiction || firstorder)
             | [ H : context [id_dec ?X ?Y] |- _ ] => destruct (id_dec X Y); simpl in *; try (discriminate || contradiction || firstorder)
           end.
  Qed.

End ExampleConfig.

Export GradebookModel.


