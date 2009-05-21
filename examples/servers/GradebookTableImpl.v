Require Import Ynot RSep.
Require Import Store GradebookApp.

Module GradesTableMapping.
  Export StoreModel.
  Open Scope hprop_scope.

  Definition Tbl := sigT (fun cfg: Config => Table (S (length (totals cfg)))).

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
     | a :: b => Tuple2List n a :: Table2List n b
   end.

  Definition Tbl2M (tbl: Tbl) : (Config * list (ID * (list Grade))) :=
    (projT1 tbl, Table2List ((length (totals (projT1 tbl)))) (projT2 tbl)).   
  
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
  
  Definition M2Tbl (m: (Config * list (ID * (list Grade)))) 
   : Tbl := existT _ (fst m)  (List2Table (snd m) (length (totals (fst m)))).

  Theorem TLT_id : forall x, Tuple2List (length (snd x)) (List2Tuple x (length (snd x))) = x.
    intros. unfold Tuple2List. unfold List2Tuple. 
    destruct x. induction l. simpl. trivial. simpl in *. 
    assert (Tuple2List' (length l) (List2Tuple' l (length l)) = l).
    injection IHl. trivial. rewrite H. trivial. 
  Qed.

  Theorem TblMTbl_id: forall x, store_inv1 (snd x) (fst x) = true -> Tbl2M (M2Tbl x) = x.
    intros. destruct x. unfold M2Tbl. unfold Tbl2M. simpl in *.  
    cut (Table2List (length (totals c)) (List2Table l (length (totals c))) = l). intros H0. congruence.
    induction l. trivial. simpl in *.
    assert (bounded (snd a) (totals c) = true). destruct (bounded (snd a) (totals c)); trivial.
    pose (TLT_id a). 
    cut (length (snd a) = length (totals c)). intros HH.
    rewrite <- HH in *. 
    rewrite e. 
    assert (store_inv1 l c = true). destruct (store_inv1 l c). trivial.
    destruct (bounded (snd a) (totals c)). simpl in H. discriminate. simpl in H. discriminate.  
    assert (Table2List (length (snd a)) (List2Table l (length (snd a))) =l). apply (IHl H1).
    rewrite H2. trivial. apply bounded_length.
    destruct (bounded (snd a) (totals c)). trivial. discriminate. 
  Qed.

  Definition mutate' (q: Command) (x: Tbl)  : (Status * Tbl). intros.
  pose (x' := mutate q (Tbl2M x)). 
  pose (p :=  M2Tbl (snd x')). 
    simpl in *. exact (fst x', p). 
  Defined.  

   Lemma List2Tuple'_Tuple2List' : forall n t,
     List2Tuple' (Tuple2List' n t) n = t.
     induction n.
     intros; destruct t; auto.
     intros. simpl. rewrite IHn. destruct t. auto.
   Qed.

 Lemma List2Tuple_Tuple2List : forall n a,
   List2Tuple (Tuple2List n a) n = a.
   destruct n.
   intros; unfold List2Tuple,Tuple2List. simpl. destruct a. destruct t. auto.
   intros. unfold List2Tuple,Tuple2List. destruct a.
   simpl. rewrite List2Tuple'_Tuple2List'. destruct t; auto.
 Qed.

 Lemma List2Table_Table2List : forall n l,
   List2Table (Table2List n l) n = l.
   induction l. reflexivity.
   simpl.
   rewrite List2Tuple_Tuple2List. rewrite IHl. trivial.
 Qed.

End GradesTableMapping.

(* Reference to (config, table) which is mapped to the logical model. *)
Module GradebookTableImpl : GradebookImpl.
  Export GradesTableMapping.
  Open Scope hprop_scope.
  Open Scope stsepi_scope.

  Definition T := ptr.
  
  Definition rep (t: T) (m: (Config * list (ID * (list Grade)))) : hprop 
   := t --> M2Tbl m.
  
  Definition exec' : forall (t : T) (q : ParseCommand) (m : [(Config * list (ID * (list Grade)))]),
    STsep (m ~~ rep t m * [store_inv (snd m) (fst m) = true] ) 
          (fun r : Status => m ~~ [r  = fst (mutate (compileCommand (fst m) q) m)] * rep t (snd (mutate (compileCommand (fst m) q) m)) * 
            [store_inv (snd m) (fst m) = true] ).
    intros; refine (
      x <- ! t  ;
      let res := mutate' (compileCommand (projT1 x) q) x in
      t ::=   snd res ;;
      {{ Return (fst res) }}); unfold rep.
    sep fail auto; unfold rep; rsep fail auto.
    sep fail auto.
    sep fail auto.
    sep fail auto.
    rsep fail auto. unfold rep. rsep fail auto. 
    unfold mutate' in *. rewrite H in *.
    unfold store_inv in H1. assert (store_inv1 (snd x0) (fst x0) = true).
     destruct (store_inv1 (snd x0) (fst x0)). trivial. simpl in H1. discriminate.
    unfold res. norm_prod. rsep fail auto. unfold rep. rewrite H0.
    rewrite (TblMTbl_id x0 H3) in *. rsep fail auto. 
  Qed.

  Export ExampleConfig.
  Definition init :
    STsep (__)
          (fun tm : T * [(Config * list (ID * (list Grade)))] =>
            hprop_unpack (snd tm) 
            (fun m => rep (fst tm) m * [store_inv (snd m) (fst m) = true])).
    unfold rep. refine ( x <- New (M2Tbl test_model) ;
    {{ Return (x, inhabits test_model ) }} ); pose test_cfg_inv;
    sep fail auto. 
  Qed.

  Definition cleanup (t : T) (m : [(Config * list (ID * (list Grade)))]) :
    STsep (m ~~ rep t m * [store_inv (snd m) (fst m) = true])
          (fun _:unit => __).
    intros. refine {{Free t}}.
    unfold rep. sep fail auto.
    rsep fail auto.
  Qed.

End GradebookTableImpl.

Module theApp : App := GradebookApp.Gradebook GradebookTableImpl.
