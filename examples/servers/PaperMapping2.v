Require Import Ynot.
Require Import GradebookModel. (* change this module name or move to here *)
Require Import List.
Require Import GradebookStoreImpl.
Require Import Store.
Require Import RSep.
Require Import AppServer.
Require Import IO.

Set Implicit Arguments.

Axiom shift : forall (P:Prop), (STsep [P] (fun pf : P => [P]))%hprop.

(* ***************************************************************************************** *)
(* Framework *)

Module Type Model.
  Parameter M : Config -> Type.
  Parameter I : forall (cfg : Config), M cfg -> Prop.
  Parameter mutate     : forall (cfg: Config) (m: M cfg)            (q: Command), (Status * M cfg).
  Parameter PreservesI : forall (cfg: Config) (m: M cfg) (pfI: I m) (q: Command), I (snd (mutate m q)).
End Model.

(** A morphism between models **)
Module Type ModelHomomorphism (* (S : Model) (T : Model) *).
(* h (S.mutate x) = T.mutate (h x) *)
  Declare Module S : Model.
  Declare Module T : Model.

  Parameter h : forall (cfg: Config), S.M cfg -> T.M cfg.
   
  Parameter InvPres : forall cfg (m: S.M cfg), S.I m -> T.I (h m).

  Parameter ObserveEq : forall cfg (m: S.M cfg), S.I m ->
    forall q, fst (S.mutate m q) = fst (T.mutate (h m) q).

  Parameter StatePres : forall cfg (m: S.M cfg), S.I m ->
    forall q, h (snd (S.mutate m q)) = snd (T.mutate  (h m) q).
End ModelHomomorphism.

(** This is an implementation of the S Model using the T Model **)
Module Type Impl.
  Declare Module Cert : ModelHomomorphism.
  Module Spec := Cert.T.
  Module Impl := Cert.S.

  Parameter T   : Type.
  Parameter rep : forall (cfg: Config) (t: T) (m: Impl.M cfg), hprop.

  Open Local Scope hprop_scope.
  (** This should be in terms of Impl **)
  Parameter imp_mutate : forall cfg (t: T) q (m: [Impl.M cfg]),
    STsep (m ~~ rep t m * [Impl.I m]) 
          (fun r : Status => m ~~ let (r', m') := (Impl.mutate m q)
                                  in  [r' = r] * rep t m' * [Impl.I m']).

  Parameter init :
    STsep (__)
          (fun tm : T * sigT (fun cfg => inhabited (Impl.M cfg)) => hprop_unpack (projT2 (snd tm)) (fun m => rep (fst tm) m * [Impl.I m])).


  Parameter cleanup : forall (cfg : Config) (t : T) (m : [Impl.M cfg]),
    STsep (m ~~ rep t m * [Impl.I m])
          (fun _:unit => __).

End Impl.

(* Deploy an implementation based on a specification *)
Module BuildApp (Y': Impl) : App.
  Module Y := Y'.
  Open Local Scope hprop_scope.

  Definition Q := Command.
  Definition T  : Type := (Config * Y.T)%type.
  Definition RR : Set  := Status.
  Definition M := sigT (fun cfg : Config => Y.Impl.M cfg).
  Definition rep (t: T) (m: M) : hprop :=
    [fst t = projT1 m] * Y.rep (snd t) (projT2 m).

  Definition I (m: M) : Prop := Y.Cert.T.I (Y.Cert.h (projT2 m)).
 
  Definition func (q: Q) (m: M) : (RR * M) := 
    match Y.Impl.mutate (projT2 m) q with
      | (r, m') => (r, (@existT Config (fun cfg : Config => Y.Impl.M cfg)) (projT1 m) m')
    end.

  Definition AppIO (_ : Q) (_ : M) (_ : RR) (_ : M) : Trace := nil.

  Theorem cast : forall (T U : Type) (t : T) (pf: T = U), U.
    intros.  subst. auto.
  Qed.

  Open Local Scope stsepi_scope.

  Definition inhabit_unpack' T U (inh : [T]) (f: forall t:T, [t]%inhabited = inh -> U) : [U].
    intros. refine (
    match inh as inh' return inh' = inh -> _ with
      | inhabits v => fun pf => inhabits (f v pf)
    end (refl_equal _)).
  Qed.
  Theorem pfCast : forall (t : T)  (m : [M])  (pf : [fst t]%inhabited = (m ~~~ projT1 m))  (m0 : M),
    [m0]%inhabited = m -> Y.Impl.M (projT1 m0) = Y.Impl.M (fst t).
  Proof.
    intros. rewrite <- H in *. simpl in *. rewrite <- (pack_injective pf). auto.
  Qed.

  Definition build : forall (t : T) (m : [M]), 
    STsep (m ~~ [fst t = projT1 m])
          (fun res : [Y.Impl.M (fst t)] => m ~~ [fst t = projT1 m]).
    intros. refine (pf <- shift ([fst t]%inhabited = (m ~~~ projT1 m)) <@> _ ; 
                    {{ Return (@inhabit_unpack' _ _ m 
                                 (fun m pf' => @cast _ _ (projT2 m) _)) }}).
    unfold rep. rsep fail auto. rewrite H0. rsep fail auto.
    rsep fail auto.
    rsep fail auto.
    instantiate (1 := (@pfCast t m pf m0 pf')). rsep fail auto.
    sep fail auto.
  Qed.

  Definition exec (t : T) (q : Q) (m : [M]) (tr : [Trace]) :
    STsep (tr ~~ m ~~ rep t m * traced tr * [I m]) 
          (fun r : RR => tr ~~ m ~~ 
            let m' := snd (func q m)
            in  [r = fst (func q m)] * rep t m' * [I m'] * 
            traced (AppIO q m r m' ++ tr)).
    intros.
    refine (pf <- shift ([fst t]%inhabited = (m ~~~ projT1 m)) <@> _ ;
            {{ @Y.imp_mutate (fst t) (snd t) q
                  (@inhabit_unpack' _ _ m (fun m0 pf' => @cast _ _ (projT2 m0) (@pfCast t m pf m0 pf'))) <@> _ }}).
    unfold rep; rsep fail auto. rewrite H1. rsep fail auto.
    rsep fail auto.
    unfold I. unfold Y.Impl.M. unfold Y.Impl.I.    
    pose (pack_type_inv m). instantiate (1 := tr ~~ traced tr).
    sep fail auto.
(* NEW
    pose (@inhabit_unpack M (Y.Cert.T.M (fst t)) m (fun m => @Y.Cert.h (projT1 m) (projT2 m))).
    pose (@Y.imp_mutate (fst t) (snd t) q (m ~~~ @Y.Cert.h (projT1 m) (projT2 m))).
*)
(* OLD
    intros; refine ({{ Y.imp_mutate (fst t) (snd t) q (m ~~~ snd m) <@> (tr ~~ m ~~ [fst t = fst m] * traced tr * [I m]) }}).
    unfold rep. unfold I. rsep fail auto. rewrite H1. rsep fail auto.
    unfold rep. unfold I. rsep fail auto. subst.
    assert (snd x0 = x1). sep fail auto. subst. rsep fail auto. rewrite H3 in *. unfold func. 
    remember (Y.M.mutate (fst x0) (snd x0) q) as pf.
    destruct pf. simpl in *. rsep fail auto. pose (pf2 := Y.M.PreservesI H2 q). rewrite <- Heqpf in pf2. simpl in pf2.
    rsep fail auto.
*)
  Admitted.
 
  Definition init :
    STsep (__)
          (fun tm : T * [M] => hprop_unpack (snd tm) (fun m => rep (fst tm) m * [I m])).
    refine (res <- Y.init ;
            {{ Return ((projT1 (snd res), (fst res)), _) }}).
    rsep fail auto. rsep fail auto. rsep fail auto.  unfold M.
  Admitted.

  Definition cleanup : forall (t : T) (m : [M]),
    STsep (m ~~ rep t m * [I m])
          (fun _:unit => __).
  Admitted.

  Definition func_preserves_I : forall q m, I m -> I (snd (func q m)).
  Admitted.

End BuildApp. 



(* *************************************************************************** *)
(* Specification *)

Module Spec <: Model.
  Definition M (_:Config) : Type := list (ID * list Grade).
  Definition I (cfg : Config) (m : M cfg) : Prop :=
    store_inv m cfg = true.

  Definition mutate (cfg: Config) (m : M cfg) (q: Command) : (Status * M cfg) :=
    if private cfg q
    then match q with
           | SetGrade id pass x a g => 
             if inbounds g a (totals cfg) 
             then match lookup x m with
                    | None => (ERR_NOINV, m)
                    | Some g' => (OK, insert x (nth_set g a g') m)  
                  end
             else (ERR_BADGRADE, m)
           | GetGrade id pass x a =>
             match lookup x m with
               | None => (ERR_NOINV, m) 
               | Some g' => match nth_get a g' with
                              | None => (ERR_BADGRADE, m)
                              | Some g'' => (RET g'', m)
                            end
             end
           | Average  id pass a => 
             if validAssignment cfg a then  
               match proj a m with
                 | None => (ERR_NOINV, m)
                 | Some x => (RET (avg x), m)
               end
               else (ERR_BADGRADE, m)
         end
      else (ERR_NOTPRIVATE, m).

  Theorem PreservesI : forall (cfg: Config) (m : M cfg) (pfI: I m) (q: Command),
    I (snd (mutate m q)).
  Proof.
    unfold I. intros. unfold mutate.
    destruct q;
      [ exhaustive assumption
      | simpl in *; exhaustive assumption
      | simpl in *; exhaustive assumption ].
    unfold store_inv in *. symmetry in HeqRM. all.
    Hint Resolve insert_preserves_noduples.
    Hint Resolve insert_preserves_total_dec.
    Hint Resolve insert_preserves_inv.
    each; auto.
  Qed.

End Spec.

(** Spec is isomorphic to itself **)
Module SpecHomomorphism : ModelHomomorphism with Module S := Spec with Module T := Spec.

  Module S := Spec.
  Module T := Spec.

  Definition h (cfg: Config) (m: S.M cfg) : T.M cfg := m.
   
  Theorem InvPres : forall cfg (m: S.M cfg), S.I m -> T.I (h m).
  Proof.
    unfold h; auto.
  Qed.

  Theorem ObserveEq : forall cfg (m: S.M cfg), S.I m ->
    forall q, fst (S.mutate m q) = fst (T.mutate (h m) q).
  Proof.
    unfold h; auto.
  Qed.

  Theorem StatePres : forall cfg (m: S.M cfg), S.I m ->
    forall q, h (snd (S.mutate m q)) = snd (T.mutate  (h m) q).
  Proof.
    unfold h; auto.
  Qed.

End SpecHomomorphism.


(* **************************************************************************************** *)
(* Store Implementation *)
(**
Module StoreImplModel <: Model.
  Import StoreModel.
  Import GradesStoreMapping.

  Definition M (cfg : Config) : Type := Table (S (length (totals cfg))).
  Definition I (cfg : Config) (m : M cfg) : Prop :=
    store_inv (Table2List m) cfg = true.

  Definition mutate (cfg: Config) (m : M cfg) (q: Command) : (Status * M cfg) :=
    if private cfg q
    then match q with
           | SetGrade id pass x a g =>
             if inbounds g a (totals cfg)
               then (OK, update (set_query x a g) m)
               else (ERR_BADGRADE, m)
           | GetGrade id pass x a =>
             (match nthget a (select (get_query x cfg) m) with 
                | None => ERR_NOINV
                | Some None => ERR_BADGRADE
                | Some (Some g') => RET g'
              end, m)
           | Average  id pass assign =>
             (match validAssignment cfg assign with
                | right _ => ERR_BADGRADE
                | left pfx2 =>
                  let projs := project (GET_COL (Lt.lt_n_S _ _ pfx2)) m in
                  let agg := aggregate (fun (a : nat) (x0 : Tuple 1) => fst x0 + a) 0 projs in
                  RET (divcheck0 agg (length (students cfg)))
              end, m)
         end
      else (ERR_NOTPRIVATE, m).

  Lemma InvDenote : forall cfg m,
    store_inv1 m cfg = true
    -> forall x, In x m -> length (snd x) = length (totals cfg).
    induction m.
      simpl. intros. inversion H0.
      intros. simpl in *; all; destruct H0.
        subst; apply bounded_length; auto.
        apply IHm; auto.
  Qed.

  Lemma Table2List_List2Table : forall m l,
    (forall x, In x m -> length (snd x) = l) ->
    Table2List (List2Table m l) = m.
    induction m.
      auto.
      intros. assert (length (snd a) = l). apply H; apply in_eq.
      simpl. destruct a. inv auto. simpl. inv auto. clear H. generalize dependent l0. clear.
      induction l.
        simpl. destruct l0; simpl in *; auto; congruence.
        simpl. destruct l0. simpl. intros. congruence. simpl. intros. inv auto.
  Qed.

  Lemma dec : forall (a b : ID * list Grade), {a = b} + {a <> b}.
    do 3 decide equality.
  Qed.

  Theorem PreservesI : forall (cfg: Config) (m : M cfg) (pfI: I m) (q: Command),
    I (snd (mutate m q)).
  Proof.
    intros. unfold mutate. unfold I in *. destruct q; exhaustive auto. 
    pose (@SetGrade_OK_store (cfg, Table2List m) i p i0 a g). simpl in e. rewrite List2Table_Table2List in e. rewrite e; try solve [ subst; auto ]. clear e.
    rewrite <- HeqRM. rewrite <- HeqRM0. destruct (@private_lookup i0 (Table2List m) cfg i p a g); auto. subst. auto.
    rewrite H. simpl. rewrite Table2List_List2Table.
    unfold store_inv in *. all.
    Hint Resolve insert_preserves_total_dec.
    Hint Resolve insert_preserves_noduples.
    Hint Resolve insert_preserves_inv.
    each; auto.
    assert (length (nth_set g a x) = length (totals cfg)).
    cut (length x = length (totals cfg)).
    clear. destruct cfg. simpl. clear. generalize dependent totals0. generalize dependent a. 
    induction x.
      auto.
      simpl; intros. destruct totals0; try (simpl in *; congruence). simpl in *. 
        destruct a0. auto. simpl. rewrite (IHx a0 totals0); auto.
    unfold store_inv in pfI. all. generalize F1 H. clear. generalize m. generalize cfg. clear.
    induction m.
      simpl. congruence.
      destruct a. simpl. intros. all. destruct (id_dec i0 n).
        inversion H. rewrite H1 in *. apply bounded_length; auto.
        apply IHm; auto.
    unfold store_inv in *. all. generalize (InvDenote _ _ F1). 
    generalize H. generalize H0. generalize x. generalize m. generalize cfg. clear.
    induction m.
      simpl. congruence.
      simpl. destruct a0. simpl. intros. destruct (id_dec n i0); destruct (id_dec i0 n); try congruence.
        inversion H. rewrite H4 in *. 
        apply (decideable_in _ dec) in H2. destruct H2. rewrite <- H2. simpl; auto. eapply H1; eauto. right; tauto.
        destruct H2. apply H1. left; auto.
        eapply IHm; eauto. 
  Qed.
      
End StoreImplModel.

(** A morphism between models **)
Module StoreHomomorphism : ModelHomomorphism with Module S := Spec
                                             with Module T := StoreImplModel.
  Module S := Spec.
  Module T := StoreImplModel.
  Import StoreModel.
  Import GradesStoreMapping.

  Definition h (cfg : Config) (sm : S.M cfg) : T.M cfg :=
    List2Table sm (length (totals cfg)).
   

  Lemma decideable_in : forall T (dec : forall a b : T, {a = b} + {a <> b}) (a x : T) b,
    In x (a :: b) -> a = x \/ (x <> a /\ In x b).
    intros. destruct (dec x a); auto. 
    right. destruct H. congruence. auto.
  Qed.

  Lemma dec : forall (a b : ID * list Grade), {a = b} + {a <> b}.
    do 3 decide equality.
  Qed.

  Theorem InvPres : forall cfg (m: S.M cfg), S.I m -> T.I (h m).
  Proof.
    intros; unfold T.I, S.I,h in *. rewrite T.Table2List_List2Table; auto.
    intros. unfold store_inv in H. all. clear F F0 H. destruct x. induction m.
      simpl in *. firstorder.
      apply (decideable_in dec) in H0.
      simpl in *. destruct H0. subst. all. simpl in *. apply bounded_length; auto. 
        destruct H. apply IHm; auto. all. auto.
  Qed.

  (* h (S.mutate x) = T.mutate (h x) *)
  Opaque GET_COL.
  Theorem ObserveEq : forall cfg (m: S.M cfg), S.I m ->
    forall q,  fst (S.mutate m q) = fst (T.mutate  (h m) q).
  Proof.
    intros. unfold S.I in *. unfold S.mutate, T.mutate. simpl projT1. simpl projT2.
    remember (private cfg q) as PVT; destruct PVT; auto.
    destruct q.
      (** SET **)
      destruct (inbounds g a (totals cfg)); auto. simpl. destruct (private_lookup i0 m cfg i p a g); auto. rewrite H0. auto.
      (** GET **)
      unfold h.
      destruct (private_lookup i0 m cfg i p a 0); auto. rewrite H0.
      pose (grade_count _ _ H _ H0). symmetry in e. destruct (lookup_select m cfg i0 H0). rewrite H1. simpl.
      remember (nthget' _ a (List2Tuple' x (length (totals cfg)))) as NTH. destruct NTH. symmetry in HeqNTH.
      rewrite (@gg_ret _ _ _ _ e HeqNTH). auto. 
      symmetry in HeqNTH. rewrite (gg_bad _ _ e HeqNTH). auto.
      (** AVG **)
      unfold h. simpl. destruct (validAssignment cfg a); auto.
      pose (@AvgRet (RET
        (divcheck0
          (aggregate (fun (a0 : nat) (x0 : Tuple 1) => fst x0 + a0) 0
            (project (GET_COL (Lt.lt_n_S a (length (totals cfg)) l))
              (List2Table m (length (totals cfg))))) 
          (length (students cfg)))) (project (GET_COL (Lt.lt_n_S a (length (totals cfg)) l))
            (List2Table m (length (totals cfg)))) (aggregate (fun (a0 : nat) (x0 : Tuple 1) => fst x0 + a0) 0
              (project (GET_COL (Lt.lt_n_S a (length (totals cfg)) l))
                (List2Table m (length (totals cfg))))) m cfg a i p l). unfold Tuple in e. rewrite e; auto. clear e. 
      simpl. simpl in HeqPVT. rewrite <- HeqPVT. destruct (validAssignment cfg a). destruct (proj a m); auto. elimtype False. omega.
  Qed.

  Theorem StatePres : forall cfg (m: S.M cfg), S.I m ->
    forall q, h (snd (S.mutate m q)) = snd (T.mutate (h m) q).
  Proof.
    unfold S.I, S.mutate, T.mutate, h. simpl projT1; simpl projT2.
    intros; remember (private cfg q) as PVT; destruct PVT; auto.
    destruct q;
      [ | exhaustive auto | exhaustive auto ].
      remember (inbounds g a (totals cfg)) as IB; destruct IB; auto.
      pose (@SetGrade_OK_store (cfg,m) i p i0 a g). simpl in e. rewrite e; auto. clear e.
      destruct (private_lookup i0 m cfg i p a 0); auto. rewrite H0. simpl.
      unfold h. simpl in HeqPVT. rewrite <- HeqPVT. auto. rewrite <- HeqIB. auto.
  Qed.

End StoreHomomorphism.

Module GbStoreImpl  (s: Store)  <: Impl. (* had name clash *)
  Module M := StoreImplModel.
  Export M.
  Definition T := s.t.
  Open Scope hprop_scope.

  Definition rep (cfg : Config) (t: T) (m: M.M cfg) : hprop :=
    s.rep t m.

  Open Local Scope hprop_scope.

  Definition imp_mutate : forall cfg (t: T ) q (m: [M.M cfg]),
    STsep (m ~~ rep t m * [M.I m] ) 
          (fun r : Status => m ~~ let (r', m') := (M.mutate m q)
                                  in  [r' = r] * rep t m').
    intros.
  Admitted.

End GbStoreImpl.


(* ************************************************************************************************ *)
(* Certification *)

Module CertifiedImpl (s: Store) : Impl.
 Module M := Spec.
 Module TheImpl := GbStoreImpl s.
 Definition T := TheImpl.T.
 Definition rep (cfg : Config) (t: TheImpl.T) (m: Spec.M cfg) : hprop :=
   @TheImpl.rep cfg t (StoreHomomorphism.h m).

 Open Scope hprop_scope.
 Definition imp_mutate : forall cfg (t: T) q (m: [M.M cfg]),
    STsep (m ~~ @rep cfg t m * [M.I m] ) 
          (fun r : Status => m ~~ let (r', m') := (M.mutate m q)
                                  in  [r' = r] * @rep cfg t m').
    refine (fun cfg t q m =>
      {{ TheImpl.imp_mutate t q (m ~~~ @StoreHomomorphism.h cfg m) }}).
    
    unfold rep, TheImpl.rep,M.I. rsep fail auto. pose (@StoreHomomorphism.InvPres cfg x H0). rsep fail auto.
    unfold rep. rsep fail auto. (** TODO: Generalization required here **)
 Admitted.

End CertifiedImpl.


Module someStore : Store := ListStore.
Module theImpl : Impl := GbStoreImpl someStore.
Module theApp : App := BuildApp theImpl.

(*
Module StoreImpl <: Impl with Module M := TupleModel.
  Module M := TupleModel.
End StoreImpl.


(* these wrappers may come in handy 
   for above. *)
Module WrapModel (X: Model).
  Export X.

  Definition wrap cfg q m (pf_I: I cfg m) :=
    match P_dec cfg q with
      | left  pf_P => match E_dec cfg q with
                        | left  pf_E => mutate cfg q m  
                        | right pf_badgrade => (ERR_BADGRADE, m) 
                      end
      | right pf_notpriv => (ERR_NOTPRIVATE, m)
    end.
End WrapModel.

Require Import Ynot.
Module WrapImpl (X: Model) (Y: Impl).
 Module Z := Y X.
 Export Z.
 Module W := WrapModel X.
 Export W.

 Open Local Scope stsepi_scope.
 Open Local Scope hprop_scope.
 Definition imp_wrap cfg t q m : 
  STsep (m ~~ rep t m * [I cfg m] * [P cfg q] * [E cfg q]) 
   (fun r : Status => m ~~ Exists pf1 :@ I cfg m, 
                           let (r', m') := (wrap q pf1 )
                           in  [r' = r] * rep t m').
 Admitted. 
End WrapImpl.

Require Import Ynot.
 


Require Import Store.

(* And we need to do this as well
Module StoreImpl (s: Store) : Impl TupleModel .
 
End StoreImpl.
*)
**)

(**
Module Test (H: ModelHomomorphism). (* sanity check *)
 Export H.
  Theorem thm1 : forall cfg (m: S.M cfg) q, S.I m -> T.I (snd (T.mutate (h m) q)).
   intros. apply T.PreservesI. pose (hCorrect H). destruct a. assumption.
 Qed.
End Test.
**)

**)