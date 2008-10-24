Require Import List.

Require Import Ynot.Axioms.
Require Import Ynot.Util.
Require Import Ynot.Heap.
Require Import Ynot.Hprop.
Require Import Ynot.ST.

Set Implicit Arguments.


Notation "{{{ v }}}" := (STWeaken _ (STStrengthen _ v _) _) (at level 0).

Definition STsep pre T (post : T -> hprop) : Set :=
  ST (pre * ??) (fun h v h' =>
    forall h1 h2, h ~> h1 * h2
      -> pre h1
      -> exists h1', h' ~> h1' * h2
        /\ post v h1').

Arguments Scope STsep [hprop_scope type_scope hprop_scope].


Ltac hreduce :=
  repeat match goal with
           | [ |- (hprop_inj _) _ ] => red
           | [ |- (hprop_cell _ _) _ ] => red
           | [ |- (hprop_sep _ _) _ ] => red
           | [ |- hprop_empty _ ] => red
           | [ |- hprop_any _ ] => red
           | [ |- (hprop_ex _) _ ] => red

           | [ H : (hprop_inj _) _ |- _ ] => red in H
           | [ H : (hprop_cell _ _) _ |- _ ] => red in H
           | [ H : (hprop_sep _ _) _ |- _ ] => red in H
           | [ H : hprop_empty _ |- _ ] => red in H
           | [ H : hprop_any _ |- _ ] => clear H
           | [ H : (hprop_ex _) _ |- _ ] => destruct H

           | [ H : ex _ |- _ ] => destruct H

           | [ H : _ ~> empty * _ |- _ ] => generalize (split_id1_invert H); clear H
         end.

Hint Extern 1 ((hprop_inj _) _) => hreduce : Ynot.
Hint Extern 1 ((hprop_cell _ _) _) => hreduce : Ynot.
Hint Extern 1 ((hprop_sep _ _) _) => hreduce : Ynot.
Hint Extern 1 (hprop_empty _) => hreduce : Ynot.
Hint Extern 1 (hprop_any _) => hreduce : Ynot.

Tactic Notation "ynot" integer(n) := repeat progress (intuition; subst; hreduce); eauto n with Ynot.

Section Sep.
  Ltac t := intros; red.

  Definition SepReturn T (v : T) : STsep __ (fun v' => [v' = v])%hprop.
    t.
    refine {{{STReturn v}}}; ynot 7.
  Qed.

  Definition SepBind pre1 T1 (post1 : T1 -> hprop)
    pre2 T2 (post2 : T2 -> hprop)
    (st1 : STsep pre1 post1)
    (_ : forall v, post1 v ==> pre2 v)
    (st2 : forall v : T1, STsep (pre2 v) post2)
    : STsep pre1 post2.
    unfold hprop_imp; t.

    refine (STBind _ _ _ _ st1 st2 _ _ _).

    tauto.

    ynot 1.
    generalize (H1 _ _ H2); clear H1.
    ynot 7.

    ynot 1.
    generalize (H1 _ _ H4 H5); clear H1.
    ynot 1.
    generalize (H3 _ _ H8); clear H3.
    ynot 1.
  Qed.

  Definition SepSeq pre1 (post1 : unit -> hprop)
    pre2 T2 (post2 : T2 -> hprop)
    (st1 : STsep pre1 post1)
    (_ : forall v, post1 v ==> pre2)
    (st2 : STsep pre2 post2)
    : STsep pre1 post2.
    intros; refine (SepBind _ st1 _ (fun _ : unit => st2)); trivial.
  Qed.

  Definition SepContra T (post : T -> hprop) : STsep [False] post.
    t.
    refine {{{STContra (fun _ => post)}}}; ynot 1.
  Qed.

  Definition SepFix : forall (dom : Type) (ran : dom -> Type)
    (pre : dom -> hprop) (post : forall v : dom, ran v -> hprop)
    (F : (forall v : dom, STsep (pre v) (post v))
      -> (forall v : dom, STsep (pre v) (post v)))
    (v : dom), STsep (pre v) (post v).
    t.
    exact (STFix _ _ _ F v).
  Qed.
  
  Definition SepNew T (v : T)
    : STsep __ (fun p => p --> v)%hprop.
    t.
    refine {{{STNew v}}}; ynot 8.
  Qed.

  Definition SepFree T p
    : STsep (Exists v :@ T, p --> v)%hprop (fun _ : unit => __)%hprop.
    t.
    refine {{{STFree p}}}; ynot 5.
  Qed.

  Definition SepRead T (p : ptr) (P : T -> hprop)
    : STsep (Exists v :@ T, p --> v * P v)%hprop (fun v => p --> v * P v)%hprop.
    t.
    refine {{{STRead T p}}}; ynot 5.

    rewrite (split2_read _ H0 H H1) in H2.
    generalize (Dyn_inj_Some H2); clear H2; intro; subst.

    ynot 10.
  Qed.

  Definition SepWrite T (p : ptr) (v : T)
    : STsep (Exists v' :@ T, p --> v')%hprop (fun _ : unit => p --> v)%hprop.
    t.
    refine {{{STWrite p v}}}; ynot 5.

    exists (h1 ## p <- Dyn v)%heap; intuition.
    eauto with Ynot.
    red; intuition.
    autorewrite with Ynot.
    unfold read in H4.
    auto.
  Qed.

  Definition SepStrengthen pre T (post : T -> hprop) (pre' : hpre)
    (st : STsep pre post)
    : pre' ==> pre
    -> STsep pre' post.
    unfold hprop_imp; t.
    refine {{{st}}}; ynot 7.
  Qed.

  Definition SepWeaken pre T (post post' : T -> hprop)
    (st : STsep pre post)
    : (forall v, post v ==> post' v)
    -> STsep pre post'.
    unfold hprop_imp; t.
    refine {{{st}}}; ynot 1.

    generalize (H1 _ _ H2); clear H1; ynot 4.
  Qed.

  Definition SepFrame pre T (post : T -> hprop) (st : STsep pre post) (P : hprop)
    : STsep (P * pre) (fun v => P * post v)%hprop.
    t.
    refine {{{st}}}; ynot 7.

    assert (h ~> x0 * (h2 * x)).
    eauto with Ynot.

    generalize (H0 _ _ H6); clear H0; ynot 0.
    exists (x5 * x)%heap; ynot 3.

    exists x.
    exists x5.
    intuition.
    eauto with Ynot.
  Qed.

  Definition SepAssert (P : hprop)
    : STsep P (fun _ : unit => P).
    t.
    refine {{{STReturn tt}}}; intuition; subst; eauto.
  Qed.

  Implicit Arguments SepStrengthen [pre T post].
  Notation "{{ st }}" := (SepWeaken _ (SepStrengthen _ st _) _).
  Definition SepFix2 : forall (dom1 dom2 : Type) (ran : dom1 -> dom2 -> Type)
    (pre : dom1 -> dom2 -> hprop) (post : forall v1 v2, ran v1 v2 -> hprop)
    (F : (forall (v1 : dom1) (v2 : dom2), STsep (pre v1 v2) (post v1 v2))
      -> (forall (v1 : dom1) (v2 : dom2), STsep (pre v1 v2) (post v1 v2)))
    (v1 : dom1) (v2 : dom2) , STsep (pre v1 v2) (post v1 v2).
    intros.
    refine ((SepFix (dom := dom1 * dom2) (fun i => ran (fst i) (snd i))
                    (fun i => pre (fst i) (snd i))
                    (fun i o => post (fst i) (snd i) o)
                    (fun self args =>
                      let self' := fun a b => self (a,b) in
                        {{match args 
                            return STsep (pre (fst args) (snd args))
                                         (post (fst args) (snd args)) with
                            | (a,b) => F self' a b
                          end}})) (v1,v2)); destruct args; red; intuition. 
  Qed.
End Sep.

Implicit Arguments SepFree [T].
Implicit Arguments SepStrengthen [pre T post].

Notation "{{ st }}" := (SepWeaken _ (SepStrengthen _ st _) _).

Notation "p <@ c" := (SepStrengthen p c _) (left associativity, at level 81) : stsep_scope.
Notation "c @> p" := (SepWeaken p c _) (left associativity, at level 81) : stsep_scope.
Infix "<@>" := SepFrame (left associativity, at level 81) : stsep_scope.

Notation "'Return' x" := (SepReturn x) (at level 75) : stsep_scope.
Notation "x <- c1 ; c2" := (SepBind _ (SepStrengthen _ c1 _) _ (fun x => c2))
  (right associativity, at level 84, c1 at next level) : stsep_scope.
Notation "c1 ;; c2" := (SepSeq (SepStrengthen _ c1 _) _ c2)
  (right associativity, at level 84) : stsep_scope.
Notation "!!!" := (SepContra _) : stsep_scope.
Notation "'Fix' f ( x : dom ) : ran 'Pre' pre 'Post' post := e" :=
  (SepFix (dom := dom) ran pre post (fun f x => e))
  (at level 85) : stsep_scope.
Notation "'New' x" := (SepNew x) (at level 75) : stsep_scope.
Notation "'FreeT' x :@ T" := (SepFree (T := T) x) (at level 75) : stsep_scope.
Infix "!!" := SepRead (no associativity, at level 75) : stsep_scope.
Infix "::=" := SepWrite (no associativity, at level 75) : stsep_scope.

Bind Scope stsep_scope with STsep.
Delimit Scope stsep_scope with stsep.


(** Alternate notations for more spec inference *)

Notation "p <@ c" := (SepStrengthen p c _) (left associativity, at level 81) : stsepi_scope.
Notation "c @> p" := (SepWeaken p c _) (left associativity, at level 81) : stsepi_scope.
Infix "<@>" := SepFrame (left associativity, at level 81) : stsepi_scope.

Open Local Scope stsepi_scope.

Notation "'Return' x" := (SepReturn x <@> _) (at level 75) : stsepi_scope.
Notation "x <- c1 ; c2" := (SepBind _ (SepStrengthen _ c1 _) _ (fun x => c2))
  (right associativity, at level 84, c1 at next level) : stsepi_scope.
Notation "c1 ;; c2" := (SepSeq (SepStrengthen _ c1 _) _ c2)
  (right associativity, at level 84) : stsepi_scope.
Notation "!!!" := (SepContra _) : stsepi_scope.
Notation "'Fix' f ( x : dom ) : ran 'Pre' pre 'Post' post := e" :=
  (SepFix (dom := dom) ran pre post (fun f x => e))
  (at level 85) : stsepi_scope.
Notation "'New' x" := (SepNew x <@> _) (at level 75) : stsepi_scope.
Notation "'Free' x" := (SepFree x <@> _) (at level 75) : stsepi_scope.
Notation "! r" := (SepRead r _) (no associativity, at level 75) : stsepi_scope.
Notation "r ::= v" := (SepWrite r v <@> _) (no associativity, at level 75) : stsepi_scope.
Notation "'Assert' P" := (SepAssert P) (at level 75) : stsepi_scope.

Delimit Scope stsepi_scope with stsepi.
