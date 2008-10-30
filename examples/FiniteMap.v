(* This file defines a module interface for finite maps and two implementations,
 * one based on a ref to an association list, and one based on a hash-table.
 * The hash-table functor is parameterized by another finite map implementation
 * so that each bucket in the hash-table is implemented by a "nested" finite map.
 *)

Require Import Ynot.
Set Implicit Arguments.
(* Require Import Relations. *)

(*************************************************)
(* Module parameter for the finite map interface *)
(*************************************************)
Module Type ASSOCIATION.
  Variable key_t : Set.
  Variable value_t : key_t -> Set.  (* note that value types depend on the keys *)
  Variable key_eq_dec : forall (k1 k2:key_t), {k1 = k2} + {k1 <> k2}.
End ASSOCIATION.

(*********************************************)
(* The functional model -- association lists *)
(*********************************************)
Module AssocList(A : ASSOCIATION).
Require Export List.

  Notation "( x ,, y )" := (@existT _ _ x y) : core_scope.
  Notation "` x" := (projT1 x) (at level 10): core_scope.

  (* because of the dependency of values on keys, we don't just use normal lists *)
  Definition alist_t := list (sigT A.value_t).

  Definition nil_al := @nil (sigT A.value_t).
  Fixpoint remove(k:A.key_t)(l:alist_t) {struct l} : alist_t := 
    match l with
    | nil => nil
    | (k',, v')::l' => if A.key_eq_dec k k' then remove k l'
                          else (k',, v')::(remove k l')
    end.

  Definition insert(k:A.key_t)(v:A.value_t k)(l:alist_t) := (k,, v)::(remove k l).

  Definition coerce(k1 k2:A.key_t)(H:k1 = k2)(v:A.value_t k1) : A.value_t k2.
    intros. rewrite H in v. apply v.
  Defined.

  Fixpoint lookup(k:A.key_t)(l:alist_t) {struct l} : option(A.value_t k) := 
    match l with
    | nil => None
    | (k',, v'):: l' => 
      match A.key_eq_dec k' k with
      | left k_eq_k' => Some (coerce k_eq_k' v')
      | right k_neq_k' => lookup k l'
      end
    end.

    Fixpoint distinct (l:alist_t) : Prop :=
      match l with
        | nil => True
        | (k,,v)::ls => lookup k ls = None /\ distinct ls
      end.
    
    Ltac simpler :=
      repeat (progress ((repeat 
        match goal with
        | [|- context [match A.key_eq_dec ?k1 ?k2 with 
                         | left _ => _ 
                         | right _ => _ end]] =>
        case_eq (A.key_eq_dec k1 k2) ; intros; try congruence ; try solve [assert False; intuition]; try subst 
        | [H:context [match A.key_eq_dec ?k1 ?k2 with 
                         | left _ => _ 
                         | right _ => _ end] |- _] =>
        destruct (A.key_eq_dec k1 k2) ; try congruence ; try solve [assert False; intuition]; try subst
        |[H: sigT _ |- _] => destruct H
      end); simpl in *; auto)).

  Lemma lookup_remove_eq k l : lookup k (remove k l) = None.
  Proof. induction l; simpler. Qed.

  Lemma lookup_remove_neq k k' l : k <> k' -> lookup k (remove k' l) = lookup k l.
  Proof. induction l; simpler. Qed.

  Lemma lookup_none_remove k l : lookup k l = None -> remove k l = l.
  Proof. induction l; simpler. f_equal; auto. Qed.

  Lemma lookup_none_perm k l l' : Permutation l l' -> lookup k l = None -> lookup k l' = None.
  Proof. induction 1; simpler. Qed.

  Lemma distinct_remove k l : distinct l -> distinct (remove k l).
  Proof. induction l; simpler; intuition. rewrite lookup_remove_neq; auto. Qed.

  Lemma distinct_insert k (v:A.value_t k) l : distinct l -> distinct (insert v l).
  Proof. induction l; simpler; intuition. rewrite lookup_remove_neq; auto. Qed.

  Lemma distinct_perm l l' : Permutation l l' -> distinct l -> distinct l'.
  Proof. Hint Resolve lookup_none_perm. induction 1; simpler; intuition (congruence||eauto). Qed.

  Hint Resolve lookup_remove_eq distinct_remove distinct_perm Permutation_sym Permutation_refl.

  Lemma lookup_dis_perm k l l' : Permutation l l' -> distinct l -> lookup k l = lookup k l'.
  Proof. induction 1; simpler; intuition try congruence. clear H1 H2; congruence. rewrite H2. eauto. Qed.

  Lemma remove_perm k l l' : Permutation l l' -> Permutation (remove k l) (remove k l').
  Proof.  Hint Constructors Permutation. induction 1; simpler; eauto. Qed.
  Hint Resolve remove_perm.

  Lemma insert_perm k l l' (v:A.value_t k) : Permutation l l' -> Permutation (insert v l) (insert v l').
  Proof. unfold insert; simpler. Qed.
  Hint Resolve insert_perm.

  Lemma remove_swap k k' l : remove k (remove k' l) = remove k' (remove k l).
  Proof. induction l; simpler. Qed.
  Hint Resolve remove_swap.

  Lemma insert_swap k (v:A.value_t k) k' (v':A.value_t k') l : k <> k' -> 
    Permutation (insert v (insert v' l)) (insert v' (insert v l)).
  Proof. intros. Hint Constructors Permutation. unfold insert; simpler. rewrite remove_swap. auto. Qed.
  Hint Resolve insert_swap.

End AssocList.

Module Type FINITE_MAP_AT.
  Declare Module A:ASSOCIATION.
  Module AL := AssocList(A).

  (* the abstract type of finite maps *)
  Variable fmap_t : Set.

  (* the abstract representation predicate -- connects an fmap_t to our model,
   * which is an association list of (key,value) pairs. *)
  Variable rep : fmap_t -> AL.alist_t -> hprop.
End FINITE_MAP_AT.

(*******************************************************************)
(* The finite-map interface, relative to an ASSOCIATION definition *)
(*******************************************************************)
Module FINITE_MAP_T(Assoc:ASSOCIATION)(AT:FINITE_MAP_AT with Module A:=Assoc).
  Module A := AT.A.
  Module AL := AT.AL.

  Import AT AL.

  Open Local Scope hprop_scope.

  (* new returns an fmap_t that represents the empty association list *)
  Definition new := 
    STsep __ (fun (ans:fmap_t) => rep ans nil_al).

  (* free takes an fmap_t that represents some association list, and destroys it *)
  Definition free := 
    forall (x:fmap_t)(l:[alist_t]), STsep (l ~~ rep x l) (fun (_:unit) => __).

  (* insert takes an fmap_t that represents some association list l satisfying the
   * predicate P, a key k, and a value v, and updates the fmap_t so it represents 
   * (k,v)::l.  Note that, like the primitive ref-read construct in STsep, we have
   * to use a predicate to characterize the model instead of universally quantifying
   * over a computationally irrelevant version in order to get something useful -- 
   * see the use in the hash-table below.
   *)
  Definition insert :=
    forall (x:fmap_t)(k:A.key_t)(v:A.value_t k)(l:[alist_t]),
      STsep (l ~~ rep x l)
        (fun (_:unit) => l ~~ rep x (insert v l)).

  (* lookup takes an fmap_t that represents some list l satisfying the predicate P, 
   * and a key k, and returns the value v associatied with k in l if any, while
   * the map continues to represent l. *)
  Definition lookup :=
    forall (x:fmap_t)(k:A.key_t)(l:[alist_t]), 
      STsep (l ~~ rep x l) 
            (fun (ans:option (A.value_t k)) =>
               l ~~ [ans = lookup k l] * rep x l).

  Definition remove :=
    forall (x:fmap_t)(k:A.key_t)(l:[alist_t]),
      STsep (l ~~ rep x l)
        (fun (_:unit) => l ~~ rep x (remove k l)).

(*
  Fixpoint fold_pre (B:Type) (P0:B->hprop)
    (P:forall k, A.value_t k->B->hprop)
    (Q:forall k, A.value_t k->B->B->hprop) (b:B)
    (l:alist_t) {struct l}:=
  match l with 
    | nil => P0 b
    | (k,,v)::ls => P k v b * [forall b', Q k v b b' ==> fold_pre P0 P Q b' ls]
  end.

  Fixpoint fold_post (B:Type) (Q0:B->hprop)
    (Q:forall k, A.value_t k->B->B->hprop) (b:B) (ans:B)
    (l:alist_t) {struct l}:=
  match l with 
    | nil => Q0 b * [b=ans]
    | (k,,v)::ls => Exists b' :@ B, Q k v b b' & fold_post Q0 Q b' ans ls
  end.

  Definition hprop_forall T (p : T -> hprop) : hprop := fun h => forall v, p v h.
  Notation "'Forall' v :@ T , p" := (hprop_forall (fun v : T => p)) (at level 90, T at next level) : hprop_scope.

  Definition fold := forall (x:fmap_t)(B:Type) (P0:B->hprop) (P:forall k, A.value_t k->B->hprop) (Q0:B->hprop)
                                               (Q:forall k, A.value_t k->B->B->hprop) (b:B)
                                               (c:forall k v b, STsep (P k v b) (Q k v b)) (l:[alist_t]),
    STsep (l ~~ rep x l * Forall l' :@ {l':alist_t | Permutation l l'}, fold_pre P0 P Q b (proj1_sig l'))
    (fun (b':B) => (l ~~ rep x l * Exists l' :@ {l':alist_t | Permutation l l'}, fold_post Q0 Q b b' (proj1_sig l'))).
*)
  Definition distinct := forall (x:fmap_t) (l:alist_t), rep x l ==> [distinct l] * ??.

  Definition perm := forall (x:fmap_t) (l l':alist_t), Permutation l l' -> rep x l ==> rep x l'.

  Ltac unfm_t := unfold new, free, insert, lookup, remove, distinct, perm.

End FINITE_MAP_T.

(*******************************************************************)
(* The finite-map interface, relative to an ASSOCIATION definition *)
(*******************************************************************)
Module Type FINITE_MAP.
(* do we need A? *)
  Declare Module A  : ASSOCIATION.
  Module AL := AssocList(A).
  Declare Module AT : FINITE_MAP_AT with Module A:=A with Module AL := AL.
  Module T := FINITE_MAP_T(A)(AT).

  Export AT.

  Parameter new : T.new.
  Parameter free : T.free.
  Parameter insert : T.insert.
  Parameter remove : T.remove.
  Parameter lookup : T.lookup.
(*  Parameter fold : T.fold. *)
  Axiom distinct : T.distinct.
  Axiom perm : T.perm.

End FINITE_MAP.

(*
Module copier(FM:FINITE_MAP).
Module AL := FM.AT.AL.
Import AL.
Import FM.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Fixpoint Tadd (sourceM destM:alist_t) {struct sourceM} :=
  match sourceM with
    | nil => destM
    | (k,,v)::sourceM => AL.insert v (Tadd sourceM destM)
  end.

Lemma Tadd_perm1 l1 l1' l2 : Permutation l1 l1' -> AL.distinct l1 -> Permutation (Tadd l1 l2) (Tadd l1' l2).
Proof. induction 1; simpler; intuition; try congruence. eapply perm_trans; eauto. Qed.

Ltac simpl_inh := repeat 
  match goal with
    | [H:[_]%inhabited = [_]%inhabited |- _] => generalize (pack_injective H); clear H; intro H 
    | [H1:?x = [?y1]%inhabited, H2:?x = [?y2]%inhabited |- _]
      => match y1 with
           | y2 => fail 1
           | _ => rewrite H1 in H2
         end
  end.

Lemma hprop_forall_conc T (P:T->hprop) Q : (forall x:T, Q ==> P x) -> Q ==> (T.hprop_forall P).
Proof. firstorder. Qed.

Ltac perm_simpl := 
  match goal with
  | [H:Permutation nil ?x |- _ ] => generalize (Permutation_nil H); clear H; intro H; subst x
  | [H:Permutation ?x nil |- _ ] => generalize (Permutation_nil (Permutation_sym H)); clear H; intro H; subst x
  | [H:Permutation (?a::?x1) ?x2 |- _ ] => 
    match x2 with
      | (_::_) => fail 1
      | (_++_) => fail 1
      | _ => destruct x2; [elim (Permutation_nil_cons (Permutation_sym H)) |]
    end
  | [H:Permutation ?x2 (?a::?x1) |- _ ] => 
    match x2 with
      | (_::_) => fail 1
      | (_++_) => fail 1
      | _ => destruct x2; [elim (Permutation_nil_cons H) |]
    end
end.

Ltac simpler2 :=
  repeat (progress ((repeat 
    match goal with
      | [H:[_]%inhabited = [_]%inhabited |- _] => generalize (pack_injective H); clear H; intro H 
      | [H1:?x = [?y1]%inhabited, H2:?x = [?y2]%inhabited |- _]
        => match y1 with
             | y2 => fail 1
             | _ => rewrite H1 in H2
           end
      | [|- context [match A.key_eq_dec ?k1 ?k2 with 
                           | left _ => _ 
                       | right _ => _ end]] =>
      case_eq (A.key_eq_dec k1 k2) ; intros; try congruence ; try solve [assert False; intuition]; try subst
        |[H: sigT _ |- _] => destruct H
    end); simpl; auto)).

Definition add (source ddest:fmap_t) (sourceM destM:[alist_t]) :
  STsep (sourceM ~~ destM ~~ rep source sourceM * rep ddest destM)
  (fun (_:unit) => sourceM ~~ destM ~~ rep source sourceM * rep ddest (Tadd sourceM destM)).
intros.
refine (zz <- (fold source _ _ _ _ destM (fun k v b => {{(insert ddest (k:=k) v b)}}
                                         ;; {{Return (b ~~~ AL.insert v b)}}) sourceM)
; {{Return tt}}); sep simpl_inh.
assert (((fun (_:A.key_t) _ (x:[alist_t]) => (x ~~ rep ddest x)) k v [x]%inhabited) ==> rep ddest x); [idtac|eassumption].
sep simpl_inh.
assert (rep ddest (AL.insert v x0) ==> 
   (fun _ _ l1 l2 => l2 ~~ rep ddest l2) k v [x0]%inhabited [AL.insert v x0]%inhabited); [idtac|eassumption].
sep simpl_inh.
apply hprop_forall_conc. destruct x1. simpl.
revert x x0 p.
induction x1; sep simpl_inh. 
assert(rep ddest x ==> (fun x => x ~~ rep ddest x) [x]%inhabited); [sep simpl_inh|eassumption].
destruct a.
sep simpl_inh. repeat intro. destruct H. red. intuition. 
sep auto.
eapply IHx1. apply Permutation_refl.
instantiate (1 := v). sep auto.
instantiate (1 := v). sep auto.
destruct v0. simpl.
clear H2.
revert x0 x2 p.
induction x1; sep simpl_inh.

perm_simpl. simpl. sep auto.
assert((fun x => x ~~ rep ddest x) [x0]%inhabited ==> rep ddest x0); [sep simpl_inh|eassumption].
perm_simpl. simpler. sep auto. sep auto. 
pose (IHx1 x5 x2).

*)