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
  Definition pair_dec (kv1 kv2:sigT A.value_t) := A.key_eq_dec (projT1 kv1) (projT1 kv2).

  Definition nil_al := @nil (sigT A.value_t).
  Fixpoint remove(k:A.key_t)(l:alist_t) {struct l} : alist_t := 
    match l with
    | nil => nil
    | (k',, v')::l' => if A.key_eq_dec k k' then remove k l'
                          else (k',, v')::(remove k l')
    end.

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
        (fun (_:unit) => l ~~ rep x ((k,, v)::(remove k l))).

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
  Definition hprop_forall T (p : T -> hprop) : hprop := fun h => forall v, p v h.
  Notation "'Forall' v :@ T , p" := (hprop_forall (fun v : T => p)) (at level 90, T at next level) : hprop_scope.

  Definition hprop_himp (P Q : hprop) : hprop := fun h => P h -> Q h.
  Notation "P ===> Q" := (hprop_himp P Q) (at level 85, T at next level) : hprop_scope.
*)

(*
  (c:forall k v b l, insert destFM k v l),

  (* fold *)
  Fixpoint fold_pre (B C:Type) 
    (P:alist_l->B->C->hprop)
    (Q:alist_l->B->C->B->C->hprop) (b:B) (c:C)
    (l:alist_t) {struct l}:=
    P 
  match l with 
    | nil => P 
    | (k,,v)::ls => P k v b c * [forall b' c', Q k v b c b' c' ==> fold_pre P Q b' c' ls]
  end.


  Fixpoint fold_pre (B C:Type) 
    (P:forall k, A.value_t k->B->C->hprop)
    (Q:forall k, A.value_t k->B->C->B->C->hprop) (b:B) (c:C)
    (l:alist_t) {struct l}:=
  match l with 
    | nil => ??
    | (k,,v)::ls => P k v b c * [forall b' c', Q k v b c b' c' ==> fold_pre P Q b' c' ls]
  end.

  Fixpoint fold_pre (B C:Type) 
    (P:forall k, A.value_t k->B->C->hprop)
    (Q:forall k, A.value_t k->B->C->B->C->hprop) (b:B) (c:C)
    (l:alist_t) {struct l}:=
  match l with 
    | nil => ??
    | (k,,v)::ls => P k v b c * [forall b' c', Q k v b c b' c' ==> fold_pre P Q b' c' ls]
  end.

  (* how to write this in seperation logic? *)
  (* this actually uses the reverse list as fold_pre, but since we are
     working upto permutation (see fold), this is ok *)

  Fixpoint fold_post (B C:Type)
    (Q:forall k, A.value_t k->B->C->B->C->hprop) (b:B) (c:C) (bans:B) (cans:C) 
    (l:alist_t) {struct l}:=
  match l with 
    | nil => ?? * [b=bans] * [c=cans]
    | (k,,v)::ls => Exists b' :@ B, Q k v ls b b' 
  end.


  Definition fold := forall (x:fmap_t)(B:Type) (P:forall k, A.value_t k->B->hprop)
                                               (Q:forall k, A.value_t k->B->B->hprop) (b:B) 
                                               (c:forall k v b, STsep (P k v b) (Q k v b)) (l:[alist_t]),
    STsep (l ~~ rep x l * Forall l' :@ {l':alist_t | Permutation l l'}, fold_pre B P Q (` l') b)
    (fun (b':B) => (l ~~ rep x l * Exists l' :@ {l':alist_t | Permutation l l'}, fold_post B P Q (` l') b b')).


  Fixpoint fold_post (B:Type) 
    (Q:forall k, A.value_t k->B->B->hprop) (b:B) 
    (l:alist_t) {struct l}:=
  match l with 
    | nil => ??
    | (k,,v)::ls => P k v b & (Forall b' :@ B, Q k v b b' ===> fold_pre P Q b' ls)
  end.
  
*)

  Ltac unfm_t := unfold new, free, insert, lookup, remove.

End FINITE_MAP_T.

(*******************************************************************)
(* The finite-map interface, relative to an ASSOCIATION definition *)
(*******************************************************************)
Module Type FINITE_MAP.
(* do we need A? *)
  Declare Module A  : ASSOCIATION.
  Declare Module AT : FINITE_MAP_AT with Module A:=A.
  Module T := FINITE_MAP_T(A)(AT).

  Export AT.

  Parameter new : T.new.
  Parameter free : T.free.
  Parameter insert : T.insert.
  Parameter remove : T.remove.
  Parameter lookup : T.lookup.

End FINITE_MAP.
