(* This file defines a module interface for finite maps and two implementations,
 * one based on a ref to an association list, and one based on a hash-table.
 * The hash-table functor is parameterized by another finite map implementation
 * so that each bucket in the hash-table is implemented by a "nested" finite map.
 *)
Require Import Ynot.
Set Implicit Arguments.

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

  (* because of the dependency of values on keys, we don't just use normal lists *)
  Inductive alist_t : Set := 
  | Nil_al : alist_t 
  | Cons_al : forall (k:A.key_t), A.value_t k -> alist_t -> alist_t.

  Fixpoint remove(k:A.key_t)(l:alist_t) {struct l} : alist_t := 
    match l with
    | Nil_al => Nil_al
    | Cons_al k' v' l' => if A.key_eq_dec k k' then remove k l'
                          else Cons_al v' (remove k l')
    end.

  Definition coerce(k1 k2:A.key_t)(H:k1 = k2)(v:A.value_t k1) : A.value_t k2.
    intros. rewrite H in v. apply v.
  Defined.

  Fixpoint lookup(k:A.key_t)(l:alist_t) {struct l} : option(A.value_t k) := 
    match l with
    | Nil_al => None
    | Cons_al k' v' l' => 
      match A.key_eq_dec k' k with
      | left k_eq_k' => Some (coerce k_eq_k' v')
      | right k_neq_k' => lookup k l'
      end
    end.
End AssocList.

(*******************************************************************)
(* The finite-map interface, relative to an ASSOCIATION definition *)
(*******************************************************************)
Module Type FINITE_MAP.
  Declare Module A : ASSOCIATION.
  Module AL := AssocList(A).

  (* the abstract type of finite maps *)
  Parameter fmap_t : Set.

  (* the abstract representation predicate -- connects an fmap_t to our model,
   * which is an association list of (key,value) pairs. *)
  Parameter rep : fmap_t -> AL.alist_t -> hprop.

  Open Local Scope hprop_scope.

  (* new returns an fmap_t that represents the empty association list *)
  Parameter new : 
    STsep __ (fun (ans:fmap_t) => rep ans AL.Nil_al).

  (* free takes an fmap_t that represents some association list, and destroys it *)
  Parameter free : 
    forall (x:fmap_t), STsep (Exists l :@ AL.alist_t, rep x l) (fun (_:unit) => __).

  (* insert takes an fmap_t that represents some association list l satisfying the
   * predicate P, a key k, and a value v, and updates the fmap_t so it represents 
   * (k,v)::l.  Note that, like the primitive ref-read construct in STsep, we have
   * to use a predicate to characterize the model instead of universally quantifying
   * over a computationally irrelevant version in order to get something useful -- 
   * see the use in the hash-table below.
   *)
  Parameter insert : 
    forall (x:fmap_t)(k:A.key_t)(v:A.value_t k)(P:AL.alist_t -> hprop), 
      STsep (Exists l :@ AL.alist_t, rep x l * P l) 
        (fun (_:unit) => Exists l :@ AL.alist_t, rep x (AL.Cons_al v (AL.remove k l)) * P l).

  (* lookup takes an fmap_t that represents some list l satisfying the predicate P, 
   * and a key k, and returns the value v associatied with k in l if any, while
   * the map continues to represent l. *)
  Parameter lookup : 
    forall (x:fmap_t)(k:A.key_t)(P : AL.alist_t -> hprop), 
      STsep (Exists l :@ AL.alist_t, rep x l * P l) 
            (fun (ans:option (A.value_t k)) =>
               Exists l :@ AL.alist_t, rep x l * P l * [ans = AL.lookup k l]).
End FINITE_MAP.

(*******************************************************************)
(* A trivial implementation of the FINITE_MAP interface where we   *)
(* use a ref to an association list.                               *)
(*******************************************************************)
Module RefAssocList(Assoc:ASSOCIATION) : FINITE_MAP with Module A := Assoc.
  Module A := Assoc.
  Module AL := AssocList(A).

  Definition fmap_t := ptr.
  
  Open Local Scope stsep_scope.
  Open Local Scope hprop_scope.

  Definition rep(x:fmap_t)(y:AL.alist_t) : hprop := (x --> y).

  Definition new : STsep __ (fun (ans:fmap_t) => rep ans AL.Nil_al) := 
    New AL.Nil_al.

  Definition free(x:fmap_t) : STsep (Exists l :@ AL.alist_t, rep x l) (fun (_:unit) => __) :=
    FreeT x :@ AL.alist_t.

  Definition lookup(x:fmap_t)(k:A.key_t)(P : AL.alist_t -> hprop) : 
    STsep (Exists l :@ AL.alist_t, rep x l * P l) 
          (fun (ans:option (A.value_t k)) => 
             Exists l :@ AL.alist_t, rep x l * P l * [ans = AL.lookup k l]).
    intros.
    refine (z <- x !! P ; 
            Return (AL.lookup k z) <@> ((x --> z) * P z) @> _) ; sep auto.
    Defined.

  Definition insert(x:fmap_t)(k:A.key_t)(v:A.value_t k)(P:AL.alist_t->hprop) : 
    STsep (Exists l :@ AL.alist_t, rep x l * P l)
          (fun (_:unit) => 
            Exists l :@ AL.alist_t, rep x (AL.Cons_al v (AL.remove k l)) * P l).
    intros.
    refine (z <- x !! P ; 
            x ::= (AL.Cons_al v (AL.remove k z)) <@> (P z) @> _) ; sep auto.
    Defined.
End RefAssocList.

(***************************************************************************)
(* The following is an argument to the hash-table functor and provides the *)
(* key comparison, key hash, and initial table size needed to build the    *)
(* hash-table.                                                             *)
(***************************************************************************)
Module Type HASH_ASSOCIATION.
  Variable key_t : Set.
  Variable value_t : key_t -> Set.
  Variable key_eq_dec : forall (k1 k2:key_t), {k1 = k2} + {k1 <> k2}.
  Variable hash : key_t -> nat.
  Variable table_size : nat.
  Variable table_size_gt_zero : table_size > 0.
End HASH_ASSOCIATION.

(*************************************************************************************)
(* The hash-table implementation is a functor, parameterized by a HASH_ASSOCIATION,  *)
(* and a finite map implementation F over the keys and values from HASH_ASSOCIATION. *)
(* We use F to implement the buckets.                                                *)
(*************************************************************************************)
Module HashTable(HA : HASH_ASSOCIATION)
                (F : FINITE_MAP with Module A := HA) : FINITE_MAP with Module A := HA.
  Require Import Coq.Arith.Euclid.
  Require Import Coq.Arith.Peano_dec.
  Module A := HA.
  Module AL := F.AL.

  Require Import Array.

  Definition fmap_t : Set := array. (* of F.fmap_t's *)
                                  
  (* We compose the modulo function from the Peano_dec library with the key hash
   * to get something that's guaranteed to be in range. *)
  Program Definition hash(k:A.key_t) : nat := 
    modulo HA.table_size HA.table_size_gt_zero (HA.hash k).

  Lemma hash_below(k:A.key_t) : hash k < HA.table_size.
  Proof.
    intros. unfold hash. 
    assert (exists x, x = modulo HA.table_size HA.table_size_gt_zero (HA.hash k)). eauto. 
    destruct H. rewrite <- H. destruct x. simpl. clear H. destruct e as [q [_ H]]. omega.
  Qed.

  (* given a list of key value pairs, return only those where the hash of the key equals i *)
  Fixpoint filter_hash (i:nat) (l:AL.alist_t) {struct l} : AL.alist_t := 
    match l with
    | AL.Nil_al => AL.Nil_al
    | AL.Cons_al k v l' => 
      if eq_nat_dec (hash k) i then 
        AL.Cons_al v (filter_hash i l')
      else
        filter_hash i l'
    end.

  Open Local Scope stsep_scope.
  Open Local Scope hprop_scope.

  (* The ith bucket of a hash-table is well-formed with respect to the association list
   * l, if it points to an F.fmap_t that represents l filtered by i. *)
  Definition wf_bucket (f:fmap_t) (l:AL.alist_t) (i:nat) : hprop := 
    (Exists r :@ F.fmap_t, 
      (let p := array_plus f i in p ~~ p --> r) * F.rep r (filter_hash i l)).

  (* A hash-table represents list l if each of the buckets is well-formed with respect
   * to l.  Note that we also have to keep around the fact that the array_length of the
   * array is equal to HA.table_size so that we can free the array. *)
  Definition rep (f:fmap_t) (l:AL.alist_t) : hprop := 
    [array_length f = HA.table_size]* iter_sep (wf_bucket f l) 0 HA.table_size.

  Lemma sub_self(x:nat) : (x - x = 0). intros ; omega. Qed.
  Lemma sub_succ(x:nat) : S x <= HA.table_size -> S (HA.table_size - S x) = HA.table_size - x.
    intros ; omega. Qed.

  (* The following is used to initialize an array with empty F.fmap_t's *)
  Definition init_pre(f:array)(n:nat) := 
    iter_sep (fun i => 
               let p := array_plus f i in p ~~ 
                 (Exists A :@ Set, Exists v :@ A, p --> v)) (HA.table_size - n) n.

  Definition init_table(f:array)(n:nat) : 
    (n <= HA.table_size) -> 
    STsep (init_pre f n)
          (fun (_:unit) => iter_sep (wf_bucket f AL.Nil_al) (HA.table_size - n) n).
  intro.
  refine (fix init(n:nat) : 
              n <= HA.table_size -> 
              STsep (init_pre f n)
                (fun (_:unit) => iter_sep (wf_bucket f AL.Nil_al) (HA.table_size - n) n) := 
          match n as n' return
              n' <= HA.table_size -> 
              STsep (init_pre f n')
                (fun (_:unit) => iter_sep (wf_bucket f AL.Nil_al) (HA.table_size - n') n') with
         | 0 => fun H => {{Return tt}}
         | S i => fun H => 
                  m <- F.new <@> init_pre f (S i) ;
                  upd_array f (HA.table_size - S i) m <@> 
                    (init_pre f i * F.rep m AL.Nil_al) ;; 
                  init i _ <@> wf_bucket f AL.Nil_al (HA.table_size - S i) @> _
         end) ; unfold init_pre, wf_bucket ; sep auto ; rewrite (sub_succ H) ; sep auto.
  Defined.

  (* We allocate an array and then initialize it with empty F.fmap_t's *)
  Definition new : STsep __ (fun (ans:fmap_t) => rep ans AL.Nil_al).
    refine (t <- new_array HA.table_size ; 
            @init_table t HA.table_size _  <@> [array_length t = HA.table_size] ;; 
            {{Return t <@> rep t AL.Nil_al}}) ; unfold init_pre, rep ; sep auto ; 
    rewrite (sub_self HA.table_size) ; sep auto.
  Defined.

  Lemma sp_index_hyp(P:nat->hprop)(Q R:hprop)(start len i:nat) : 
    i < len -> 
    iter_sep P start i * P (start + i) * iter_sep P (1 + start + i) (len - i - 1) * Q ==> R 
    ->
    iter_sep P start len * Q ==> R.
  Proof.
    intros. eapply hprop_mp. eapply himp_split. apply (split_index_sep P start H). 
    sep auto. apply H0.
  Qed.

  Lemma sp_index_conc(P:nat->hprop)(Q R:hprop)(start len i:nat) : 
    i < len -> 
    R ==> iter_sep P start i * P (start + i) * iter_sep P (1 + start + i) (len - i - 1) * Q -> 
    R ==> iter_sep P start len * Q.
  Proof.
    intros. eapply hprop_mp_conc. eapply himp_split. apply (join_index_sep P start H).
    sep auto. apply H0.
  Qed.
    
  Lemma emp_himp_lift : forall (P:Prop), P -> (__ ==> [P]).
  Proof.
    sep auto.
  Qed.

  Ltac mytac2 := (eapply sp_index_hyp || eapply sp_index_conc || auto).

  Ltac mysimplr := 
    repeat (progress
    match goal with
    | [ |- context[if eq_nat_dec ?e1 ?e2 then _ else _] ] => 
      destruct (eq_nat_dec e1 e2) ; try congruence ; subst
    | [ |- context[if F.A.key_eq_dec ?k1 ?k2 then _ else _] ] => 
      destruct (F.A.key_eq_dec k1 k2) ; try congruence ; subst
    | _ => simpl ; auto
    end).

  Lemma look_filter_hash(k:A.key_t)(l:AL.alist_t) : 
    F.AL.lookup k (filter_hash (hash k) l) = AL.lookup k l.
  Proof.
    induction l ; mysimplr ; rewrite IHl ; auto. destruct (F.A.key_eq_dec k0 k) ;
    congruence. 
  Qed.

  (* an attempt to keep the sep tactic from unfolding things -- it's a bit too
   * eager to instantiate existentials in the conclusion of himp's, leading to
   * unrecoverable failure.  *)
  Definition myExists(A:Set)(F:A -> hprop) := 
    Exists x :@ A, F x.

  Ltac fold_ex_conc := 
    match goal with 
    | [ |- forall x, _ ] => intro ; fold_ex_conc
    | [ |- _ ==> (hprop_ex ?f) ] => fold (myExists f)
    | [ |- _ ==> (hprop_ex ?f) * _] => fold (myExists f)
    | [ |- _ ==> _ * (hprop_ex ?f)] => fold (myExists f)
    | [ |- _ ==> _ * (hprop_ex ?f) * _] => fold (myExists f)
    | [ |- _ ==> _ * _ * (hprop_ex ?f)] => fold (myExists f)
    end.

  Ltac mytac := 
    repeat progress ( 
      match goal with 
      | [ |- _ ==> Exists x :@ _, _ ] => 
        apply himp_empty_conc' ; apply himp_ex_conc
      | [ |- _ ==> myExists _ ] => 
        unfold myExists ; apply himp_empty_conc' ; apply himp_ex_conc
      | [ |- _ ==> (myExists _) * _] => unfold myExists ; apply himp_ex_conc
      | [ |- __ ==> [_] ] => apply emp_himp_lift
      end
    ).

  Ltac unhide := 
    match goal with
    | [ |- context[let p := ?e in p ~~ _]] => simpl ; unhide
    | [ |- context[hprop_unpack ?e _] ] => generalize e; intro
    end.

  Definition lookup(x:fmap_t)(k:A.key_t)(P : AL.alist_t -> hprop) :
    STsep (Exists l :@ AL.alist_t, rep x l * P l) 
           (fun (ans:option (A.value_t k)) => 
              Exists l :@ AL.alist_t, rep x l * P l * [ans = AL.lookup k l]).
    intros.
    refine (fm <- sub_array x (hash k)   (* extract the right bucket *)
              (fun fm => 
                [array_length x = HA.table_size] * 
                Exists l :@ AL.alist_t, F.rep fm (filter_hash (hash k) l) * P l * 
                   iter_sep (wf_bucket x l) 0 (hash k) * 
                   iter_sep (wf_bucket x l) (S (hash k)) (HA.table_size - (hash k) - 1)) ;
           F.lookup fm k                 (* and use F.lookup to find the value *)
              (fun l' => 
                [array_length x = HA.table_size] *
                Exists l :@ AL.alist_t, 
                   [l' = filter_hash (hash k) l] * P l *
                   (let p := array_plus x (hash k) in p ~~ p --> fm) *
                   iter_sep (wf_bucket x l) 0 (hash k) * 
                   iter_sep (wf_bucket x l) (S (hash k)) (HA.table_size - (hash k) - 1)) @> _);
    unfold rep. sep mytac2. apply (hash_below k). unfold wf_bucket at 2. unhide.
    sep auto. fold_ex_conc. sep auto. sep mytac. exists v1. sep mytac2. 
    apply (hash_below k). unfold wf_bucket. sep auto. rewrite look_filter_hash;
    mytac ; auto. unhide. fold_ex_conc. sep auto. mytac. exists (filter_hash (hash k) v0). 
    sep mytac.
  Defined.

  Lemma remove_filter_eq (k:A.key_t)(l:AL.alist_t) : 
    F.AL.remove k (filter_hash (hash k) l) = filter_hash (hash k) (AL.remove k l).
  Proof. induction l ; simpl ; mysimplr. rewrite IHl. auto. Qed.

  Lemma remove_filter_neq (k:A.key_t)(i:nat)(l:AL.alist_t) : 
    (hash k <> i) -> filter_hash i l = filter_hash i (AL.remove k l).
  Proof. induction l ; simpl ; intros ; mysimplr. rewrite IHl ; auto. Qed.
    
  Definition insert(x:fmap_t)(k:A.key_t)(v:A.value_t k)(P:AL.alist_t -> hprop) : 
    STsep (Exists l :@ AL.alist_t, rep x l * P l) 
          (fun (_:unit) => 
            Exists l :@ AL.alist_t, rep x (AL.Cons_al v (AL.remove k l)) * P l).
  intros.
  refine (fm <- sub_array x (hash k) (* find the right bucket *)
           (fun fm =>
             [array_length x = HA.table_size] * 
             myExists (fun l : AL.alist_t => 
                  (P l * F.rep fm (filter_hash (hash k) l) * 
                   iter_sep (wf_bucket x l) 0 (hash k) * 
                   iter_sep (wf_bucket x l) (S (hash k)) (HA.table_size - (hash k) - 1)))) ; 
         F.insert fm v     (* and use F.insert to insert the key value pair *)
           (fun l' => 
             [array_length x = HA.table_size] * 
             myExists (fun l : AL.alist_t => 
                     [l' = filter_hash (hash k) l] * 
                     P l * (let p := array_plus x (hash k) in p ~~ p --> fm) *
                     iter_sep (wf_bucket x l) 0 (hash k) * 
                     iter_sep (wf_bucket x l) (S (hash k)) (HA.table_size - (hash k) - 1)))
        @> _) ; 
  unfold rep. sep mytac2. apply (hash_below k). unfold wf_bucket at 2. unhide.
  sep auto. unfold myExists. sep mytac. exists v0. sep auto. intros. fold_ex_conc. 
  unfold myExists at 1. sep auto. sep mytac. exists v2. sep mytac2. apply (hash_below k). 
  unfold wf_bucket at 4. unhide ; sep auto ; mysimplr. rewrite remove_filter_eq.  
  sep auto. apply himp_comm_prem. apply himp_split ; apply iter_imp ; unfold wf_bucket ; 
  sep auto ; assert (hash k <> i); try omega ; mysimplr; rewrite (remove_filter_neq _ v2 n) ; 
  sep auto. unhide. unfold myExists at 1. fold_ex_conc. sep auto. sep mytac.
  exists (filter_hash (hash k) v1). sep mytac. 
  Defined.

  (* the following runs through the array and calls F.free on each of the buckets. *)
  Definition free_table(f:array)(n:nat) : 
    (n <= HA.table_size) -> 
    STsep (myExists (fun l => iter_sep (wf_bucket f l) (HA.table_size - n) n))
          (fun (_:unit) => 
            iter_sep (fun i => let p := array_plus f i in p ~~ ptsto_any p) 
                     (HA.table_size - n) n).
  intro f.
  refine (fix free_tab(n:nat) : 
             (n <= HA.table_size) -> 
               STsep (myExists (fun l => iter_sep (wf_bucket f l) (HA.table_size - n) n)) 
                     (fun (_:unit) => 
                        iter_sep (fun i => let p := array_plus f i in p ~~ ptsto_any p) 
                                 (HA.table_size - n) n) := 
          match n as n' return
             (n' <= HA.table_size) -> 
              STsep (myExists (fun l => iter_sep (wf_bucket f l) (HA.table_size - n') n'))
                     (fun (_:unit) => 
                        iter_sep (fun i => let p := array_plus f i in p ~~ ptsto_any p) 
                                 (HA.table_size - n') n') 
          with
          | 0 => fun H => {{Return tt}}
          | S i => fun H => 
              fm <- sub_array f (HA.table_size - (S i)) 
                       (fun fm => myExists (fun l => 
                        F.rep fm (filter_hash (HA.table_size - (S i)) l) * 
                        iter_sep (wf_bucket f l) (HA.table_size - i) i)) ;
              F.free fm <@> 
                 ((let p := array_plus f (HA.table_size - (S i)) in p ~~ p --> fm) *
                  myExists (fun l => iter_sep (wf_bucket f l) (HA.table_size - i) i)) ;; 
              free_tab i _ <@> 
                (let p := array_plus f (HA.table_size - (S i)) in p ~~ ptsto_any p ) @> _
          end) ; simpl ; intros. unfold myExists ; sep auto. unfold myExists ; sep auto.
  unfold myExists at 1. unfold wf_bucket at 1. unhide ; sep auto. unfold myExists ; sep auto. 
  rewrite (sub_succ H) ; sep auto. unfold myExists ; sep auto. auto with arith. unhide.
  sep auto. rewrite (sub_succ H) ; sep auto. unhide ; sep auto. unfold ptsto_any ; sep auto.
  unhide. unfold myExists. repeat fold_ex_conc. sep auto. unfold myExists. sep auto.
  Defined.

  (* Run through the array, call F.free on all of the maps, and then call array_free *)
  Definition free(f:fmap_t) : 
    STsep (Exists l :@ AL.alist_t, rep f l) (fun (_:unit) => __).
  intros.
  refine (@free_table f HA.table_size _ <@> [array_length f = HA.table_size] ;; 
          free_array f) ; simpl ; auto ; unfold rep, myExists ; 
  rewrite (sub_self HA.table_size) ; sep auto. rewrite H ; sep auto.
  Defined.

End HashTable.
