(* This file defines a module interface for finite maps and two implementations,
 * one based on a ref to an association list, and one based on a hash-table.
 * The hash-table functor is parameterized by another finite map implementation
 * so that each bucket in the hash-table is implemented by a "nested" finite map.
 *)

Require Import Ynot.
Require Import Relations.
Set Implicit Arguments.

Notation "( x ,, y )" := (@existT _ _ x y) : core_scope.
Notation "` x" := (projT1 x) (at level 10): core_scope.


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
Require Import List.
Module AssocList(A : ASSOCIATION).

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

(*******************************************************************)
(* A trivial implementation of the FINITE_MAP interface where we   *)
(* use a ref to an association list.                               *)
(*******************************************************************)
Module RefAssocList(Assoc:ASSOCIATION) : FINITE_MAP with Module A := Assoc.

  Module AT <: FINITE_MAP_AT with Module A:=Assoc.
    Module A := Assoc.
    Module AL := AssocList(Assoc).
    Open Local Scope hprop_scope.
    Definition fmap_t := ptr.
    Definition rep(x:fmap_t)(y:AL.alist_t) := (x --> y).
  End AT.

  Module T:=FINITE_MAP_T(Assoc)(AT).
  Module A := T.A.
  Module AL := T.AL.

  Import AT.
  
  Open Local Scope stsepi_scope.
  Open Local Scope hprop_scope.

  Ltac s := T.unfm_t; intros.
  Ltac t := unfold AT.rep; sep auto.

  Definition new : T.new. s;
    refine ({{New AL.nil_al}})
  ; t. Defined.

  Definition free : T.free. s;
    refine ({{Free x}})
  ; t. Defined.

  Definition lookup : T.lookup. s;
    refine (z <- ! x ; 
            {{Return (AL.lookup k z)}})
  ; t. Defined.

  Definition insert : T.insert. s;
    refine (z <- ! x ;
            {{x ::= ((k,, v):: (AL.remove k z))}})
  ; t. Defined.

  Definition remove : T.remove. s;
    refine (z <- ! x ;
            {{x ::= (AL.remove k z)}})
  ; t. Defined.

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

  Require Import Euclid Peano_dec Minus Array.

  Module AT <: FINITE_MAP_AT with Module A:=HA.
    Module A := HA.
    Module AL := AssocList(A).
    Open Local Scope hprop_scope.

    Definition fmap_t : Set := array. (* of F.fmap_t's *)
                                  
    (* We compose the modulo function from the Peano_dec library with the key hash
     * to get something that's guaranteed to be in range. *)
    Program Definition hash(k:A.key_t) : nat := modulo HA.table_size HA.table_size_gt_zero (HA.hash k).

    Ltac simpl_sig := 
      match goal with 
        | [|- context [proj1_sig ?x]] => destruct x; simpl
        | [H:context [proj1_sig ?x] |- _] => destruct x; simpl in H
      end. 
  
    Lemma hash_below(k:A.key_t) : hash k < HA.table_size.
    Proof. unfold hash; intros; simpl_sig; destruct e; omega. Qed.

    (* given a list of key value pairs, return only those where the hash of the key equals i *)
    Fixpoint filter_hash (i:nat) (l:AL.alist_t) {struct l} : AL.alist_t := 
      match l with
      | nil => nil
      | (k,, v)::l' => 
        if eq_nat_dec (hash k) i then 
          (k,,v):: (filter_hash i l')
        else
          filter_hash i l'
      end.

    (* The ith bucket of a hash-table is well-formed with respect to the association list
     * l, if it points to an F.fmap_t that represents l filtered by i. *)

    (* Some notation for unpacking pointer arithmetic *)
    (* why isn't this being pulled in from Array? *)
    Notation "p ':~~' e1 'in' e2" := (let p := e1 in p ~~ e2) (at level 91, right associativity) : hprop_scope.

    Definition wf_bucket (f:fmap_t) (l:AL.alist_t) (i:nat) : hprop := 
      (Exists r :@ F.AT.fmap_t, 
        (p :~~ array_plus f i in p --> r) * F.AT.rep r (filter_hash i l)).

    (* notation for iter_sep, modeled after list/array comprehensions *)
    Notation "{@ P | i <- s + l }" := (iter_sep (fun i => P) s l) (i ident, s at next level).

    (* A hash-table represents list l if each of the buckets is well-formed with respect
     * to l.  Note that we also have to keep around the fact that the array_length of the
     * array is equal to HA.table_size so that we can free the array. *)
    Definition rep (f:fmap_t) (l:AL.alist_t) : hprop := 
      [array_length f = HA.table_size] * {@ (wf_bucket f l i) | i <- 0 + HA.table_size}.

    Lemma sub_succ(x:nat) : 
      S x <= HA.table_size -> S (HA.table_size - S x) = HA.table_size - x.
    Proof. intros ; omega. Qed.

    Ltac sub_simpl :=
      (repeat 
        match goal with
          | [|- context [?x - ?x]] => rewrite <- minus_n_n
          | [|- context [S (HA.table_size - S ?x)]] => rewrite sub_succ; [idtac | solve[auto]]
          | [H:array_length ?x = _ |- context [array_length ?x]] => rewrite H
        end); simpl; auto.
    End AT.

  Module T:=FINITE_MAP_T(HA)(AT).

  Import AT.
  
  Open Local Scope stsepi_scope.
  Open Local Scope hprop_scope.

  Module A := HA.
  Module AL := F.AT.AL.
  Ltac s := T.unfm_t; intros.

  (* The following is used to initialize an array with empty F.fmap_t's *)
  Definition init_pre(f:array)(n:nat) := 
    {@ p :~~ array_plus f i in (Exists A :@ Set, Exists v :@ A, p --> v) | i <- (HA.table_size - n) + n }.

  Definition init_post (f:array)(n:nat)(_:unit) := {@ AT.wf_bucket f AL.nil_al i | i <- (HA.table_size - n) + n}.
  Definition init_table_spec (f:array)(n:nat) := (n <= HA.table_size) -> STsep (init_pre f n) (init_post f n).

  Definition init_table(f:array)(n:nat) : init_table_spec f n.
  intro.
  refine(
    fix init(n:nat) : init_table_spec f n :=
          match n as n' return init_table_spec f n' with
         | 0 => fun _ => {{Return tt}}
         | S i => fun _ => (* ANNOTE *)
                    m <- F.new 
                      <@> init_pre f (S i)
                  ; upd_array f (HA.table_size - S i) m
                      <@> (init_pre f i * F.AT.rep m AL.nil_al)
                 ;; {{init i _ <@> AT.wf_bucket f AL.nil_al (HA.table_size - S i)}}
         end) ; unfold init_pre, init_post, wf_bucket ; sep sub_simpl.
  Defined.

  (* We allocate an array and then initialize it with empty F.fmap_t's *)
  Definition new : T.new. s.
    Ltac r:= unfold init_pre, init_post, rep; sep sub_simpl.
    refine (  t <- new_array HA.table_size 
            ; @init_table t HA.table_size _
              <@> [array_length t = HA.table_size] 
           ;; {{Return t}}); unfold  init_pre, init_post, rep; r.
  Defined.

  Definition free_pre (f:array)(l:[AL.alist_t])(n:nat) := l ~~ {@ wf_bucket f l i | i <- (HA.table_size - n) + n}.
  Definition free_post (f:array)(n:nat) (_:unit) := {@ p :~~ array_plus f i in ptsto_any p | i <- (HA.table_size - n) + n}.
  Definition free_spec (f:array)(l:[AL.alist_t])(n:nat) := (n <= HA.table_size) -> STsep (free_pre f l n) (free_post f n).

  (* this definition and notation is useful enough that it probably ought to 
   * go in Separation.v or somewhere else... *)

  Definition inhabit_unpack T U (inh : [T]) (f:T -> U) : [U] := 
    match inh with
    | inhabits v => inhabits (f v)
    end.
  Notation "inh ~~~ f" := (inhabit_unpack inh (fun inh => f)) 
    (at level 91, right associativity) : hprop_scope.

  (* the following runs through the array and calls F.free on each of the buckets. *)
  Definition free_table(f:array)(l:[AL.alist_t])(n:nat) : free_spec f l n.
  intros f l.
  refine (fix free_tab(n:nat) : free_spec f l n := 
          match n as n' return free_spec f l n' 
          with
          | 0 => fun H => {{Return tt}}
          | S i => fun H => let j := HA.table_size - (S i) in
                              let p := array_plus f j in 
              fm <- sub_array f j 
                       (fun fm => l ~~ F.AT.rep fm (filter_hash j l) * 
                        iter_sep (wf_bucket f l) (HA.table_size - i) i) 
            ; F.free fm (l ~~~ filter_hash j l)
                <@> ((p ~~ p --> fm) * free_pre f l i)
           ;; {{free_tab i _ <@> (p ~~ ptsto_any p )}}
          end); unfold free_pre, free_post, wf_bucket, ptsto_any; clear free_tab;
 try solve[
(* the first goal *)
simpl; apply himp_comm_conc; apply himp_empty_conc; apply himp_refl];
(* the other ones *)
sep sub_simpl; try subst j; try (rewrite H0; sep sub_simpl).
Defined.

  (* Run through the array, call F.free on all of the maps, and then call array_free *)
  Definition free : T.free. s.
  refine (@free_table x l HA.table_size _ 
              <@> [array_length x = HA.table_size] 
      ;; free_array x)
    ; unfold free_pre, free_post, rep; sep sub_simpl.
  Defined.

  (* an attempt to keep the sep tactic from unfolding things -- it's a bit too
   * eager to instantiate existentials in the conclusion of himp's, leading to
   * unrecoverable failure.  *)
  Definition myExists(A:Set)(F:A -> hprop) := 
    Exists x :@ A, F x.

  Ltac fold_ex_conc := 
    search_conc ltac:(try match goal with
                          | [ |- _ ==> (hprop_ex ?f) * _ ] => fold (myExists f)
                          end).
  Definition myeq := eq.
  Ltac unhide := 
    match goal with
    | [ |- context[let p := ?e in p ~~ _]] => simpl ; unhide
    | [ |- context[hprop_unpack ?e _] ] => 
      let H := fresh "eqq" in let x := fresh "x" in 
        assert (H:exists x, myeq e x); [exists e; reflexivity|destruct H as [x H]; rewrite H]
    end.

  Ltac mysimplr := 
    repeat (progress
    match goal with
    | [ |- context[if eq_nat_dec ?e1 ?e2 then _ else _] ] => 
      destruct (eq_nat_dec e1 e2) ; try congruence ; subst
      | [|- context [match F.AT.A.key_eq_dec ?k1 ?k2 with 
                       | left _ => _ 
                       | right _ => _ end]] =>
      destruct (F.AT.A.key_eq_dec k1 k2) ; try congruence ; subst
    |[H: sigT _ |- _] => destruct H
    | _ => simpl ; auto
    end).


  Lemma sp_index_hyp(P:nat->hprop)(Q R:hprop)(start len i:nat) : 
    i < len -> 
    iter_sep P start i * P (start + i) * iter_sep P (1 + start + i) (len - i - 1) * Q ==> R 
    ->
    iter_sep P start len * Q ==> R.
  Proof.
    intros. eapply hprop_mp. eapply himp_split. apply (split_index_sep P start H). 
    sep auto. auto. 
  Qed.

  Lemma sp_index_conc(P:nat->hprop)(Q R:hprop)(start len i:nat) : 
    i < len -> 
    R ==> iter_sep P start i * P (start + i) * iter_sep P (1 + start + i) (len - i - 1) * Q -> 
    R ==> iter_sep P start len * Q.
  Proof.
    intros. eapply hprop_mp_conc. eapply himp_split. apply (join_index_sep P start H).
    sep auto. auto.
  Qed.

  Lemma look_filter_hash(k:A.key_t)(l:AL.alist_t) : 
   AL.lookup k (filter_hash (hash k) l) = AL.lookup k l.
  Proof.
    induction l; mysimplr; rewrite IHl; auto.
  Qed.

  Ltac sp_index := 
    repeat progress
    match goal with
      | [ |- iter_sep ?P ?s ?len * ?Q ==> ?R ] => 
        eapply (sp_index_hyp P)
      | [ |- ?R ==> iter_sep ?P ?s ?len * ?Q] => 
        eapply (sp_index_conc P) 
      | [ k: AT.A.key_t |- _ < HA.table_size ] => apply (hash_below k)
      | _ => eauto
    end.

  Definition lookup : T.lookup. s;
    refine (fm <- sub_array x (hash k)   (* extract the right bucket *)
              (fun fm => 
                l ~~ [array_length x = HA.table_size] * 
                F.AT.rep fm (filter_hash (hash k) l) * 
                   iter_sep (wf_bucket x l) 0 (hash k) * 
                   iter_sep (wf_bucket x l) (S (hash k)) (HA.table_size - (hash k) - 1))
         ; {{F.lookup fm k (l ~~~ (filter_hash (hash k) l))
               <@> (l ~~ [array_length x = HA.table_size] * 
                 (let p := array_plus x (hash k) in p ~~ p --> fm) *
                 iter_sep (wf_bucket x l) 0 (hash k) * 
                 iter_sep (wf_bucket x l) (S (hash k)) (HA.table_size - (hash k) - 1))}})
    ; unfold rep, wf_bucket ; intros; sep auto.

  search_prem sp_index. sep auto. unhide. sep auto.
  unhide. sep auto.
  rewrite look_filter_hash. sep auto.  fold_ex_conc. sp_index. sep auto.
  Defined. (* this proof could be simpler/more automated. eliminateing fold_ex_conc should be easy *)

  Lemma remove_filter_eq (k:A.key_t)(l:AL.alist_t) : 
    AL.remove k (filter_hash (hash k) l) = filter_hash (hash k) (AL.remove k l).
  Proof. induction l ; simpl ; mysimplr; rewrite IHl; auto. Qed.

  Lemma remove_filter_neq (k:A.key_t)(i:nat)(l:AL.alist_t) : 
    (hash k <> i) -> filter_hash i l = filter_hash i (AL.remove k l).
  Proof. induction l ; simpl ; intros ; mysimplr. rewrite IHl ; auto. Qed.
    
  Definition insert : T.insert. s;
  refine (fm <- sub_array x (hash k) (* find the right bucket *)
           (fun fm =>
             [array_length x = HA.table_size] * 
             (l ~~ F.AT.rep fm (filter_hash (hash k) l) * 
                 iter_sep (wf_bucket x l) 0 (hash k) * 
                 iter_sep (wf_bucket x l) (S (hash k)) (HA.table_size - (hash k) - 1))); 
         (* and use F.insert to insert the key value pair *)
         F.insert fm v (l ~~~ (filter_hash (hash k) l))    
           <@> 
             [array_length x = HA.table_size] * 
             (let p := array_plus x (hash k) in p ~~ p --> fm) * 
             (l ~~ (iter_sep (wf_bucket x l) 0 (hash k) * 
                iter_sep (wf_bucket x l) (S (hash k)) (HA.table_size - (hash k) - 1)))
        @> _) ; 
   unfold rep ; sep sp_index ; unfold wf_bucket ; unhide ; sep mysimplr ;
     rewrite remove_filter_eq ; sep auto ; apply himp_split ; 
     apply iter_imp ; sep auto ; 
     match goal with 
     [ |- context[filter_hash ?i (AT.AL.remove ?k ?x)] ] => 
       assert (hash k <> i) ; try omega ; mysimplr ; rewrite (@remove_filter_neq k i x) ; 
         sep auto
     end.
  Defined.

  Definition remove : T.remove. s;
  refine (fm <- sub_array x (hash k) (* find the right bucket *)
           (fun fm =>
             [array_length x = HA.table_size] * 
             (l ~~ F.AT.rep fm (filter_hash (hash k) l) * 
                 iter_sep (wf_bucket x l) 0 (hash k) * 
                 iter_sep (wf_bucket x l) (S (hash k)) (HA.table_size - (hash k) - 1))); 
         (* and use F.insert to insert the key value pair *)
         F.remove fm k (l ~~~ (filter_hash (hash k) l))    
           <@> 
             [array_length x = HA.table_size] * 
             (let p := array_plus x (hash k) in p ~~ p --> fm) * 
             (l ~~ (iter_sep (wf_bucket x l) 0 (hash k) * 
                iter_sep (wf_bucket x l) (S (hash k)) (HA.table_size - (hash k) - 1)))
        @> _) ; 
   unfold rep ; sep sp_index ; unfold wf_bucket ; unhide ; sep mysimplr ;
     rewrite remove_filter_eq ; sep auto ; apply himp_split ; 
     apply iter_imp ; sep auto ; 
     match goal with 
     [ |- context[filter_hash ?i (AT.AL.remove ?k ?x)] ] => 
       assert (hash k <> i) ; try omega ; mysimplr ; rewrite (@remove_filter_neq k i x) ; 
         sep auto
     end.
  Defined.

End HashTable.

Module Type ORDERED_ASSOCIATION.
  Require Import Relations.

  Variable key_t : Set.
  Variable value_t : key_t -> Set.
  Variable key_eq_dec : forall (k1 k2:key_t), {k1 = k2} + {k1 <> k2}.
  Variable key_lt : key_t -> key_t -> Prop.

  Notation "k1 '<' k2" := (key_lt k1 k2) (at level 70).

  Variable key_lt_eq_total : forall (k1 k2:key_t), {k1 < k2} + {k2 < k1} + {k1 = k2}.
  Variable key_lt_trans : transitive _ key_lt.
  Variable key_lt_irrefl : forall (k1:key_t), ~ k1 < k1.
End ORDERED_ASSOCIATION.

Module OA_FACTS(OA : ORDERED_ASSOCIATION).
Export OA.

Ltac compare_keys k1 k2 :=   
  let klt := (fresh "klt") in
    let kgt := (fresh "kgt") in
      let keq := (fresh "keq") in
    destruct (key_lt_eq_total k1 k2) as [[klt | kgt] | keq].

Lemma key_lt_antisym (k1 k2 : key_t) : k1 < k2 -> k2 < k1 -> False.
Proof. 
intros. refine (@key_lt_irrefl k1 _). apply (key_lt_trans H H0). 
Qed.

Lemma key_eq_dec_derived (k1 k2:key_t) : {k1 = k2} + {k1 <> k2}.
Proof.
  intros k1 k2. compare_keys k1 k2.
    right. intro. subst. apply (key_lt_irrefl klt).
    right. intro. subst. apply (key_lt_irrefl kgt). 
    left. trivial.
Qed.

Lemma key_lt_dec (k1 k2:key_t) : {k1 < k2} + {~ k1 < k2}.
Proof.
  intros k1 k2. compare_keys k1 k2.
    left. trivial. 
    right. intro. eapply key_lt_antisym; eauto.
    right. subst. apply key_lt_irrefl.
Qed.

End OA_FACTS.

(*****************************************************************************************)
(* The splay tree implementation is a functor, parameterized by an ORDERED_ASSOCIATION,  *)
(*****************************************************************************************)
Module SplayMap(OA : ORDERED_ASSOCIATION) : FINITE_MAP with Module A := OA.

  Module OAF := OA_FACTS(OA).
  Import OAF.

(* define functional binary-association-trees. *)
  Module TREE.
    Module AL := AssocList(OA).

(* first, lets define our functional representation: a functional tree. 
   The external representation has already been fixed by SSet: a list.
   However it is useful to have an intermediary representation that
   precisely captures the shape of the data structure. *)

  Inductive tree : Type :=
    Empty
  | Node : forall (k:key_t) (v:value_t k) (left:tree) (right:tree), tree.
 
  (* We now define what it means to be in a (functional) tree *)
  
  Function InT (k':key_t) (t:tree) {struct t} : Prop :=
    match t with
      Empty => False
      | Node k v l r => k = k' \/ InT k' l \/ InT k' r
    end.

  Inductive bst : forall (t:tree), Prop :=
    bst_empty : bst Empty
  | bst_node : forall k (v:value_t k) (l r:tree)
    (bstl : bst l) (bstr:bst r)
    (lessl:forall k', InT k' l -> k' < k)
    (lessr:forall k', InT k' r -> k < k'),
    bst (Node v l r).
  
  (* we now define an inorder traversal of a (functional) tree.  We will
     use this to relate the (functional) tree representation to the
     external list representation *)
  Function inorder (t:tree)
    {struct t} : AL.alist_t :=
    match t with
      Empty => nil
      | Node k v l r => (inorder l) ++ ((k,,v)::nil) ++(inorder r)
    end.

  (* we will be sorting with < *)
  (*  equivalent to Sorting.sort *)

  Definition lelist k (l:AL.alist_t) : Prop :=
    match l with 
      | nil => True
      | (k',,v')::l => if key_lt_dec k k' then True else False
    end.

  Fixpoint sort (l:AL.alist_t) : Prop := 
    match l with 
      | nil => True
      | (k,,v)::l => lelist k l /\ sort l
    end.
  
  Hint Constructors bst : tree.

  Ltac tree_tac tac := repeat (progress match goal with
      | [H:exists a, _ |- _ ] => destruct H
      | [v: _ : value_t ?k |- exists v : value_t ?k, _ ] => exists v
      | [H: sigT _ |- _] => destruct H
      | [|- In ?a (?l1 ++ ?l2)] => apply in_or_app
      | [H:In ?a (?l1 ++ ?l2) |- _] => destruct (in_app_or l1 l2 _ H); clear H
      | [H:In ?a (?x :: ?l) |- _] => destruct (in_inv H); clear H
      | [H: (_,,_) = (_,,_)|- _] => let H1 := (fresh "H") in let H2 := (fresh "H") in  
                                      inversion H as [[H1 H2]]; clear H2; destruct H1
(*      | [|- Sorting.sort _ nil] => constructor
      | [|- Sorting.sort _ (?a::?l)] => constructor
      | [H:Sorting.sort _ (?a::?l)|-_] => inversion H; clear H
      | [|- lelistA _ _ (_::_)] => constructor *)
      | [|- lelist _ (?l1 ++ _)] => destruct l1; simpl
      | [H:True|-_] => clear H
      | [H:lelist _ (_::_)|- _] => inversion H; clear H
      | [|- lelist _ ?l] => destruct (destruct_list l) as [[? [? e]] | e]; rewrite e; simpl in *
      | [H:bst (Node _ _ _)|- _] => inversion H; clear H
      | [|- bst (Node _ _ _)] => constructor
      | [ |- context[if key_lt_dec ?e1 ?e2 then True else False]] => let G := fresh "H" in destruct (key_lt_dec e1 e2) as [G|G]; [trivial|apply G; clear G]
      | [ |- context[if key_lt_dec ?e1 ?e2 then _ else _] ] => destruct (key_lt_dec e1 e2) ; try congruence ; subst
      | [H: if key_lt_dec ?e1 ?e2 then _ else _|-_] => destruct (key_lt_dec e1 e2) ; try congruence ; subst
      | [H:inorder ?x = _ |- context [?x]] => rewrite H
      | _ => try tac; simpl in *; firstorder; eauto with tree; subst
    end).



  Ltac rewriter := repeat match goal with [H:?x = _ |- context [?x]] => rewrite H end.

  (* being in the tree is equivalent to being in the inorder traversal of it *)
  Definition inT_inorder_in (t:tree) (k:key_t) : InT k t -> exists v:value_t k, In (k,,v) (inorder t).
  Proof. intros; functional induction (InT k t); tree_tac idtac. Qed.

  Definition in_inorder_inT (t:tree) (k:key_t) (v:value_t k): In (k,,v) (inorder t) -> InT k t.
  Proof. induction t; tree_tac idtac. Qed.

  Hint Resolve inT_inorder_in in_inorder_inT : tree.

  Lemma sort_app (l1 l2:AL.alist_t) (k:key_t) (v:value_t k) (sort1:sort l1) (sort2:sort ((k,,v) :: l2))
    (dgreat : forall k' v', In (k',,v') l1 -> k' < k) (dless : forall k' v', In (k',,v') l2 -> k < k') :
    sort (l1 ++ ((k,,v)::l2)).
  Proof. induction l1; tree_tac idtac. Qed.

  Lemma lelist_app_inv  k l1 l2 : lelist k (l1 ++ l2) -> lelist k l1.
  Proof. induction l1; tree_tac idtac. Qed.

  Hint Resolve lelist_app_inv sort_app key_lt_trans: tree.

  Lemma sort_in_order l a k v: sort l -> lelist a l -> In (k,,v) l -> a < k.
  Proof. induction l; tree_tac idtac. Qed.

  Lemma sort_app_inv (l1 l2:AL.alist_t) : sort (l1 ++ l2) -> 
        sort l1 
     /\ sort l2 
     /\ forall d1 d2, In d1 l1 -> In d2 l2 -> `d1 < `d2.
  Proof. Hint Resolve lelist_app_inv in_or_app sort_in_order : tree. induction l1; tree_tac idtac. Qed.

  Hint Resolve sort_app_inv : tree.
  Hint Constructors bst : tree.

(* Binary search trees are sorted -- meaning that an inorder traversal should be sorted.
   conversly, if an inorder traversal is sorted, then the tree is a binary search tree. *)
Lemma bst_inorder_sorted (t:tree): bst t -> sort (inorder t).
  induction t; tree_tac idtac. apply sort_app; tree_tac idtac. 
  eapply lessr; eapply in_inorder_inT; tree_tac idtac.
Qed.

Ltac sort_dest := repeat match goal with
                           | [H : sort (?a ++ ?b) |- _] => destruct (sort_app_inv _ _ H); clear H
                         end.
Ltac tree_tac2 tac := tree_tac ltac:(try sort_dest; tac).

Lemma inorder_sorted_bst (t:tree): sort (inorder t) -> bst t.
Proof.
  induction t; tree_tac2 idtac; tree_tac2 idtac. 
  destruct (inT_inorder_in t1 k' H0).
  replace k' with (`(k',,x)); [idtac|auto].
  replace k with (`(k,,v)); [idtac|auto]. auto.
  destruct (inT_inorder_in t2 k' H0).
  replace k' with (`(k',,x)); [idtac|auto].
  replace k with (`(k,,v)); [idtac|auto]. apply H2.

  apply H2.
  apply (inlt (k',,d') (k,,v) ind). intuition.
  clear sort1 sort2 inlt.
  replace (inorder t1 ++ (k,,v) :: inorder t2) with ((inorder t1 ++ (k,,v) :: nil) ++ inorder t2) in b.
  destruct (sort_app_inv _ _ b) as [sort1 [sort2 inlt]].
  intros k' int.
  destruct (in_inorder_in t2 k') as [G1 G2].
  destruct (G1 int) as [d' ind]. clear G1 G2.
  apply (inlt (k,,v) (k',,d')); auto. apply in_or_app. intuition.
  rewrite app_ass; rewrite <- app_comm_cons. auto.
Qed.

  End TREE.

  Import TREE.

  Module AT <: FINITE_MAP_AT with Module A:=OA.
    Module A := OA.
    Module AL := AssocList(A).
    Open Local Scope hprop_scope.

    (* This is our imperative representation of trees.  The left_node and
       right_node contain pointers to other nodes. *) 
    
    Record node : Type :=
      mkNode {
        key : key_t ;
        value : value_t key ;
        left_node : ptr; 
        right_node : ptr
      }.

    (* This is the invariant that relates the imperative model to the
       functional model. It is parameterized by a null location used as a
       sentinel.  Note that it exactly captures the shape of the tree (it is
       precise) as well as the functional node (the functional tree
       representation is unique) *)
    Fixpoint models_tree (nullRef:ptr) (root:ptr) (t:tree) {struct t} :
      hprop :=
      match t with
        Empty => [root = nullRef]
        |  Node k v l r => [root <> nullRef] * Exists n :@ node, [(k,,v) = (key n,,value n)] * 
          ((root-->n) * ((models_tree nullRef (left_node n) l) * (models_tree nullRef (right_node n) r)))
      end.

(* the actual bst invariant: relates the imperative structure with the
external representation (list) using an intermediary functional bst.  

The complete imperative data structure is a base pointer, which points
to the root node of the tree (or nullRef if the tree is empty).
We also use base as nullRef -- yes, it (provably) works ( :). *) 
Definition fmap_t := ptr.
Definition rep(base:fmap_t)(s:AL.alist_t) 
  := (Exists root :@ ptr, (base --> root) *
    Exists t :@ tree,  [bst t] * [Permutation s (inorder t)] * models_tree base root t).

Lemma models_tree_null (nullRef:ptr) (t:tree) : models_tree nullRef nullRef t ==> [t = Empty].
Proof. intros; destruct t; sep auto. Qed.

(* want a flattening lemma *)

(* the model is a unique model of the tree in the heap *)
Lemma models_tree_uniq (nullRef root : ptr) (t1 t2 : tree) :
  models_tree nullRef root t1 & models_tree nullRef root t2 ==> [t1 = t2].
Proof.
  intros nullRef root t1. revert root. 
  induction t1; simpl.
    intros. intro. destruct 1. destruct H. subst. destruct (models_tree_null _ _ _ H0). sep auto.
    intros root t2 h H.
    destruct t2; simpl in H.
    do 4 destruct H. destruct H1. destruct H2. destruct H1; destruct H0; contradiction.

    do 4 destruct H. destruct H1. destruct H2. destruct H1. subst. 
  Admitted. (* there has to be a better proof, adam style. and we may no longer need this lemma anyway... *)

End AT.

  Module T:=FINITE_MAP_T(OA)(AT).

  Import AT.
  
  Open Local Scope stsepi_scope.
  Open Local Scope hprop_scope.

  Module A := OA.
  Ltac s := T.unfm_t; intros.

  Hint Constructors bst.
  Hint Resolve Permutation_refl.


  Lemma models_tree_null' (nullRef:ptr) (t:tree) p : models_tree nullRef nullRef t * p ==> [t = Empty] * p.
  Proof. intros; destruct t; sep auto. Qed.

  Lemma models_tree_null_hyp1 (nullRef:ptr) (t:tree) R : [t = Empty] ==> R -> models_tree nullRef nullRef t ==> R.
  Proof. intros; destruct t; sep auto. do 2 intro. apply (H h). sep auto. Qed.

  Lemma models_tree_null_hyp2 (nullRef:ptr) (t:tree) p R : [t = Empty] * p ==> R -> models_tree nullRef nullRef t * p ==> R.
  Proof. intros; destruct t; sep auto. do 2 intro. apply (H h). exists empty. exists h. sep auto. Qed.

    Ltac find_model :=
      repeat 
        match goal with
          | [|- context [models_tree ?x ?x ?a]] => equate a Empty
          | [|- models_tree ?nullRef ?nullRef ?v ==> ?R] => apply models_tree_null_hyp1
          | [|- models_tree ?nullRef ?nullRef ?v * ?p ==> ?R] => apply models_tree_null_hyp2
        end; eauto.

  Ltac t := unfold rep, AL.nil_al; sep find_model.

  Definition new : T.new. s.
  refine  (*  allocate a new location to be the base of the tree. Initialize to some dummy value *)
         ( base <- New 0 
         (* since base doubles as nullRef, and the tree starts empty, set base to nullRef (itself). *)
         ; base ::= base
         (* return the base of the new tree *)
         ;; {{Return base}})
  ; t. Defined.

Definition free_node_t (nullRef root:ptr) := 
  STsep (ists rep :@ tree, models_tree nullRef root rep) 
  (fun _ : unit => __).

  Require Import Peano_dec.
  Notation "x == y" := (eq_nat_dec x y) (at level 70, no associativity).

Definition free_node' (nullRef:ptr)
  (free_node : forall (root:ptr), free_node_t nullRef root)
  (root:ptr) 
  : free_node_t nullRef root. s. 
  refine (if root == nullRef
          then {{Return tt}}
          else node <- ! root 
             ; free_node (left_node node) 
                <@> ([root <> nullRef] * Exists n :@ AT.node,  ((root-->n)) * (models_tree nullRef (right_node n) r))
            ;; free_node (right_node node) 
                <@> ([root <> nullRef] * Exists n :@ AT.node,  ((root-->n)))
            ;; {{Free root}}); sep find_model.


Next Obligation.
nextvc. destruct H0 as [t models].
poses (models_tree_null models). auto. 
Qed.
Next Obligation.
destruct H0 as [t models].
destruct t; simpl in models; unlift_in models.
(* get rid of the null case *)
  destruct models. contradiction.
destruct models as [nnull [n [datad [i1 [i2 [splitsi_12 [ptsroot [i1_1 [i1_2 [splitsi1_12 [modelsl modelsr]]]]]]]]]]].
nextvc. 
  splits_rewrite_in splitsi1_12 splitsi_12. splits_join_in H0 (1 :: 0 :: 1 :: nil).
  exists i1_1. split. exists t1. trivial.
  exists (union (i1 :: i1_2 :: nil) pf0).
  split. 
    apply* splits_commute. split.
    (* normal cases *)
    intros x [eqx emph2]. inversion_clear eqx. clear x. rewrites.
    nextvc. exists i1_2. split. exists t2. trivial.
    exists i1. split. apply* splits_commute. unfold splits. simpl. 
      exists pf0. trivial.
    
    intros j0 j2. split. intros x [eqx empj2]. inversion_clear eqx. rewrites.
    nextvc. exists empty. exists i1. split.
      eauto.
      nextvc.
    (* exceptional case *)
    intros e [contr rest]. discriminate.
    intros e [contr rest]. discriminate.
Qed.

(* tie the knot *)
Program Definition free_node (nullRef:loc) (root:loc) : free_node_def nullRef root
  := sfix (@free_node' nullRef) root.

Program Definition free_set (base:loc) : free_t bst_inv base
  := sdo ( root <-- !! base
         ; free_node base root
        ;; STsep.sfree base).
Next Obligation.
Proof with trivial.
  rename H into valid1.
  destruct valid1 as [set1 [root [h1 [h2 [splitsh_12 [ptsroot [t [bstt [fp mod]]]]]]]]].
  nextvc.
  exists h2. split.
    exists t...
    exists h1. nextvc.
      nextvc. exists empty. exists h1. nextvc. 
Qed.
