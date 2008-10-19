(* This file defines a module interface for finite maps and two implementations,
 * one based on a ref to an association list, and one based on a hash-table.
 * The hash-table functor is parameterized by another finite map implementation
 * so that each bucket in the hash-table is implemented by a "nested" finite map.
 *)
Require Import Ynot.
Set Implicit Arguments.

Notation "( x ,, y )" := (@existT _ _ x y) : core_scope.


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
    forall (x:fmap_t), STsep (Exists l :@ alist_t, rep x l) (fun (_:unit) => __).

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
    forall (x:fmap_t)(k:A.key_t)(P : alist_t -> hprop), 
      STsep (Exists l :@ alist_t, rep x l * P l) 
            (fun (ans:option (A.value_t k)) =>
               Exists l :@ alist_t, rep x l * P l * [ans = lookup k l]).

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
  Declare Module A : ASSOCIATION.
  Declare Module AT : FINITE_MAP_AT with Module A:=A.
  Module T := FINITE_MAP_T(A)(AT).

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

  Ltac t := unfold AT.rep; sep auto.
  Ltac s := T.unfm_t; intros.

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

  Require Import Euclid Peano_dec Array.

  Module AT <: FINITE_MAP_AT with Module A:=HA.
    Module A := HA.
    Module AL := AssocList(A).
    Open Local Scope hprop_scope.

    Definition fmap_t : Set := array. (* of F.fmap_t's *)
                                  
    (* We compose the modulo function from the Peano_dec library with the key hash
     * to get something that's guaranteed to be in range. *)
    Program Definition hash(k:A.key_t) : nat := 
      modulo HA.table_size HA.table_size_gt_zero (HA.hash k).
  
    Lemma hash_below(k:A.key_t) : hash k < HA.table_size.
    Proof.
      intros. unfold hash. destruct modulo.
      simpl. destruct e. omega.
    Qed.

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
    Definition wf_bucket (f:fmap_t) (l:AL.alist_t) (i:nat) : hprop := 
      (Exists r :@ F.AT.fmap_t, 
        (let p := array_plus f i in p ~~ p --> r) * F.AT.rep r (filter_hash i l)).

    (* A hash-table represents list l if each of the buckets is well-formed with respect
     * to l.  Note that we also have to keep around the fact that the array_length of the
     * array is equal to HA.table_size so that we can free the array. *)
    Definition rep (f:fmap_t) (l:AL.alist_t) : hprop := 
      [array_length f = HA.table_size]* iter_sep (wf_bucket f l) 0 HA.table_size.

    Lemma sub_self(x:nat) : (x - x = 0).
    Proof. intros ; omega. Qed.

    Lemma sub_succ(x:nat) : 
      S x <= HA.table_size -> S (HA.table_size - S x) = HA.table_size - x.
    Proof. intros ; omega. Qed.

    Ltac sub_simpl :=
      (repeat 
        match goal with
          | [|- context [?x - ?x]] => rewrite sub_self
          | [|- context [S (HA.table_size - S ?x)]] => rewrite sub_succ; [idtac | solve[auto]]
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
    iter_sep (fun i => 
               let p := array_plus f i in p ~~ 
                 (Exists A :@ Set, Exists v :@ A, p --> v)) (HA.table_size - n) n.

  Definition init_post (f:array)(n:nat)(_:unit) := (iter_sep (AT.wf_bucket f AL.nil_al) (HA.table_size - n) n).
  Definition init_table_spec (f:array)(n:nat) := (n <= HA.table_size) -> STsep (init_pre f n) (init_post f n).

  Definition init_table(f:array)(n:nat) : init_table_spec f n.
  intro.
  refine(
    fix init(n:nat) : init_table_spec f n :=
          match n as n' return init_table_spec f n' with
         | 0 => fun H => {{Return tt}}
         | S i => fun H => 
                    m <- F.new 
                      <@> init_pre f (S i)
                  ; upd_array f (HA.table_size - S i) m
                      <@> (init_pre f i * F.AT.rep m AL.nil_al)
                 ;; {{init i _ <@> AT.wf_bucket f AL.nil_al (HA.table_size - S i)}}
         end) ; unfold init_pre, init_post, wf_bucket ; sep sub_simpl.
  Defined.

  (* We allocate an array and then initialize it with empty F.fmap_t's *)
  Definition new : T.new. s;
    refine (  t <- new_array HA.table_size 
            ; @init_table t HA.table_size _  
                <@> [array_length t = HA.table_size] 
           ;; {{Return t <@> rep t AL.nil_al}}) ; unfold init_pre, init_post, rep ; 
    sep sub_simpl.
  Defined.

  Definition free_pre (f:array)(n:nat) := (Exists l :@ _, iter_sep (wf_bucket f l) (HA.table_size - n) n).
  Definition free_post (f:array)(n:nat) := (fun (_:unit) => 
    iter_sep (fun i => let p := array_plus f i in p ~~ ptsto_any p) 
    (HA.table_size - n) n).
  Definition free_spec (f:array)(n:nat) := (n <= HA.table_size) -> STsep (free_pre f n) (free_post f n).


  (* the following runs through the array and calls F.free on each of the buckets. *)
  Definition free_table(f:array)(n:nat) : free_spec f n.
  intro f.
  refine (fix free_tab(n:nat) : free_spec f n := 
          match n as n' return free_spec f n' 
          with
          | 0 => fun H => {{Return tt}}
          | S i => fun H => let j := HA.table_size - (S i) in
                              let p := array_plus f j in 
              fm <- sub_array f j 
                       (fun fm => Exists l :@ _,
                        F.AT.rep fm (filter_hash j l) * 
                        iter_sep (wf_bucket f l) (HA.table_size - i) i) 
            ; F.free fm 
                <@> ((p ~~ p --> fm) * free_pre f i)
           ;; {{free_tab i _
                <@> (p ~~ ptsto_any p )}}
          end); unfold free_pre, free_post, wf_bucket, ptsto_any; try solve[
(* the first goal *)
simpl; apply himp_comm_conc; apply himp_empty_conc; apply himp_refl];
(* the other ones *)
sep sub_simpl; try subst j; try (rewrite H0; sep sub_simpl).
Defined.

  (* Run through the array, call F.free on all of the maps, and then call array_free *)
  Definition free : T.free. s.
  refine (@free_table x HA.table_size _ 
              <@> [array_length x = HA.table_size] 
      ;; free_array x)
    ; unfold free_pre, free_post, rep; sep sub_simpl; rewrite H; sep auto.
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
                [array_length x = HA.table_size] * 
                Exists l :@ AL.alist_t, F.AT.rep fm (filter_hash (hash k) l) * P l * 
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
    unfold rep, wf_bucket ; intros ; fold_ex_conc ; sep sp_index ; unfold myExists.
    unhide ; sep auto.
    unhide ; sep auto.
    apply himp_empty_conc' ; apply himp_ex_conc ; econstructor ; 
      search_conc ltac:(eapply sp_index_conc) ; sp_index;
      rewrite look_filter_hash ; sep auto.
  Defined.

  Lemma remove_filter_eq (k:A.key_t)(l:AL.alist_t) : 
    AL.remove k (filter_hash (hash k) l) = filter_hash (hash k) (AL.remove k l).
  Proof. induction l ; simpl ; mysimplr; rewrite IHl; auto. Qed.

  Lemma remove_filter_neq (k:A.key_t)(i:nat)(l:AL.alist_t) : 
    (hash k <> i) -> filter_hash i l = filter_hash i (AL.remove k l).
  Proof. induction l ; simpl ; intros ; mysimplr. rewrite IHl ; auto. Qed.

  (* this definition and notation is useful enough that it probably ought to 
   * go in Separation.v or somewhere else... *)
  Definition inhabit_unpack T U (inh : [T]) (f:T -> U) : [U] := 
    match inh with
    | inhabits v => inhabits (f v)
    end.
  Notation "inh ~~~ f" := (inhabit_unpack inh (fun inh => f)) 
    (at level 91, right associativity) : hprop_scope.

    
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
