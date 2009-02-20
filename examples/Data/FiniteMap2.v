(* Copyright (c) 2009, Harvard University
 * All rights reserved.
 *
 * Author: Greg Morrisett
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - The names of contributors may not be used to endorse or promote products
 *   derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

(* Another finite-map development, but this time using records instead of 
 * modules so that things can be first-class.
 *)
Require Import Ynot.
Set Implicit Arguments.

Module FiniteMapInterface.
  Section FiniteMapInterface.
  Variable key_t : Set.
  Variable key_eq_dec : forall (k1 k2:key_t), {k1=k2} + {k1<>k2}.
  Variable value_t : key_t -> Set.

  Inductive alist_t : Set := 
  | Nil_al : alist_t 
  | Cons_al : forall (k:key_t), value_t k -> alist_t -> alist_t.

  Fixpoint remove_al(k:key_t)(l:alist_t) {struct l} : alist_t := 
    match l with
    | Nil_al => Nil_al
    | Cons_al k' v' l' => if key_eq_dec k k' then remove_al k l' 
                          else Cons_al v' (remove_al k l')
    end.

  Definition coerce_al(k1 k2:key_t)(H:k1 = k2)(v:value_t k1) : value_t k2.
    intros. rewrite H in v. apply v. 
  Defined.

  Fixpoint lookup_al(k:key_t)(l:alist_t) {struct l} : option(value_t k) := 
    match l with
    | Nil_al => None
    | Cons_al k' v' l' => 
      match key_eq_dec k' k with
      | left k_eq_k' => Some (coerce_al k_eq_k' v')
      | right k_neq_k' => lookup_al k l'
      end
    end.

  Open Local Scope hprop_scope.
  Record finite_map_t : Type := mkFM { 
    fmap_t : Set ; 
    rep : fmap_t -> alist_t -> hprop ; 
    new : STsep __ (fun (ans:fmap_t) => rep ans Nil_al) ; 
    free : forall (x:fmap_t), STsep (Exists l :@ alist_t, rep x l) (fun (_:unit) => __) ; 
    insert : forall (x:fmap_t)(k:key_t)(v:value_t k)(P:alist_t -> hprop),
               STsep (Exists l :@ alist_t, rep x l * P l)
                     (fun (_:unit) => 
                       Exists l :@ alist_t, rep x (Cons_al v (remove_al k l))
                          * P l) ; 
    lookup : forall (x:fmap_t)(k:key_t)(P:alist_t -> hprop),
               STsep (Exists l :@ alist_t, rep x l * P l)
                     (fun (ans:option (value_t k)) => 
                       Exists l :@ alist_t, rep x l * P l * [ans = lookup_al k l])
  }.
  End FiniteMapInterface.
End FiniteMapInterface.

Module RefAssocList.
  Module F := FiniteMapInterface.
  Section RefAssocList.
  Variable key_t : Set.
  Variable key_eq_dec : forall (k1 k2:key_t), {k1=k2} + {k1<>k2}.
  Variable value_t : key_t -> Set.
  Definition alist_t := F.alist_t value_t.
  Definition Nil := F.Nil_al value_t.
  Definition Cons := @F.Cons_al key_t value_t.

  Open Local Scope stsep_scope.
  Open Local Scope hprop_scope.

  Definition fmap_t := ptr.
  Definition rep(x:fmap_t)(y:alist_t) : hprop := (x --> y).

  Definition new : STsep __ (fun (ans:fmap_t) => rep ans Nil) := New Nil.

  Definition free(x:fmap_t) : STsep (Exists l :@ alist_t, rep x l) (fun _:unit => __) := 
    FreeT x :@ alist_t.

  Definition lookup(x:fmap_t)(k:key_t)(P:alist_t->hprop) : 
    STsep (Exists l :@ alist_t, rep x l * P l)
          (fun (ans:option (value_t k)) => 
            Exists l :@ alist_t, rep x l * P l * [ans = F.lookup_al key_eq_dec k l]).
    intros.
    refine (z <- x !! P ; 
            Return (F.lookup_al key_eq_dec k z) <@> ((x --> z) * P z) @> _) ; sep fail auto.
    Defined.

  Definition insert(x:fmap_t)(k:key_t)(v:value_t k)(P:alist_t -> hprop) :
    STsep (Exists l :@ _, rep x l * P l)
          (fun _:unit => Exists l :@ _, 
            rep x (Cons v (F.remove_al key_eq_dec k l)) * P l).
    intros.
    refine (z <- x !! (fun z => Exists l :@ _, [z = l] * P l) ; 
            x ::= (Cons v (F.remove_al key_eq_dec k z)) <@> 
            (Exists l :@ _, [z=l] * P l) @> _) ; sep fail auto.
    Defined.

  Definition ref_assoc_list : FiniteMapInterface.finite_map_t key_eq_dec value_t := 
    F.mkFM key_eq_dec rep new free insert lookup.
  End RefAssocList.
End RefAssocList.

Module HashTable.
  Section HashTable. 
  Variable key_t : Set.
  Variable key_eq_dec : forall (k1 k2:key_t), {k1=k2}+{k1<>k2}.
  Variable key_hash : key_t -> nat.
  Variable value_t : key_t -> Set.
  Variable table_size : nat.
  Variable table_size_gt_zero : table_size > 0.
  Variable FM : FiniteMapInterface.finite_map_t key_eq_dec value_t.

  Definition alist_t := FiniteMapInterface.alist_t value_t.
  Definition Nil := FiniteMapInterface.Nil_al value_t.
  Definition Cons := @FiniteMapInterface.Cons_al key_t value_t.
  Definition lookup_al := @FiniteMapInterface.lookup_al key_t key_eq_dec value_t.
  Definition remove_al := @FiniteMapInterface.remove_al key_t key_eq_dec value_t.

  Require Import Array.
  Require Import Coq.Arith.Euclid.
  Require Import Coq.Arith.Peano_dec.

  Definition fmap_t : Set := array.
  
  Program Definition hash(k:key_t) : nat := 
    modulo table_size table_size_gt_zero (key_hash k).

  Lemma hash_below(k:key_t) : hash k < table_size.
  Proof. intros ; unfold hash. assert (exists x, x = modulo table_size table_size_gt_zero
    (key_hash k)). eauto. destruct H. rewrite <- H. destruct x. simpl. clear H. 
    destruct e as [q [_ H]]. omega.
  Qed.

  Fixpoint filter_hash(i:nat)(l:alist_t) {struct l} : alist_t := 
    match l with
    | FiniteMapInterface.Nil_al => Nil 
    | FiniteMapInterface.Cons_al k v l' => if eq_nat_dec (hash k) i then Cons v (filter_hash i l') 
                     else filter_hash i l'
    end.

  Open Local Scope stsep_scope.
  Open Local Scope hprop_scope.

  Definition wf_bucket(f:fmap_t)(l:alist_t)(i:nat) : hprop := 
    (Exists r :@ FiniteMapInterface.fmap_t FM,
      (let p := array_plus f i in p ~~ p --> r) * FiniteMapInterface.rep FM r (filter_hash i l)).

  Definition rep(f:fmap_t)(l:alist_t) : hprop := 
    [array_length f = table_size] * iter_sep (wf_bucket f l) 0 table_size.

  Lemma sub_self(x:nat) : (x - x = 0). intros ; omega. Qed.
  Lemma sub_succ(x:nat) : S x <= table_size -> S (table_size - S x) = table_size - x.
    intros ; omega. Qed.

  Definition init_pre(f:fmap_t)(n:nat) := 
    iter_sep (fun i => let p := array_plus f i in p ~~
               (Exists A :@ Set, Exists v :@ A, p --> v)) (table_size - n) n.

  Definition init_table_t(f:fmap_t)(n:nat) := (n <= table_size) -> 
    STsep (init_pre f n) (fun _:unit => iter_sep (wf_bucket f Nil) (table_size - n) n).

  Definition init_table(f:fmap_t)(n:nat) : init_table_t f n.
    intro.
    refine (fix init(n:nat) : init_table_t f n := 
              match n as n' return init_table_t f n' with
              | 0 => fun H => {{Return tt}}
              | S i => fun H => m <- FiniteMapInterface.new FM <@> init_pre f (S i) ; 
                                upd_array f (table_size - S i) m <@> 
                                  (init_pre f i * FiniteMapInterface.rep FM m Nil) ;; 
                                init i _ <@> wf_bucket f Nil (table_size - S i) @> _
              end) ; 
    unfold init_table_t, init_pre, wf_bucket ; sep fail auto ; rewrite (sub_succ H) ; 
      sep fail auto.
  Defined.
      
  Definition new : STsep __ (fun ans:fmap_t => rep ans Nil).
    refine (t <- new_array table_size ; 
            @init_table t table_size _ <@> [array_length t = table_size] ;; 
            {{Return t <@> rep t Nil}}) ; 
    unfold init_table_t, init_pre, rep ; try rewrite sub_self ; sep fail auto.
    rewrite H0 ; sep fail auto.
  Defined.

  Lemma sp_index_hyp(P:nat->hprop)(Q R:hprop)(start len i:nat) : i < len -> 
    iter_sep P start i * P (start + i) * iter_sep P (1 + start + i) (len - i - 1) * Q ==> R 
    -> iter_sep P start len * Q ==> R.
  Proof.
    intros. eapply hprop_mp. eapply himp_split. apply (split_index_sep P start H). 
    sep fail auto. apply H0.
  Qed.

  Lemma sp_index_conc(P:nat->hprop)(Q R:hprop)(start len i:nat) : i < len -> 
    R ==> iter_sep P start i * P (start + i) * iter_sep P (1 + start + i) (len - i - 1) * Q -> 
    R ==> iter_sep P start len * Q.
  Proof.
    intros. eapply hprop_mp_conc. eapply himp_split. apply (join_index_sep P start H).
    sep fail auto. apply H0.
  Qed.
    
  Lemma emp_himp_lift : forall (P:Prop), P -> (__ ==> [P]).
  Proof. sep fail auto. Qed.

  Ltac mytac2 := (eapply sp_index_hyp || eapply sp_index_conc || auto).

  Ltac mysimplr := 
    repeat (progress
    match goal with
    | [ |- context[if eq_nat_dec ?e1 ?e2 then _ else _] ] => 
      destruct (eq_nat_dec e1 e2) ; try congruence ; try subst
    | [ key_eq_dec : _ |- context[if key_eq_dec ?k1 ?k2 then _ else _] ] => 
      destruct (key_eq_dec k1 k2) ; try congruence ; try subst
    | _ => simpl ; auto
    end).

  Lemma look_filter_hash(k:key_t)(l:alist_t) : 
    lookup_al k (filter_hash (hash k) l) = lookup_al k l.
  Proof.
    induction l ; mysimplr ; rewrite IHl ; auto. destruct (key_eq_dec k0 k) ; congruence. 
  Qed.

  (* an attempt to keep the sep tactic from unfolding things -- it's a bit too
   * eager to instantiate existentials in the conclusion of himp's, leading to
   * unrecoverable failure.  *)
  Definition myExists(A:Set)(F:A -> hprop) := Exists x :@ A, F x.


  Ltac fold_ex_conc := 
    search_conc ltac:(try match goal with
                          | [ |- _ ==> (hprop_ex ?f) * _ ] => fold (myExists f)
                          end).

  Ltac sp_index := 
    repeat progress
    match goal with
      | [ |- iter_sep ?P ?s ?len * ?Q ==> ?R ] => 
        eapply (sp_index_hyp P)
      | [ |- ?R ==> iter_sep ?P ?s ?len * ?Q] => 
        eapply (sp_index_conc P) 
      | [ table_size:nat, k:key_t |- _ < table_size ] => apply (hash_below k)
      | _ => eauto
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

  Definition lookup(x:fmap_t)(k:key_t)(P:alist_t -> hprop) :
    STsep (Exists l :@ alist_t, rep x l * P l) 
           (fun (ans:option (value_t k)) => 
              Exists l :@ alist_t, rep x l * P l * [ans = lookup_al k l]).
    intros.
    refine (fm <- sub_array x (hash k)   (* extract the right bucket *)
              (fun fm => 
                [array_length x = table_size] * 
                Exists l :@ alist_t, FiniteMapInterface.rep FM fm (filter_hash (hash k) l) * P l * 
                   iter_sep (wf_bucket x l) 0 (hash k) * 
                   iter_sep (wf_bucket x l) (S (hash k)) (table_size - (hash k) - 1)) ;
           FiniteMapInterface.lookup FM fm k                 (* and use FiniteMapInterface.lookup to find the value *)
              (fun l' => 
                [array_length x = table_size] *
                Exists l :@ alist_t, 
                   [l' = filter_hash (hash k) l] * P l *
                   (let p := array_plus x (hash k) in p ~~ p --> fm) *
                   iter_sep (wf_bucket x l) 0 (hash k) * 
                   iter_sep (wf_bucket x l) (S (hash k)) (table_size - (hash k) - 1)) @>_)
    ; unfold rep, wf_bucket ; intros ; 
    sep fail ltac:(idtac ; 
       match goal with 
         | [ |- iter_sep ?p ?s ?l * ?Q ==> ?R ] => 
           apply (@sp_index_hyp p Q R s l _ (hash_below k)) ; sep fail auto
         | [ |- ?R ==> iter_sep ?P ?s ?l * ?Q ] => 
           apply (@sp_index_conc P Q R s l _ (hash_below k))
         | _ => auto
       end).
    match goal with 
      | [ H : ?v = FiniteMapInterface.lookup_al _ _ _ |- context[?v = lookup_al _ _] ] => 
        rewrite H ; rewrite look_filter_hash ; sep fail auto
    end.
  Defined.

  Lemma remove_filter_eq (k:key_t)(l:alist_t) : 
    remove_al k (filter_hash (hash k) l) = filter_hash (hash k) (remove_al k l).
  Proof. induction l ; simpl ; mysimplr. rewrite IHl. auto. Qed.

  Lemma remove_filter_neq (k:key_t)(i:nat)(l:alist_t) : 
    (hash k <> i) -> filter_hash i l = filter_hash i (remove_al k l).
  Proof. induction l ; simpl ; intros ; mysimplr. rewrite IHl ; auto. Qed.
    
  (* this definition and notation is useful enough that it probably ought to 
   * go in Separation.v or somewhere else... *)
  Definition inhabit_unpack T U (inh : [T]) (f:T -> U) : [U] := 
    match inh with
    | inhabits v => inhabits (f v)
    end.
  Notation "inh ~~~ f" := (inhabit_unpack inh (fun inh => f)) 
    (at level 91, right associativity) : hprop_scope.

  Definition insert(x:fmap_t)(k:key_t)(v:value_t k)(P:alist_t->hprop) : 
    STsep (Exists l :@ _, rep x l * P l) 
          (fun (_:unit) => Exists l :@ _, rep x (Cons v (remove_al k l)) * P l).
  intros.
  refine (fm <- sub_array x (hash k) (* find the right bucket *)
           (fun fm =>
             [array_length x = table_size] * 
             Exists l :@ _, P l * 
               FiniteMapInterface.rep FM fm (filter_hash (hash k) l) * 
               iter_sep (wf_bucket x l) 0 (hash k) * 
               iter_sep (wf_bucket x l) (S (hash k)) 
                        (table_size - (hash k) - 1)) ; 
         (* and use FiniteMapInterface.insert to insert the key value pair *)
         FiniteMapInterface.insert FM fm k v (fun l' => 
             [array_length x = table_size] * 
             (let p := array_plus x (hash k) in p ~~ p --> fm) * 
             Exists l :@ _, P l * 
              [l' = filter_hash (hash k) l] * 
              iter_sep (wf_bucket x l) 0 (hash k) * 
              iter_sep (wf_bucket x l) (S (hash k)) (table_size - (hash k) - 1))
        @> _) ;
  unfold rep, wf_bucket ;
  sep fail ltac:(idtac ; 
    match goal with 
      | [ |- iter_sep ?p ?s ?l * ?Q ==> ?R ] => 
        apply (@sp_index_hyp p Q R s l _ (hash_below k)) ; simpl 
      | [ |- ?R ==> iter_sep ?P ?s ?l * ?Q ] => 
        apply (@sp_index_conc P Q R s l _ (hash_below k)) ; simpl
      | _ => auto
    end) ; sep fail auto. 
  destruct (eq_nat_dec (hash k) (hash k)) ; try congruence ; try subst.
  rewrite remove_filter_eq ; sep fail auto. simpl.
  apply himp_comm_prem. apply himp_split ; apply iter_imp ; sep fail mysimplr ; 
    try (assert False ; [ omega | contradiction ]) ;
     match goal with 
     [ |- context[filter_hash ?i (remove_al ?k ?x)] ] => 
       rewrite (@remove_filter_neq k i x) ; sep fail auto
     end.
  Defined.

  (* the following runs through the array and calls FiniteMapInterface.free on each of the buckets. *)
  Definition free_table_t(f:fmap_t)(n:nat) := (n <= table_size) -> 
    STsep (Exists l :@ _, iter_sep (wf_bucket f l) (table_size - n) n)
       (fun (_:unit) => 
        iter_sep (fun i => let p := array_plus f i in p ~~ ptsto_any p) (table_size - n) n).

  Definition free_table(f:array)(n:nat) : free_table_t f n.
  intro f.
  refine (fix free_tab(n:nat) : free_table_t f n := 
          match n as n' return free_table_t f n' with 
          | 0 => fun H => {{Return tt}}
          | S i => fun H => 
              fm <- sub_array f (table_size - (S i)) 
                       (fun fm => Exists l :@ _, 
                        FiniteMapInterface.rep FM fm (filter_hash (table_size - (S i)) l) * 
                        iter_sep (wf_bucket f l) (table_size - i) i) ;
              FiniteMapInterface.free FM fm <@> 
                 ((let p := array_plus f (table_size - (S i)) in p ~~ p --> fm) *
                  Exists l :@ _, iter_sep (wf_bucket f l) (table_size - i) i) ;; 
              free_tab i _ <@> 
                (let p := array_plus f (table_size - (S i)) in p ~~ ptsto_any p ) @> _
          end) ; simpl ; intros ; try fold_ex_conc ; unfold ptsto_any, wf_bucket ; 
  sep fail auto ; try (rewrite (sub_succ H)) ; sep fail auto.
  Defined.

  (* Run through the array, call FiniteMapInterface.free on all of the maps, and then call array_free *)
  Definition free(f:fmap_t) : STsep (Exists l :@ alist_t, rep f l) (fun (_:unit) => __).
  intros.
  refine (@free_table f table_size _ <@> [array_length f = table_size] ;; 
          free_array f) ; simpl ; auto ; unfold rep, myExists ; 
  rewrite (sub_self table_size) ; sep fail auto. 
  Defined.

  Definition hash_table : FiniteMapInterface.finite_map_t key_eq_dec value_t := 
    FiniteMapInterface.mkFM key_eq_dec rep new free insert lookup.
  End HashTable.
End HashTable.

(*
Require Import Coq.Arith.Peano_dec.
Definition nat_nat_rl := RefAssocList.ref_assoc_list eq_nat_dec (fun _ => nat).
Lemma fourty_two : 42 > 0. auto with arith. Qed.
Definition nat_nat_ht := 
  HashTable.hash_table(key_eq_dec:=eq_nat_dec)(value_t:=(fun _ => nat)) 
  (fun x:nat => x) fourty_two nat_nat_rl.
Check nat_nat_ht.
Check FiniteMapInterface.new nat_nat_ht.
*)
