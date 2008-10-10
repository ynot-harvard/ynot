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
                     (fun (_:unit) => Exists l :@ alist_t, 
                         rep x (Cons_al v (remove_al k l)) * P l) ; 
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
            Return (F.lookup_al key_eq_dec k z) <@> ((x --> z) * P z) @> _) ; sep auto.
    Defined.

  Definition insert(x:fmap_t)(k:key_t)(v:value_t k)(P:alist_t->hprop) : 
    STsep (Exists l :@ alist_t, rep x l * P l)
      (fun _:unit => Exists l :@ alist_t, rep x (Cons v (F.remove_al key_eq_dec k l)) * P l).
    intros.
    refine (z <- x !! P ; 
            x ::= (Cons v (F.remove_al key_eq_dec k z)) <@> P z @> _) ; sep auto.
    Defined.

  Definition ref_assoc_list : FiniteMapInterface.finite_map_t key_eq_dec value_t := 
    F.mkFM key_eq_dec rep new free insert lookup.
  End RefAssocList.
End RefAssocList.

Module HashTable.
  Module F := FiniteMapInterface.
  Section HashTable. 
  Variable key_t : Set.
  Variable key_eq_dec : forall (k1 k2:key_t), {k1=k2}+{k1<>k2}.
  Variable key_hash : key_t -> nat.
  Variable value_t : key_t -> Set.
  Variable table_size : nat.
  Variable table_size_gt_zero : table_size > 0.
  Variable FM : F.finite_map_t key_eq_dec value_t.

  Definition alist_t := F.alist_t value_t.
  Definition Nil := F.Nil_al value_t.
  Definition Cons := @F.Cons_al key_t value_t.
  Definition lookup_al := @F.lookup_al key_t key_eq_dec value_t.
  Definition remove_al := @F.remove_al key_t key_eq_dec value_t.

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
    | F.Nil_al => Nil 
    | F.Cons_al k v l' => if eq_nat_dec (hash k) i then Cons v (filter_hash i l') 
                     else filter_hash i l'
    end.

  Open Local Scope stsep_scope.
  Open Local Scope hprop_scope.

  Definition wf_bucket(f:fmap_t)(l:alist_t)(i:nat) : hprop := 
    (Exists r :@ F.fmap_t FM,
      (let p := array_plus f i in p ~~ p --> r) * F.rep FM r (filter_hash i l)).

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
              | S i => fun H => m <- F.new FM <@> init_pre f (S i) ; 
                                upd_array f (table_size - S i) m <@> 
                                  (init_pre f i * F.rep FM m Nil) ;; 
                                init i _ <@> wf_bucket f Nil (table_size - S i) @> _
              end) ; 
    unfold init_table_t, init_pre, wf_bucket ; sep auto ; rewrite (sub_succ H) ; sep auto.
  Defined.
      
  Definition new : STsep __ (fun ans:fmap_t => rep ans Nil).
    refine (t <- new_array table_size ; 
            @init_table t table_size _ <@> [array_length t = table_size] ;; 
            {{Return t <@> rep t Nil}}) ; 
    unfold init_table_t, init_pre, rep ; sep auto. rewrite H0 ; sep auto.
    rewrite (sub_self table_size) ; sep auto. rewrite (sub_self (array_length v)) ; sep auto.
  Defined.

  Lemma sp_index_hyp(P:nat->hprop)(Q R:hprop)(start len i:nat) : i < len -> 
    iter_sep P start i * P (start + i) * iter_sep P (1 + start + i) (len - i - 1) * Q ==> R 
    -> iter_sep P start len * Q ==> R.
  Proof.
    intros. eapply hprop_mp. eapply himp_split. apply (split_index_sep P start H). 
    sep auto. apply H0.
  Qed.

  Lemma sp_index_conc(P:nat->hprop)(Q R:hprop)(start len i:nat) : i < len -> 
    R ==> iter_sep P start i * P (start + i) * iter_sep P (1 + start + i) (len - i - 1) * Q -> 
    R ==> iter_sep P start len * Q.
  Proof.
    intros. eapply hprop_mp_conc. eapply himp_split. apply (join_index_sep P start H).
    sep auto. apply H0.
  Qed.
    
  Lemma emp_himp_lift : forall (P:Prop), P -> (__ ==> [P]).
  Proof. sep auto. Qed.

  Ltac mytac2 := (eapply sp_index_hyp || eapply sp_index_conc || auto).

  Ltac mysimplr := 
    repeat (progress
    match goal with
    | [ |- context[if eq_nat_dec ?e1 ?e2 then _ else _] ] => 
      destruct (eq_nat_dec e1 e2) ; try congruence ; subst
    | [ |- context[if key_eq_dec ?k1 ?k2 then _ else _] ] => 
      destruct (key_eq_dec k1 k2) ; try congruence ; subst
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

  Definition lookup(x:fmap_t)(k:key_t)(P:alist_t -> hprop) :
    STsep (Exists l :@ alist_t, rep x l * P l) 
           (fun (ans:option (value_t k)) => 
              Exists l :@ alist_t, rep x l * P l * [ans = lookup_al k l]).
    intros.
    refine (fm <- sub_array x (hash k)   (* extract the right bucket *)
              (fun fm => 
                [array_length x = table_size] * 
                Exists l :@ alist_t, F.rep FM fm (filter_hash (hash k) l) * P l * 
                   iter_sep (wf_bucket x l) 0 (hash k) * 
                   iter_sep (wf_bucket x l) (S (hash k)) (table_size - (hash k) - 1)) ;
           F.lookup FM fm k                 (* and use F.lookup to find the value *)
              (fun l' => 
                [array_length x = table_size] *
                Exists l :@ alist_t, 
                   [l' = filter_hash (hash k) l] * P l *
                   (let p := array_plus x (hash k) in p ~~ p --> fm) *
                   iter_sep (wf_bucket x l) 0 (hash k) * 
                   iter_sep (wf_bucket x l) (S (hash k)) (table_size - (hash k) - 1)) @> _);
    unfold rep. sep auto. eapply himp_comm_prem. eapply sp_index_hyp. apply (hash_below k).
    unfold wf_bucket at 2. unhide. sep auto. fold_ex_conc. sep auto. sep mytac. exists v1.
    sep auto. eapply sp_index_conc. apply (hash_below k). unfold wf_bucket. sep auto.
    rewrite H1. rewrite H0. rewrite look_filter_hash ; mytac ; auto. sep auto. unhide.
    sep auto.
  Defined.

  Lemma remove_filter_eq (k:key_t)(l:alist_t) : 
    remove_al k (filter_hash (hash k) l) = filter_hash (hash k) (remove_al k l).
  Proof. induction l ; simpl ; mysimplr. rewrite IHl. auto. Qed.

  Lemma remove_filter_neq (k:key_t)(i:nat)(l:alist_t) : 
    (hash k <> i) -> filter_hash i l = filter_hash i (remove_al k l).
  Proof. induction l ; simpl ; intros ; mysimplr. rewrite IHl ; auto. Qed.
    
  Definition insert(x:fmap_t)(k:key_t)(v:value_t k)(P:alist_t -> hprop) : 
    STsep (Exists l :@ alist_t, rep x l * P l) 
          (fun (_:unit) => Exists l :@ alist_t, rep x (Cons v (remove_al k l)) * P l).
  intros.
  refine (fm <- sub_array x (hash k) (* find the right bucket *)
           (fun fm =>
             [array_length x = table_size] * 
             myExists (fun l : alist_t => 
                  (P l * F.rep FM fm (filter_hash (hash k) l) * 
                   iter_sep (wf_bucket x l) 0 (hash k) * 
                   iter_sep (wf_bucket x l) (S (hash k)) (table_size - (hash k) - 1)))) ; 
         F.insert FM fm k v     (* and use F.insert to insert the key value pair *)
           (fun l' => 
             [array_length x = table_size] * 
             myExists (fun l : alist_t => 
                     [l' = filter_hash (hash k) l] * 
                     P l * (let p := array_plus x (hash k) in p ~~ p --> fm) *
                     iter_sep (wf_bucket x l) 0 (hash k) * 
                     iter_sep (wf_bucket x l) (S (hash k)) (table_size - (hash k) - 1)))
        @> _) ; 
   unfold rep. sep auto. apply himp_comm_prem. eapply sp_index_hyp. apply (hash_below k).
   unfold wf_bucket at 2. unhide. sep auto. unfold myExists. sep mytac. exists v0. 
   sep auto. intros. fold_ex_conc. unfold myExists at 1. sep auto. sep mytac. exists v2. 
   sep auto. eapply himp_empty_conc'. eapply sp_index_conc. apply (hash_below k). 
   unfold wf_bucket at 4. unhide ; sep auto ; mysimplr. rewrite H0. rewrite remove_filter_eq.
   destruct (eq_nat_dec (hash k) (hash k)) ; try congruence. sep auto. apply himp_comm_prem. 
   apply himp_split ; apply iter_imp ; unfold wf_bucket ; sep auto ; assert (hash k <> i) ;
   try omega ; mysimplr ; destruct (eq_nat_dec (hash k) i) ; try congruence ; 
   rewrite (remove_filter_neq _ v2 n) ; sep auto. unhide. unfold myExists at 1. 
   fold_ex_conc. sep auto. sep mytac. exists (filter_hash (hash k) v1). sep mytac. 
  Defined.

  (* the following runs through the array and calls F.free on each of the buckets. *)
  Definition free_table_t(f:fmap_t)(n:nat) := (n <= table_size) -> 
    STsep (myExists (fun l => iter_sep (wf_bucket f l) (table_size - n) n))
       (fun (_:unit) => 
        iter_sep (fun i => let p := array_plus f i in p ~~ ptsto_any p) (table_size - n) n).

  Definition free_table(f:array)(n:nat) : free_table_t f n.
  intro f.
  refine (fix free_tab(n:nat) : free_table_t f n := 
          match n as n' return free_table_t f n' with 
          | 0 => fun H => {{Return tt}}
          | S i => fun H => 
              fm <- sub_array f (table_size - (S i)) 
                       (fun fm => myExists (fun l => 
                        F.rep FM fm (filter_hash (table_size - (S i)) l) * 
                        iter_sep (wf_bucket f l) (table_size - i) i)) ;
              F.free FM fm <@> 
                 ((let p := array_plus f (table_size - (S i)) in p ~~ p --> fm) *
                  myExists (fun l => iter_sep (wf_bucket f l) (table_size - i) i)) ;; 
              free_tab i _ <@> 
                (let p := array_plus f (table_size - (S i)) in p ~~ ptsto_any p ) @> _
          end) ; simpl ; intros. unfold myExists ; sep auto. unfold myExists ; sep auto.
  unfold myExists at 1. unfold wf_bucket at 1. unhide ; sep auto. unfold myExists ; sep auto. 
  rewrite (sub_succ H) ; sep auto. unfold myExists ; sep auto. auto with arith. unhide.
  sep auto. rewrite (sub_succ H) ; sep auto. unhide ; sep auto. unfold ptsto_any ; sep auto.
  unhide. unfold myExists. repeat fold_ex_conc. sep auto. unfold myExists. sep auto.
  Defined.

  (* Run through the array, call F.free on all of the maps, and then call array_free *)
  Definition free(f:fmap_t) : STsep (Exists l :@ alist_t, rep f l) (fun (_:unit) => __).
  intros.
  refine (@free_table f table_size _ <@> [array_length f = table_size] ;; 
          free_array f) ; simpl ; auto ; unfold rep, myExists ; 
  rewrite (sub_self table_size) ; sep auto. 
  Defined.

  Definition hash_table : FiniteMapInterface.finite_map_t key_eq_dec value_t := 
    F.mkFM key_eq_dec rep new free insert lookup.
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
