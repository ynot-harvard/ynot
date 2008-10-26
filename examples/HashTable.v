Require Import Ynot.
Require Import FiniteMap.
Set Implicit Arguments.

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
  Open Local Scope hprop_scope.

  Module AT <: FINITE_MAP_AT with Module A:=HA.
    Module A := HA.
    Module AL := AssocList(A).
    Import AL.
    Definition fmap_t : Set := array. (* of F.fmap_t's *)
                                  
    (* We compose the modulo function from the Peano_dec library with the key hash
     * to get something that's guaranteed to be in range. *)
    Program Definition hash(k:A.key_t) : nat := modulo HA.table_size HA.table_size_gt_zero (HA.hash k).

    Ltac simpl_sig := 
      match goal with 
        | [|- context [(proj1_sig ?x)]] => destruct x; simpl
        | [H:context [(proj1_sig ?x)] |- _] => destruct x; simpl in H
      end. 
  
    Lemma hash_below(k:A.key_t) : hash k < HA.table_size.
    Proof. unfold hash; intros; simpl_sig; destruct e; omega. Qed.

    (* given a list of key value pairs, return only those where the hash of the key equals i *)
    Fixpoint filter_hash (i:nat) (l:alist_t) {struct l} : alist_t := 
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
    (* NOTE: this is not being pulled in from Array, because notations don't survive sections *)
    Notation "p ':~~' e1 'in' e2" := (let p := e1 in p ~~ e2) (at level 91, right associativity) : hprop_scope.


    Definition wf_bucket (f:fmap_t) (l:alist_t) (i:nat) : hprop := 
      (Exists r :@ F.AT.fmap_t, 
        (p :~~ array_plus f i in p --> r) * F.AT.rep r (filter_hash i l)).

    (* notation for iter_sep, modeled after list/array comprehensions *)
    Notation "{@ P | i <- s + l }" := (iter_sep (fun i => P) s l) (i ident, s at next level).

    (* A hash-table represents list l if each of the buckets is well-formed with respect
     * to l.  Note that we also have to keep around the fact that the array_length of the
     * array is equal to HA.table_size so that we can free the array. *)
    Definition rep (f:fmap_t) (l:alist_t) : hprop := 
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
  Module AL := F.AT.
  Import AT AL.
  Ltac s := T.unfm_t; intros.

  (* The following is used to initialize an array with empty F.fmap_t's *)
  Definition init_pre(f:array)(n:nat) := 
    {@ p :~~ array_plus f i in (Exists A :@ Set, Exists v :@ A, p --> v) | i <- (HA.table_size - n) + n }.

  Definition init_post (f:array)(n:nat)(_:unit) := {@ wf_bucket f nil_al i | i <- (HA.table_size - n) + n}.
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
                      <@> (init_pre f i * F.AT.rep m nil_al)
                 ;; {{init i _ <@> wf_bucket f nil_al (HA.table_size - S i)}}
         end) ; unfold init_pre, init_post, wf_bucket ; sep sub_simpl.
  Defined.

  (* We allocate an array and then initialize it with empty F.fmap_t's *)
  Definition new : T.new. s.
    refine (  t <- new_array HA.table_size 
            ; @init_table t HA.table_size _
              <@> [array_length t = HA.table_size] 
           ;; {{Return t}}); unfold  init_pre, init_post, rep; sep sub_simpl.
  Defined.

  Definition free_pre (f:array)(l:[alist_t])(n:nat) := l ~~ {@ wf_bucket f l i | i <- (HA.table_size - n) + n}.
  Definition free_post (f:array)(n:nat) (_:unit) := {@ p :~~ array_plus f i in ptsto_any p | i <- (HA.table_size - n) + n}.
  Definition free_spec (f:array)(l:[alist_t])(n:nat) := (n <= HA.table_size) -> STsep (free_pre f l n) (free_post f n).

  (* this definition and notation is useful enough that it probably ought to 
   * go in Separation.v or somewhere else... *)

  Definition inhabit_unpack T U (inh : [T]) (f:T -> U) : [U] := 
    match inh with
    | inhabits v => inhabits (f v)
    end.
  Notation "inh ~~~ f" := (inhabit_unpack inh (fun inh => f)) 
    (at level 91, right associativity) : hprop_scope.

  (* the following runs through the array and calls F.free on each of the buckets. *)
  Definition free_table(f:array)(l:[alist_t])(n:nat) : free_spec f l n.
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
      | [|- context [match A.key_eq_dec ?k1 ?k2 with 
                       | left _ => _ 
                       | right _ => _ end]] =>
      destruct (A.key_eq_dec k1 k2) ; try congruence ; subst
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

  Lemma look_filter_hash(k:A.key_t)(l:alist_t) : 
   lookup k (filter_hash (hash k) l) = lookup k l.
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
      | [ k: A.key_t |- _ < HA.table_size ] => apply (hash_below k)
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

  Lemma remove_filter_eq (k:A.key_t)(l:alist_t) : 
    remove k (filter_hash (hash k) l) = filter_hash (hash k) (remove k l).
  Proof. induction l ; simpl ; mysimplr; rewrite IHl; auto. Qed.

  Lemma remove_filter_neq (k:A.key_t)(i:nat)(l:alist_t) : 
    (hash k <> i) -> filter_hash i l = filter_hash i (remove k l).
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
     [ |- context[filter_hash ?i (remove ?k ?x)] ] => 
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
     [ |- context[filter_hash ?i (remove ?k ?x)] ] => 
       assert (hash k <> i) ; try omega ; mysimplr ; rewrite (@remove_filter_neq k i x) ; 
         sep auto
     end.
  Defined.

End HashTable.
