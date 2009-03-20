(* Copyright (c) 2008, Harvard University
 * All rights reserved.
 *
 * Author: Avi Shinnar
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

(* A simple binary search tree implementation, implementing the finite map
 * interface. 
 *)
Require Import Ynot.
Require Import FiniteMap.
Require Import AssocListOrdModel.

Set Implicit Arguments.
  
Module BinaryTree(BT : BINARY_TREE_ASSOCIATION). (* : FINITE_MAP with Module A := BT. *)
  Module A := BT.
  Module AL := AssocListOrdModel(BT).
  Import AL.
  
  Open Local Scope stsepi_scope.
  Open Local Scope hprop_scope.

  Module AT <: FINITE_MAP_AT with Module A:=A with Module AL:=AL.
    Module A := A.
    Module AL := AL.
    Import A AL.

  (* the imperative model *)
    Definition ref(A:Set) := ptr.

    (* A node in the binary tree *)
    Record node_t : Set := 
      Node { node_key : key_t ; node_value : value_t node_key ; 
        node_left : ptr ; node_right : ptr }.

    Definition n_left(n:node_t) : ref(option node_t) := node_left n.
    Definition n_right(n:node_t) : ref(option node_t) := node_right n.
   (* A binary tree is implemented as a ref to an optional node *)
    Definition fmap_t := ref(option node_t).

  (* The rep predicate -- note that I had to call this rep' to avoid 
   * a problem exporting this from the module.  Anyway, when the list is
   * empty, the tree represents it only when it points to None.  When the
   * tree points to Some node with key k and value v, then looking up k in
   * the list should yield v, and the node's left and right sub-trees must  
   * represent the result of filtering out all keys less-than-or-equal/
   * greater-then-or-equal to k. *)
  Inductive rep' : fmap_t -> alist_t -> hprop := 
  | Rep_none : forall x, (x --> None(A:=node_t)) ==> rep' x nil_al
  | Rep_some : forall x k (v:value_t k) xleft xright l,
      x --> Some(Node v xleft xright) * 
      rep' xleft (filter_gte k l) * rep' xright (filter_lte k l)
      * [lookup k l = Some v]
      ==> rep' x l.

  Hint Constructors rep'.
  Definition rep x l := rep' x l * [distinct l].

  (* Unwind the definition of rep' when we know the node that the tree 
   * points to. *)
  Definition node_rep(nopt:option node_t)(l:alist_t) : hprop := 
    match nopt with
    | None => [l = nil_al]
    | Some n => rep' (node_left n) (filter_gte (node_key n) l) * 
      rep' (node_right n) (filter_lte (node_key n) l) * 
      [lookup (node_key n) l = Some (node_value n)]
    end.

  (* Used to eliminate rep' from a premise in an implication *)
  Lemma repinv(x:fmap_t)(l:AL.alist_t)(Q R:hprop) : 
    (x --> None(A:=node_t) * [l = nil_al] * Q ==> R) -> 
    (forall k v xl xr, 
      (x --> Some(Node v xl xr) * rep' xl (filter_gte k l) * 
        rep' xr (filter_lte k l) * [lookup k l = Some v]) * Q ==> R) -> 
    rep' x l * Q ==> R.
  Proof. intros x l Q R H1 H2 h H.
    destruct H as [h1 [h2 [H3 [H4 H5]]]]. 
    destruct H4. apply H1. exists h0. exists h2. sep fail auto.
    generalize h0 H. change (x --> None(A:=node_t) ==> 
    x --> None(A:=node_t) * [nil_al = nil_al]). sep fail auto.
    apply (H2 k v xleft xright). exists h0. eauto. 
  Qed.

  Lemma rep2node_prem(x:fmap_t)(l:AL.alist_t) P Q: 
   (Exists n :@ option node_t, x --> n * node_rep n l * P) ==> Q -> rep' x l * P ==> Q.
  Proof. intros; apply (himp_apply H); apply repinv; sep fail auto. Qed.

  Lemma rep2node_conc(x:fmap_t)(l:AL.alist_t) P Q: 
   P ==> (Exists n :@ option node_t, x --> n * node_rep n l * Q) -> P ==> rep' x l * Q.
  Proof. intros. eapply himp_trans. eexact H. sep fail auto. destruct v; sep fail auto. destruct n.
    pose (@Rep_some x node_key0 node_value0 node_left0 node_right0 l).  simpl.
    apply (himp_apply h). sep fail auto.
  Qed.

  End AT.

  Module T:=FINITE_MAP_T(A)(AT).
  Import A AT.
    
  Ltac unfolder := idtac; apply rep2node_prem.
  Ltac impsimpler := search_conc ltac:(apply rep2node_conc).
  Ltac t := unfold rep; unfold_local; repeat progress (
    repeat progress (sep ltac:(idtac; search_prem unfolder) AL.simpler; auto; impsimpler); simpler; autorewrite with AssocListModel).

  (* The new operation: just allocate a ref and initialize it with None *)
  Definition new : T.new.
    refine( f <- New (None(A:=node_t))
          ; {{ Return f }})
    ; t. Defined.

  (* coq modules are a little annoying... *)
  Lemma filter_distinct' f l : AL.distinct l -> AL.distinct (filter f l).
  Proof. apply filter_distinct. Qed.
  Hint Resolve filter_distinct'.

  (* The free operation -- we must loop over the tree and free each node *)
  Definition free : T.free.
  refine(Fix2 _ _ (fun (free:T.free) f l => 
     n <- ! f 
   ; Free f  
  ;; IfNull n 
     Then {{Return tt}}
     Else free (n_left n) (l ~~~ (filter_gte (node_key n) l)) <@> _
       ;; free (n_right n) (l ~~~ (filter_lte (node_key n) l)))).
  t. t. t. t. t. t. 2: t. t.
Qed.

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

  Lemma fold_hprop P Q: P==>Q -> forall h, P h -> Q h.
  Proof. auto. Qed.

  Lemma filter_length f l: (length (filter f l) < S (length l))%nat.
  Proof. induction l; simpler; auto. omega. Qed.
  Hint Resolve filter_length.

  Lemma lookup_dis_perm' : forall (k : BT.key_t) (l l' : list (sigT BT.value_t)),
       Permutation l l' -> distinct l -> AL.lookup k l = AL.lookup k l'.
  Proof. apply lookup_dis_perm. Qed.

  Lemma filter_gte_length l k v : AL.lookup k l = Some v -> (length (filter_gte k l) < length l)%nat.
  Proof. induction l; AL.t; simpler; intuition; simpler; auto.
    apply Lt.lt_n_S. apply (IHl _ _ H). 
  Qed.

  Lemma filter_lte_length l k v : AL.lookup k l = Some v -> (length (filter_lte k l) < length l)%nat.
  Proof. induction l; AL.t; simpler; intuition; simpler; auto.
    apply Lt.lt_n_S. apply (IHl _ _ H). 
  Qed.

  Lemma perm'_n n x l l' : length l <= n -> [Permutation l l'] * [distinct l] * rep' x l ==> rep' x l'.
  Proof. induction n; sep fail auto; destruct l; simpl in H; try (assert False; [omega|intuition]); perm_simpl. 
    sep fail auto. sep fail auto.
    intros h R. inversion_clear R.
    apply (@Rep_some x k v xleft xright (s0::l')).
    set (ll := (s::l)) in *. set (ll' := (s0::l')) in *.
    revert h H2. apply fold_hprop. search_prem premer.
    search_conc ltac:(apply himp_inj_conc). rewrite (lookup_dis_perm' k H0 H1) in H2. auto.

    unfold hprop_imp in IHn. repeat apply himp_split.
    sep fail auto.
    intros h R. apply IHn with (l:=filter_gte k ll).
    generalize (filter_gte_length ll H2). intro. 
    assert (length ll <= S n) by auto. omega.
    revert h R. apply fold_hprop. repeat search_conc ltac:(apply himp_inj_conc).
    apply filter_perm. auto.
    apply filter_distinct. auto.
    sep fail auto.

    intros h R. apply IHn with (l:=filter_lte k ll).
    generalize (filter_lte_length ll H2). intro. 
    assert (length ll <= S n) by auto. omega.
    revert h R. apply fold_hprop. repeat search_conc ltac:(apply himp_inj_conc).
    apply filter_perm. auto.
    apply filter_distinct. auto.
    sep fail auto.
Qed.

  Lemma perm' x l l' :Permutation l l' -> distinct l -> rep' x l ==> rep' x l'.
  Proof. intros. apply (himp_apply (@perm'_n _ x l l' (le_n _))). t. Qed.

   Lemma perm : T.perm.
   Proof. T.unfm_t; unfold rep; intros. sep fail auto.
     search_conc ltac:(apply himp_inj_conc). apply (distinct_perm H H0).
     apply perm'; auto.
   Qed.

   Lemma perm'_frame x l l' P Q :Permutation l l' -> distinct l -> P ==> Q -> rep' x l * P ==> rep' x l' * Q.
   Proof. Hint Resolve perm'. intros. apply himp_split; auto. Qed.

   Ltac rep'_perm := search_conc ltac:(search_prem ltac:(apply perm'_frame)) || auto.

   (* prove this along with perm *)
   Lemma perm_node_rep n l l' : Permutation l l' -> distinct l -> node_rep n l ==> node_rep n l'.
   Proof. destruct n; simpl.
     sep fail rep'_perm. rewrite (lookup_dis_perm' (node_key n) H H0) in H1. sep fail auto.
     unfold AL.nil_al; sep fail ltac:(perm_simpl || auto).
   Qed.

   Lemma perm_node_swap_frame n l l' P Q : Permutation l l' -> distinct l -> P ==> Q -> node_rep n l * P ==> node_rep n l' * Q.
   Proof. Hint Resolve perm_node_rep. intros. apply himp_split; auto. Qed.

   Ltac nr_perm := search_conc ltac:(search_prem ltac:(apply perm_node_swap_frame)) || auto.
(*
   Fixpoint find_max (l:alist_t) mk (mv:value_t mk) {struct l} :=
     match l with
       | nil => (mk,,mv)
       | (k,,v)::l' => if mk <=! k then find_max l' v else find_max l' mv
     end.

(*   Definition delete_pred_t := forall (x : fmap_t) l, STsep (l ~~ rep x l * [l <> nil])
     (fun d => (l ~~ Exists pf :@ _, rep x (remove (`(find_max l pf)) l) * [d = find_max l ])).
*)
   Definition remove : T.remove.
   refine(Fix3 _ _ (fun (remove:T.remove) f k l =>
      n <- ! f 
    ; IfNull n
      Then {{ Return tt}}
      Else let l_left := (l ~~~ (filter_gte (node_key n) l)) in
           let l_right := (l ~~~ (filter_lte (node_key n) l)) in
             Compare BT.key_cmp k (node_key n)
             WhenLt {{remove (node_left n) k l_left
               <@> (f --> Some n * (l_right ~~ rep' (node_right n) l_right) * 
                 (l ~~ [distinct l] * [AL.lookup (node_key n) l = Some (node_value n)]))}}
             WhenEq ln <- SepRead (node_left n) 
                 (fun ln => (l_left ~~ node_rep ln l_left) *
                   f --> Some n * (l_right ~~ rep' (node_right n) l_right) * 
                   (l ~~ [distinct l] * [lookup (node_key n) l = Some (node_value n)]))
                  ; rn <- SepRead (node_right n)
                  (fun rn => ((node_left n) --> ln * (l_left ~~ node_rep ln l_left)) *
                    f --> Some n * (l_right ~~ node_rep rn  l_right) * 
                   (l ~~ [distinct l] * [lookup (node_key n) l = Some (node_value n)]))
                  ; IfNull ln
                    Then Free (node_right n)
                      ;; Free (node_left n)
                      ;; {{f ::= rn}}
                     Else IfNull rn
                          Then Free (node_right n)
                            ;; Free (node_left n)
                            ;; {{f ::= Some ln}}
                          Else rln <- ! (node_right ln)
                             ; IfNull rln
                               Then Free (node_left n)
                                 ;; Free (node_right ln)
                                 ;; {{f ::= Some (Node (node_value ln) (node_left ln) (node_right n))}}
(*                          Else d <-- delete_pred (left_node node) l_left <@> _
                             ; {{f ::= Some (Node (projT2 d) (left_node n) (right_node n))}}
                             *)Else {{remove f k l}}
             WhenGt {{remove (node_right n) k l_right
               <@> (f --> Some n * 
                 (l_left ~~ rep' (node_left n) l_left) * 
                 (l ~~ [distinct l] * [AL.lookup (node_key n) l = Some (node_value n)]))}})).
 t. t. t. t. t. t. t. t. t. t. t. t. t. t. t. t.

 sep fail nr_perm.
 apply Permutation_sym. pose (remove_perm_filters _ H H0).
 rewrite H1 in p. unfold AL.nil_al in p. rewrite <- app_nil_end in p. exact p.

 t. t. t. t. t.
 t. sep fail auto.
 pose (remove_perm_filters _ H H0). rewrite H2 in p. simpl in p.
 sep fail nr_perm.
 rewrite <- filter_remove. apply filter_perm. apply Permutation_sym; auto.
 rewrite <- filter_remove. apply filter_perm. apply Permutation_sym; auto.

 search_conc ltac:(apply himp_inj_conc).
 cut (AL.lookup (node_key ln0) (remove (node_key n0) x) =
   Some (node_value ln0)); [intro XX; apply XX|idtac].
 rewrite (lookup_dis_perm' (node_key ln0) p (distinct_remove (node_key n0) _ H)). auto.
 sep fail auto.

 subst ln rn.
 sep unfolder idtac. subst ln rn; simpl. sep unfolder idtac.

(* debugging tools *)
Ltac print_goal := idtac; 
  match goal with
    [|- ?g] => idtac g
  end. 

Ltac print_hyps := idtac; 
  try match goal with
        [H: ?g |- _] => idtac H ": " g; fail
end.
Ltac print_all := idtac ""; idtac "subgoal: "; print_hyps; idtac "========================="; print_goal.

search_prem ltac:(apply rep2node_prem). sep fail idtac.
search_prem ltac:(apply rep2node_prem). sep fail idtac.
search_prem ltac:(apply rep2node_prem). sep fail idtac.
search_prem ltac:(apply rep2node_prem). sep fail idtac.

 subst ln rn. sep unfolder idtac. simpl. sep fail auto.
 
 t. t. t. t.
 Qed.

*)

   Definition lookup  : T.lookup.
   refine (Fix3 _ _ (fun (lookup:T.lookup) f k l => 
      n <- ! f
    ; IfNull n
      Then {{ Return None }}
      Else let l_left := (l ~~~ (filter_gte (node_key n) l)) in
           let l_right := (l ~~~ (filter_lte (node_key n) l)) in
             Compare BT.key_cmp k (node_key n)
             WhenLt {{lookup (node_left n) k l_left <@> _
               <@> (f --> Some n * 
                   (l_right ~~ rep' (node_right n) l_right) * 
                   (l ~~ [distinct l] * [AL.lookup (node_key n) l = Some (node_value n)]))}}
             WhenEq {{Return Some(AL.coerce _ (node_value n))}}
             WhenGt {{lookup (node_right n) k l_right
               <@> (f --> Some n * 
                 (l_left ~~ [distinct l_left] * rep' (node_left n) l_left) * 
                 (l ~~ [distinct l] * [AL.lookup (node_key n) l = Some (node_value n)]))}}))
   ; t. Qed.

   Definition insert : T.insert.
   refine(Fix4 _ _ (fun (insert:T.insert) f k v l =>
      n <- ! f 
    ; IfNull n
      Then nleft <- New None(A:=node_t) 
         ; nright <- New None(A:=node_t)
         ; {{ f ::= Some (Node v nleft nright) }}
      Else let l_left := (l ~~~ (filter_gte (node_key n) l)) in
           let l_right := (l ~~~ (filter_lte (node_key n) l)) in
             Compare BT.key_cmp k (node_key n)
             WhenLt {{insert (node_left n) k v l_left
               <@> (f --> Some n * 
                 (l_right ~~ rep' (node_right n) l_right) * 
                 (l ~~ [distinct l] * [AL.lookup (node_key n) l = Some (node_value n)]))}}
             WhenEq {{ f ::= Some (Node v (node_left n) (node_right n)) }}
             WhenGt {{insert (node_right n) k v l_right
               <@> (f --> Some n * 
                 (l_left ~~ rep' (node_left n) l_left) * 
                 (l ~~ [distinct l] * [AL.lookup (node_key n) l = Some (node_value n)]))}}))
  ; t; intuition; t. Qed.

End BinaryTree.