Require Import List.
Require Import Ynot.
Require Import Arith.
Require Import Omega.
Set Implicit Arguments.

Open Local Scope stsep_scope.
Open Local Scope hprop_scope.

Section Array.

(* I used these to explicitly transform an himp goal -- there's probably a better way *)
Lemma hprop_mp(P1 P2 P3:hprop) : (P1 ==> P2) -> (P2 ==> P3) -> (P1 ==> P3).
Proof. intros. red. intros. pose (H h H1). apply (H0 h p). Qed.

Lemma hprop_mp_conc(P1 P2 P3:hprop) : (P2 ==> P3) -> (P1 ==> P2) -> (P1 ==> P3).
Proof. intros. red. intros. pose (H0 h H1). apply (H h p). Qed.

(* iterating, separating conjunction -- should go in a separate file *)
Fixpoint iter_sep(P:nat->hprop)(start len:nat) {struct len} : hprop :=
  match len with
  | 0 => __
  | S m => (P start) * (iter_sep P (1 + start) m)
  end.

(* split separating conjunction into two pieces *)
Lemma split_sep(P:nat->hprop)(len i:nat)(H:i <= len)(start:nat) :
  ((iter_sep P start len) ==> (iter_sep P start i) * (iter_sep P (start + i) (len - i))).
Proof.
  induction len ; intros. 
  assert (i = 0) ; [ omega | subst ; sep auto].
  induction i ; simpl ; intros ; assert (start + 0 = start) ; try omega. 
  rewrite H0 ; sep auto. assert (start + S i = ((S start) + i)) ; try omega ; 
  rewrite H1 ;sep auto. 
Qed.

(* join two adjacent separating conjunctions *)
Lemma join_sep(P:nat->hprop)(len i:nat)(H:i <= len)(start:nat) : 
  (iter_sep P start i) * (iter_sep P (start + i) (len - i)) ==> iter_sep P start len.
Proof.
  induction len ; intros. 
  assert (i = 0) ; [omega | sep auto].
  induction i ; simpl ; intros ; assert (start + 0 = start) ; try omega. 
  rewrite H0 ; sep auto.
  assert (start + S i = ((S start) + i)) ; try omega ; rewrite H1 ; sep auto.
Qed.

(* split out a particular index, leaving the front and rear *)
Lemma split_index_sep(P:nat->hprop)(start len i:nat) : 
  i < len -> 
  (iter_sep P start len) ==> 
  (iter_sep P start i) * (P (start + i)) * (iter_sep P (1 + start + i) (len - i - 1)).
Proof.
  intros. assert (i <= len). omega. assert (1 <= len - i). omega.
  eapply hprop_mp. apply (split_sep P H0 start). sep auto. 
  eapply hprop_mp. apply (split_sep P H1 (start + i)).
  assert (S (start + i) = start + i + 1). omega. rewrite H2. sep auto. 
Qed.

(* opposite of above *)
Lemma join_index_sep(P:nat->hprop)(start len i:nat) : 
  i < len -> 
  (iter_sep P start i) * (P (start + i)) * (iter_sep P (1 + start + i) (len - i - 1)) ==>
  (iter_sep P start len).
Proof.
  intros. eapply hprop_mp_conc. assert (i <= len). omega. 
  apply (join_sep P H0 start). sep auto. assert (1 <= len - i). omega.
  eapply hprop_mp_conc. apply (join_sep P H0 (start + i)).
  assert (S (start + i) = start + i + 1). omega. rewrite H1. sep auto. 
Qed.

(* simplify proof for iterating separating conjunction implication *)
Lemma iter_imp(P1 P2:nat->hprop)(len start:nat) : 
  (forall i, i >= start -> i < len + start -> P1 i ==> P2 i) -> 
  iter_sep P1 start len ==> iter_sep P2 start len.
Proof.
  induction len. sep auto. sep auto. eapply himp_split. apply H. auto. omega.
  apply (IHlen (S start)). intros. apply H. omega. omega.
Qed.

(*************************************************************************)

(* arrays are an abstract type *)
Parameter array : Set.
(* with an operation that returns the length *)
Parameter array_length : array -> nat.  

(* The array_plus operation is intended for specifications only, hence the 
 * return type of [ptr].  We want to rule out the possibility of doing this
 * pointer arithmetic at run-time, so that a garbage collector won't have
 * track interior pointers.  But this causes many headaches below...
 *)
Parameter array_plus : array -> nat -> [ptr].

(* The assumed operations on arrays -- note that operations such as sub and upd
 * only require that the location being manipulated point to something. *)

(* Create a new array of size n.  Notice that the array contents are not yet initialized. *)
Parameter new_array : forall (n:nat),
                        STsep __ (fun (a:array) => 
                                    [array_length a = n] *
                                    iter_sep
                                      (fun i => p :~~ array_plus a i in p -->? ) 0 n).

(* Destroy an array.  Note that the caller can't destroy part of the array. *)
Parameter free_array : forall (a:array),
                        STsep (iter_sep (fun i => p :~~ array_plus a i in p -->? ) 0 
                                         (array_length a))
                              (fun (_:unit) => __).

(* Read index i from the array.  This is similar to the ref-read in ST *)
Parameter sub_array : forall (A:Type)(a:array)(i:nat)(P : A -> hprop),
                        STsep (p :~~ array_plus a i in 
                                Exists v :@ A, p --> v * P v)
                              (fun (v:A) => 
                                p :~~ array_plus a i in p --> v * P v).

(* Update location a[i] with value v.  Note that this supports a strong update in
 * the sense that the type of v does not have to be the same as the old value in a[i].
 * In addition, note that this allows us to have arrays whose contents hold different
 * types of values at different indices. 
 *)
Parameter upd_array : forall (A:Type)(a:array)(i:nat)(v:A),
                        STsep (p :~~ array_plus a i in 
                                 Exists B :@ Set, Exists w :@ B, p --> w)
                              (fun (_:unit) => 
                                p :~~ array_plus a i in p --> v).
End Array.
