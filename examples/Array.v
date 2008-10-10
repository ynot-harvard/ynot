Require Import List.
Require Import Permutation.
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
  induction len. intros. assert (i = 0). omega. subst. simpl. sep auto.
  induction i ; simpl ; intros. assert (start + 0 = start). omega. rewrite H0. sep auto.
  sep auto. assert (start + S i = ((S start) + i)). omega. rewrite H0. apply IHlen. omega.
Qed.

(* join two adjacent separating conjunctions *)
Lemma join_sep(P:nat->hprop)(len i:nat)(H:i <= len)(start:nat) : 
  (iter_sep P start i) * (iter_sep P (start + i) (len - i)) ==> iter_sep P start len.
Proof.
  induction len. intros. assert (i = 0). omega. subst. sep auto.
  induction i ; simpl ; intros. assert (start + 0 = start). omega. rewrite H0. sep auto.
  sep auto. assert (start + S i = ((S start) + i)). omega. rewrite H0. apply IHlen. omega.
Qed.

(* split out a particular index, leaving the front and rear *)
Lemma split_index_sep(P:nat->hprop)(start len i:nat) : 
  i < len -> 
  (iter_sep P start len) ==> 
  (iter_sep P start i) * (P (start + i)) * (iter_sep P (1 + start + i) (len - i - 1)).
Proof.
  intros. eapply hprop_mp. assert (i <= len). omega. 
  apply (split_sep P H0 start). sep auto. assert (1 <= len - i). omega.
  eapply hprop_mp. apply (split_sep P H0 (start + i)).
  assert (S (start + i) = start + i + 1). omega. rewrite H1. sep auto. 
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

(* Some notation for unpacking pointer arithmetic *)
Notation "p ':~~' e1 'in' e2" := (let p := e1 in p ~~ e2) (at level 91, right associativity) : hprop_scope.

(* Should go in hprop *)
Definition ptsto_any(p:ptr) : hprop := Exists A :@ Set, Exists v :@ A, p --> v.
Notation "p '-->?'" := (ptsto_any p) (at level 38, no associativity) : hprop_scope.

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

(*****************************************************************************)
(* The following derived operations are intended to make it easier to work 
 * with and use the arrays as an aggregate.  We model the contents of the 
 * entire array as a (uniformly-typed) list of values.  The heap-predicate array_ptsto
 * captures the fact that locatins in successive locations of array a point to the
 * successive values in the list vs.
 *)
Fixpoint array_ptsto_start(A:Set)(a:array)(vs:list A)(start:nat) {struct vs} : 
  hprop := 
  match vs with
  | nil => __
  | v::vs => (p :~~ array_plus a start in p --> v) * 
             (array_ptsto_start a vs (1 + start))
  end.

Definition array_ptsto(A:Set)(a:array)(vs:list A) : hprop := array_ptsto_start a vs 0.

(* Used to generate a list of values from a function f *)
Fixpoint gen_list'(A:Set)(f:nat -> A)(n:nat) {struct n} : list A := 
  match n with
  | 0 => nil
  | S m => (f m) :: (gen_list' f m)
  end.
Definition gen_list(A:Set)(f:nat -> A)(n:nat) : list A := List.rev (gen_list' f n).

(* The following loop is used to initialize an array with a list of values, starting
 * at offset i.  I had trouble using "refine" and a fix here (bug in Coq), so I used
 * Russell instead.
 *)
Program Fixpoint array_init_list'(A:Set)(n:nat)(a:array)(vs:list A)(i:nat) {struct vs} : 
                  length vs = n - i -> 
                  STsep (iter_sep (fun i => p :~~ array_plus a i in p -->?) i (n-i))
                        (fun (_:unit) => array_ptsto_start a vs i) := 
  match vs as ws' return 
    length ws' = n - i ->
    STsep (iter_sep (fun i => p :~~ array_plus a i in p -->?) i (n-i))
          (fun (_:unit) => array_ptsto_start a ws' i) with
  | nil => fun H1 => {{Return tt}}
  | w::ws' => fun H1 => upd_array a i w <@> 
                          iter_sep (fun i => p :~~ array_plus a i in p -->?) (1+i) (n-i-1) ;;
                        array_init_list' n a ws' (1+i) _ <@> 
                          (p :~~ array_plus a i in p --> w) @> _
  end.
Next Obligation. rewrite <- H1. sep omega. Defined.
Next Obligation. sep auto. Defined.
Next Obligation. rewrite <- H1. sep auto. assert (length ws' - 0 = length ws'). omega. 
  rewrite H. sep auto. Defined.
Next Obligation. sep auto. Defined.
Next Obligation. sep auto. rewrite <- H1. sep auto. assert (length ws' - 0 = n - S i). omega.
  rewrite H. sep auto. Defined.

(* Initialize array a with the values in the list vs *)
Definition array_init_list(A:Set)(n:nat)(a:array)(vs:list A) : 
  (length vs = n) -> 
  STsep (iter_sep (fun i => p :~~ array_plus a i in p -->?) 0 n)
        (fun (_:unit) => array_ptsto a vs).
  intros.
  refine ({{array_init_list' n a vs 0 _}}).
  omega. assert (n - 0 = n). omega. rewrite H0. sep auto. 
  unfold array_ptsto. sep auto.
Defined.

Lemma GenListLen(A:Set)(f:nat->A)(n:nat) : length (gen_list f n) = n.
Proof. unfold gen_list. induction n. auto. simpl. 
      assert (length (rev (gen_list' f n) ++ (f n) :: nil) = 
              length (rev (gen_list' f n)) + (length ((f n) :: nil))).
  apply app_length. rewrite H. rewrite IHn. simpl. omega. 
Qed.

(* Create and initialize array a at each location with the constant v *)
Definition const_array(A:Set)(n:nat)(v:A) : 
  STsep __ (fun (a:array) => [array_length a = n] * array_ptsto a (gen_list (fun _ => v) n)).
  intros.
  refine (a <- new_array n ; 
          array_init_list a (gen_list (fun _ => v) n) _ <@> [array_length a = n];; 
          Return a <@> [array_length a = n] * array_ptsto a (gen_list (fun _ => v) n) @> _) ;
  sep auto. rewrite (GenListLen (fun _ => v) (array_length v0)). sep auto.
Defined.

(* Create and initialize array a, using the function f to generate the values *)
Definition tabulate_array(A:Set)(n:nat)(f:nat->A) : 
  STsep __ (fun (a:array) => [array_length a = n] * array_ptsto a (gen_list f n)).
  intros.
  refine (a <- new_array n ; 
          array_init_list a (gen_list f n) _ <@> [array_length a = n];;
          Return a <@> [array_length a = n] * array_ptsto a (gen_list f n) @> _) ; 
  sep auto. rewrite (GenListLen f (array_length v)). sep auto.
Defined.

(* The following definitions allow us to easily move between the array_ptsto
 * predicate and the more general iter_sep.
 *)
Definition nth_hprop(A:Set)(P:nat-> A->hprop)(vs:list A)(i:nat) : hprop := 
  match nth_error vs i with
  | None => [False]
  | Some v => P i v
  end.

Definition nth_ptsto(A:Set)(a:array) := 
  nth_hprop (fun i (v:A) => p :~~ array_plus a i in p --> v).

Lemma ListToIter'(A:Set)(a:array)(vs2 vs1:list A)(start:nat) : 
  start = length vs1 -> 
  array_ptsto_start a vs2 start ==> 
    iter_sep (nth_ptsto a (vs1 ++ vs2)) start (length vs2).
Proof.
  induction vs2. sep auto. intros.
  assert (vs1 ++ a0 :: vs2 = (vs1 ++ a0::nil) ++ vs2). clear IHvs2 H. induction vs1.
  auto. simpl. rewrite IHvs1. auto. rewrite H0. simpl. sep auto.
  assert (nth_error ((vs1 ++ a0 :: nil) ++ vs2) (length vs1) = Some a0).
  clear H0 IHvs2. induction vs1. simpl. auto. simpl. auto. unfold nth_ptsto, nth_hprop.
  rewrite H. sep auto. apply (IHvs2 (vs1 ++ a0 :: nil) (S (length vs1))). 
  assert (length (vs1 ++ a0 :: nil) = (length vs1) + (length (a0::nil))). 
  apply app_length. rewrite H1. simpl. omega.
Qed.

(* convert from list model to iterating separating conjunction *)
Lemma ListToIter(A:Set)(a:array)(vs:list A) : 
  array_ptsto a vs ==> iter_sep (nth_ptsto a vs)  0 (length vs).
Proof.
  intros. assert (length nil(A:=A) = 0). auto. apply (ListToIter' a vs nil H).
Qed.

Lemma IterToList'(A:Set)(a:array)(vs2 vs1:list A)(start:nat) : 
  start = length vs1 -> 
  iter_sep (nth_ptsto a (vs1 ++ vs2)) start (length vs2) ==> 
    array_ptsto_start a vs2 start.
Proof.
  induction vs2. sep auto. intros.
  assert (vs1 ++ a0::vs2 = (vs1 ++ a0::nil) ++ vs2). clear IHvs2 H. induction vs1.
  auto. simpl. rewrite IHvs1. auto. rewrite H0. simpl. sep auto.
  assert (nth_error ((vs1 ++ a0 :: nil) ++ vs2) (length vs1) = Some a0). 
  clear H0 IHvs2. induction vs1. simpl. auto. simpl. auto. unfold nth_ptsto, nth_hprop.
  rewrite H. sep auto. apply (IHvs2 (vs1 ++ a0 :: nil) (S (length vs1))).
  assert (length (vs1 ++ a0 :: nil) = length vs1 + length (a0::nil)). 
  apply app_length. rewrite H1. simpl. omega.
Qed.

(* convert from iterating separating conjunction to list model *)
Lemma IterToList(A:Set)(a:array)(vs:list A) : 
  iter_sep (nth_ptsto a vs) 0 (length vs) ==> array_ptsto a vs.
Proof.
  intros. assert (length nil(A:=A) = 0). auto. apply (IterToList' a vs nil H).
Qed.

(* simplify proof for iterating separating conjunction implication *)
Lemma iter_imp(P1 P2:nat->hprop)(len start:nat) : 
  (forall i, i >= start -> i < len + start -> P1 i ==> P2 i) -> 
  iter_sep P1 start len ==> iter_sep P2 start len.
Proof.
  induction len. sep auto. sep auto. eapply himp_split. apply H. auto. omega.
  apply (IHlen (S start)). intros. apply H. omega. omega.
Qed.

(* I wish omega did this by default. *)
Ltac omega_contra := assert False ; [omega | contradiction].

Lemma NthSome(A:Set)(l:list A)(i:nat) : i < length l -> exists v, nth_error l i = Some v.
Proof.
  induction l ; simpl ; intros. omega_contra. induction i ; simpl. eauto. apply IHl. omega.
Qed.

(* Notice we have to generalize array_plus a i in order to get the dependent
 * inversion of the hprop_unpack to fire. *)
Lemma FreeArrayList(A:Set)(a:array)(l:list A)(i:nat) : 
  i < (length l) -> nth_ptsto a l i ==> (p :~~ array_plus a i in p -->?).
Proof.
  intros. unfold nth_ptsto, nth_hprop, ptsto_any. generalize (array_plus a i). 
  destruct (NthSome l H). rewrite H0. sep eauto. sep auto.
Qed.

Fixpoint update_list(A:Set)(vs:list A)(i:nat)(v:A) {struct i} : list A :=
  match (i,vs) with
  | (_,nil) => nil
  | (0,w::vs) => v::vs
  | (S i,w::vs) => w::(update_list vs i v)
  end.

Lemma LengthUpdate(A:Set)(v:A)(l:list A)(i:nat)(H:i < length l) : 
  length (update_list l i v) = length l.
Proof.
  induction l ; simpl ; intros. omega_contra.
  destruct i. auto. assert (i < length l). omega. simpl. rewrite (IHl _ H0). auto.
Qed.

Lemma NthUpdateSame(A:Set)(v:A)(l:list A)(i:nat)(j:nat) : 
  i < length l -> i <> j -> nth_error l j = nth_error (update_list l i v) j.
Proof.
  induction l ; simpl. intros. omega_contra. 
  induction i ; simpl. destruct j. intros. omega_contra. simpl. auto.
  intros. destruct j ; simpl. auto. apply IHl. omega. omega.
Qed.

Lemma NthUpdate(A:Set)(v:A)(l:list A)(i:nat) : 
  i < length l -> nth_error (update_list l i v) i = Some v.
Proof.
  induction l ; induction i ; simpl ; intros ; try omega_contra. auto.
  apply IHl. omega.
Qed.

Lemma ListToIterHyp(A:Set)(a:array)(vs:list A)(Q:hprop) : 
  (iter_sep (nth_ptsto a vs) 0 (length vs) ==> Q) -> 
  (array_ptsto a vs ==> Q).
Proof.
  intros. eapply hprop_mp. apply ListToIter. auto.
Qed.

Lemma ListToIterConc(A:Set)(a:array)(vs:list A)(P:hprop) : 
  (P ==> iter_sep (nth_ptsto a vs) 0 (length vs)) -> 
  (P ==> array_ptsto a vs).
Proof.
  intros. eapply hprop_mp_conc. apply IterToList. auto.
Qed.

Lemma SplitIterHyp(P:nat->hprop)(Q:hprop)(start len i:nat) : 
  i < len -> 
 (((iter_sep P start i) * (P (start + i)) * (iter_sep P (1 + start + i) (len - i - 1))) ==> Q)
  -> 
  ((iter_sep P start len) ==> Q).
Proof.
  intros. eapply hprop_mp. apply (split_index_sep P start H). auto.
Qed.

Lemma SplitIterConc(P:nat->hprop)(Q:hprop)(start len i:nat) : 
  i < len -> 
 (Q ==> ((iter_sep P start i) * (P (start + i)) * (iter_sep P (1 + start + i) (len - i - 1))))
  -> 
  (Q ==> (iter_sep P start len)).
Proof.
  intros. eapply hprop_mp_conc. apply join_index_sep. apply H. auto.
Qed.

Lemma hprop_ex_imp(A:Type)(F:A -> hprop)(P:hprop) : 
  (forall x:A, (F x) ==> P) -> 
  (hprop_ex F) ==> P.
Proof.
  intros. red. unfold hprop_ex. intros. destruct H0. apply (H x h). auto.
Qed.

Lemma nth_some_lt(A:Type)(v:A)(vs:list A)(i:nat) : 
  nth_error vs i = Some v -> i < length vs.
Proof.
  induction vs.
    induction i ; simpl ; unfold error ; intros ; congruence.
  intro. destruct i ; simpl ; intros. omega. pose (IHvs _ H). omega.
Qed.

Lemma lift_ex2(A B:Type)(x:[A])(P:A->hprop)(F:B->hprop) : 
  hprop_unpack x (fun v => (P v) * (hprop_ex F)) ==> hprop_ex F * hprop_unpack x P.
Proof.
  intros. sep auto.
Qed.

Ltac sep_arr_it := 
  repeat (progress
  match goal with
    (* convert array_ptsto to separating conjunction *)
  | [ |- array_ptsto ?a ?l ==> _ ] => apply (ListToIterHyp a l)
  | [ |- _ ==> array_ptsto ?a ?l ] => apply (ListToIterConc a l)
    (* split out separating conjunction when there's a distinguished index *)
  | [ H : ?i < length ?l |- iter_sep ?P ?s (length ?l) ==> ?Q ] => 
      apply (SplitIterHyp(Q:=Q) P s H)
  | [ H : ?i < length ?l |- ?Q ==> iter_sep ?P ?s (length ?l) ] => 
      apply (SplitIterConc(Q:=Q) P s H)
    (* simplify separating conjunction proof *)
  | [ |- iter_sep _ ?s ?x ==> iter_sep _ ?s ?x ] => apply iter_imp
    (* simplify treatment of updated list *)
  | [ H : ?i < length ?l |- 
      nth_ptsto ?a ?l ?x ==> nth_ptsto ?a (update_list ?l ?i ?v) ?x ] => 
     let H2 := fresh "H" in
     assert (H2: i <> x) ; [ omega | unfold nth_ptsto, nth_hprop ; 
                                     rewrite (NthUpdateSame v l H H2) ]
  | [ H : ?i < length ?l |- context[nth_error (update_list ?l ?i ?v) ?i] ] => 
     rewrite (NthUpdate v l H)
  | [ H : ?i < length ?l |- context[length (update_list ?l ?i ?v)]] => 
     rewrite (LengthUpdate v l H)
  | [ |- (Exists x :@ _, _) ==> _ ] => apply hprop_ex_imp
  | _ => auto
  end).

Ltac sep_arr := repeat (progress sep sep_arr_it).

(* an alternative array update interface in terms of the list of values *)      
Definition UpdArray(A:Set)(a:array)(i:nat)(v:A)(vs:[list A]) : 
  STsep (vs ~~ [i < length vs] * array_ptsto a vs)
        (fun (_:unit) => vs ~~ array_ptsto a (update_list vs i v)).
  intros.
  refine {{upd_array a i v <@> 
            (vs ~~ [i < length vs] *
             (iter_sep (nth_ptsto a vs) 0 i * 
               iter_sep (nth_ptsto a vs) (1+i) ((length vs)-i-1)))}} ;
  sep_arr. apply FreeArrayList. auto. unfold nth_ptsto at 4. unfold nth_hprop.
  generalize (array_plus a i). sep_arr. apply himp_split ; sep_arr.
Defined. 

(* similarly for array subscript, but note caller must know the list *)
Definition SubArray(A:Set)(a:array)(i:nat)(vs:[list A]) : 
  STsep (vs ~~ [i < length vs] * array_ptsto a vs)
        (fun (v:A) => vs ~~ array_ptsto a vs * [nth_error vs i = Some v]).
  intros.
  refine {{(sub_array a i (fun v => vs ~~ [nth_error vs i = Some v])
             <@> (vs ~~ [i < length vs] * iter_sep (nth_ptsto a vs) 0 i * 
                        iter_sep (nth_ptsto a vs) (1+i) ((length vs)-i-1)))}} ; 
  sep_arr. unfold nth_ptsto, nth_hprop. destruct (NthSome l H). rewrite H0. 
  generalize (array_plus a i). sep_arr. 
  eapply hprop_mp_conc. eapply himp_split. apply IterToList.
  assert (hprop_unpack [l] (fun vs => [nth_error vs i = Some v]) ==> [nth_error l i = Some v]).
  sep auto. apply H0. assert ((p :~~ (array_plus a i) in (p --> v * hprop_unpack [l] (fun vs =>  [nth_error vs i = Some v]))) ==> (p :~~ (array_plus a i) in p --> v) * (hprop_unpack [l] (fun vs => [nth_error vs i = Some v]))). generalize (array_plus a i). sep_arr. 
  eapply hprop_mp. eapply himp_split. apply himp_refl. eapply himp_split. eapply himp_refl.
  apply H0. sep_arr. unfold nth_ptsto, nth_hprop. rewrite H1. sep_arr.
Defined.

(* here, the caller doesn't need to know the list, but must describe relevant info 
 * with predicate P *)
Definition SubArray2(A:Set)(a:array)(i:nat)(P:list A -> hprop) : 
  STsep (Exists vs :@ list A, [i < length vs] * array_ptsto a vs * P vs)
        (fun (v:A) => 
          Exists vs :@ list A, 
            array_ptsto a vs * [nth_error vs i = Some v] * P vs).
  intros.
  refine {{sub_array a i 
                (fun v => Exists vs :@ list A, 
                   [nth_error vs i = Some v] * 
                   iter_sep (nth_ptsto a vs) 0 i * 
                   iter_sep (nth_ptsto a vs) (1+i) ((length vs)-i-1) * P vs)}}.
  sep_arr. eapply hprop_mp. apply himp_split.
  eapply hprop_mp. apply ListToIter. apply split_index_sep. eauto. apply himp_refl.
  simpl. unfold nth_ptsto at 2. unfold nth_hprop. destruct (NthSome _ H). rewrite H0.
  generalize (array_plus a i). sep_arr. 

  intro. eapply hprop_mp. apply lift_ex2. sep_arr. eapply hprop_mp_conc.
  eapply hprop_mp_conc. apply join_index_sep. apply (nth_some_lt v0 i H). 
  sep_arr. sep_arr. unfold nth_ptsto, nth_hprop. rewrite H. sep_arr.
Defined.
  
End Array.
