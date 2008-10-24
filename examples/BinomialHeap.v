(* Priority Queues as Binomial Heaps *)

Require Import List.
Require Import Ynot.

Set Implicit Arguments.

(* Some helpers *)
Section T.
 Variables (T: Set) 
           (f: T -> T -> bool)  
           (eqT : forall (x y: T), {x = y} + {x <> y}).

Definition antisymmetric := forall a b, f a b = true /\ f b a = true -> a = b.
  
Definition transitive := forall a b c,
   f a b = true /\ f b c = true -> f a c = true.

Definition total := forall a b, f a b = true \/ f b a = true.  
  
Fixpoint sorted (ls : list T) : Prop :=
  match ls with
    | a :: bc => match bc with
                   | nil => True 
                   | b :: c  => f a b = true /\ sorted bc   
                 end
    | nil => True
  end.

  Fixpoint del (x: T) (ls: list T) :=
    match ls with
      | nil => nil
      | a :: b => if eqT x a then b else (a :: (del x b))
    end. 
  
  Fixpoint minimal (x: T) (ls: list T) :=
    match ls with
      | nil => True
      | a :: b => f x a = true /\ minimal x b
    end.

  Definition slist := sig sorted.

  Definition snil : slist := exist sorted nil I .

  Conjecture insert : slist -> T -> slist.

  Conjecture insert_ok : forall sls x, exists a, exists b, 
    proj1_sig sls = a :: b /\ proj1_sig (insert sls x) = a :: x :: b. 

Theorem c1 : forall (ls0: slist) x' ls',
proj1_sig ls0 = x' :: ls'  -> sorted  (x' :: ls').
 intros ls0 x' ls' H; destruct ls0; simpl in H; congruence. Defined.  

End T.

(* There's a few ways to represent priority queues.
   Here are three interfaces. *) 

(* This interface uses unsorted lists. 
   Arguably, these should be sets. *)
Module Type PRIORITY_QUEUE_1.
  Section PRIORITY_QUEUE.
  Variable T : Set.
  Variable ord : T -> T -> bool.  
  Variable eqT : forall (a b: T), {a = b} + {a <> b}.

  Axiom ord_antisymmetric : antisymmetric ord.
  Axiom ord_transitive : transitive ord.
  Axiom ord_total : total ord.

  Parameter t : Set.
 
  Parameter rep : t -> list T -> hprop.

  Parameter new : 
    STsep __ (fun q : t => rep q nil).
  Parameter free : forall (q : t),
    STsep (rep q nil) (fun _ : unit => __)%hprop.
    
  Parameter enqueue : forall (q : t) (x : T) (ls : [list T]) ,
    STsep (ls ~~ rep q ls)
          (fun _ : unit => ls ~~ rep q (x :: ls))%hprop.

  Parameter dequeue : forall (q : t) (ls : [list T]) ,
    STsep (ls ~~ rep q ls) (fun xo => ls ~~ match xo with
                                              | None => [ls = nil] * rep q ls
                                              | Some x =>
                                                match ls with
                                                  | nil => [False]
                                                  | _   => [minimal ord x ls /\ In x ls] * rep q (del eqT x ls)  
                                                end
                                            end)%hprop.
End PRIORITY_QUEUE.
End PRIORITY_QUEUE_1.

(* This priority queue interface uses sorted lists 
   directly as representatives. *)
Module Type PRIORITY_QUEUE_2.
  Section PRIORITY_QUEUE.
  Variable T : Set.
  Variable ord : T -> T -> bool.  

  Axiom ord_antisymmetric : antisymmetric ord.
  Axiom ord_transitive : transitive ord.
  Axiom ord_total : total ord.

  Parameter t : Set.
 
  Parameter rep : t -> slist ord -> hprop.

  Parameter new : 
    STsep __ (fun q : t => rep q (snil ord)).
  Parameter free : forall (q : t),
    STsep (rep q (snil ord)) (fun _ : unit => __)%hprop.
    
  Parameter enqueue : forall (q : t) (x : T) (ls : [slist ord]) ,
    STsep (ls ~~ rep q ls)
          (fun _ : unit => ls ~~ rep q (insert ls x))%hprop.

(* not needed as a parameter *)
  Parameter thm1: forall a b, sorted ord (a :: b) -> sorted ord b.

  Parameter dequeue : forall (q : t) (ls : [slist ord]) ,
    STsep (ls ~~ rep q ls) (fun xo => ls ~~ match xo with
                                              | None => [ls = snil ord] * rep q ls
                                              | Some x =>
                                                match proj1_sig ls as ls0 return proj1_sig ls = ls0 -> hprop with
                                                  | nil => fun _ => [False]
                                                  | x' :: ls' => fun pf => [x' = x] * 
                                                    rep q (exist (sorted ord) ls' (thm1 x' ls' (c1 ls pf) )) end (refl_equal (proj1_sig ls))
 end)%hprop.

End PRIORITY_QUEUE.
End PRIORITY_QUEUE_2.

(* This priority queue interface uses an arbitrary list
   as a modelling type but the representation relation
   requires lists to be sorted; this is expressed as an axiom.
   The postconditions ensure that sorted modelling lists
   remain sorted. *)
Module Type PRIORITY_QUEUE_3.
  Section PRIORITY_QUEUE.
  Variable T : Set.
  Variable ord : T -> T -> bool.  

  Axiom ord_antisymmetric : antisymmetric ord.
  Axiom ord_transitive : transitive ord.
  Axiom ord_total : total ord.

  Parameter t : Set.

  Parameter rep : t -> list T -> hprop.

  Parameter new : 
    STsep __ (fun q : t => rep q nil).
  Parameter free : forall (q : t),
    STsep (rep q nil) (fun _ : unit => __)%hprop.
    
  Parameter enqueue : forall (q : t) (x : T) (ls : [list T]) ,
    STsep (ls ~~ rep q ls)
          (fun _ : unit => ls ~~ rep q ((fix f (ls : list T) :=
                                           match ls with
                                             | nil => x :: nil
                                             | a :: b => if ord a x
                                                         then x :: ls
                                                         else a :: f b
                                           end) ls))%hprop.

  Parameter dequeue : forall (q : t) (ls : [list T]) ,
    STsep (ls ~~ rep q ls) (fun xo => ls ~~ match xo with
                                              | None => [ls = nil] * rep q ls
                                              | Some x =>
                                                match ls with
                                                  | nil => [False]
                                                  | x' :: ls' => [x' = x] * rep q ls'
                                                end
                                            end)%hprop.

Axiom rep_sorted : forall q ls h, rep q ls h -> sorted ord ls.

End PRIORITY_QUEUE.
End PRIORITY_QUEUE_3.

Section BINOMIAL_TREE.

Variable A:Set.
Variable a:A. (* for testing *)

(* From wikipedia:
   A binomial heap is represented as a collection of binomial
   trees.  A binomial tree is defined recursively:
    - a tree of order 0 is a single node
    - a tree of order k has a root node whose children are
      roots of binomial trees of orders k-1, k-2... 1, 0,
      in this order.
*)

(* The element associated with each tree is at
   the *end* of the list of trees. *)
Fixpoint btree (n: nat) : Type:=
  match n with
    | 0 => A
    | S n' => prod ptr (btree n')
  end.

Eval simpl in btree 2.
Definition t2 := (1, (0, a)) : btree 2. 
Definition t3 := (2, (1, (0, a))) : btree 3.

Open Scope hprop_scope.

Fixpoint rep' (n: nat) {struct n} : btree n -> hprop :=
 match n as n return btree n -> hprop with
  | 0 => fun (a0: A) => [a0 = a0] (* helps with counting elements *)
  | S n' => fun (bt: prod ptr (btree n')) => rep' n' (snd bt) *
             (Exists bt' :@ btree n', fst bt --> bt' * rep' n' bt')
 end. 

Definition rep (n: nat) (p: ptr) : hprop :=
 Exists bt :@ btree n, p --> bt.

Eval simpl in rep' 2 t2.
(*  = [a = a] * (Exists bt' :@ A, 0 --> bt' * [bt' = bt']) *
       (Exists bt' :@ ptr * A,
        1 --> bt' *
        ([snd bt' = snd bt'] *
         (Exists bt'0 :@ A, fst bt' --> bt'0 * [bt'0 = bt'0])))
     : hprop  *)

(* Attach one as the leftmost child of the other *)
Conjecture merge : forall (n: nat) (p1 p2: ptr), 
 STsep (rep n p1 * rep n p2)
       (fun r:unit => rep (S n) p1).
 (* this is too weak, need to rep a btree n with a list of length 2^(n+1) *)
 (* in retrospect,don't need to index with n *)
Inductive ilist : nat -> Set :=
 | inil : A -> ilist 1
 | icons : forall n, ilist n -> ilist n -> ilist (n+n).

(* Fixpoint rep0' (n: nat) (ls: ilist (S n)) {struct ls} : btree n -> hprop :=
 match ls in ilist n0 return btree  with
  | inil a0 => [True]
  | icons n0 l1 l2 => fun _ => [True]
 end.

Fixpoint rep0' (n: nat) {struct n} : btree n -> ilist (S n) -> hprop :=
 match n as n return btree n -> ilist (S n) -> hprop with
  | 0 => fun (a0: A) (ls: ilist 1) => [ls = inil a0] (* helps with counting elements *)
  | S n' => fun (bt: prod ptr (btree n')) (ls: ilist (S (S n')))  => 
      match ls in ilist n0 with
       | inil _ => [False]
       | icons n0 l1 l2 => rep0' (snd bt) l1 * (Exists bt' :@ btree n', fst bt --> bt' * rep0' n' bt')
      end
 end. 

Eval simpl in rep0' 2 t2.
*)

End BINOMIAL_TREE.

(* 
*** Local Variables: ***
*** coq-prog-name: "c:/Coq/bin/coqtop.opt.exe" ***
*** coq-prog-args: ("-emacs-U" "-R" "c:/ynot/src/" "Ynot" ) ***
*** End: ***
 *)
