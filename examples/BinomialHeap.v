(* Priority Queues as Binomial Heaps *)

Require Import List.
Require Import Ynot.

Set Implicit Arguments.

Open Scope hprop_scope.
Open Local Scope stsep_scope.
Open Local Scope stsepi_scope.

Section BINOMIAL_HEAP.

Variable A:Set.
Variable a:A. (* for testing *)

(* A binomial heap is represented as a collection of binomial trees. *)

(*  A binomial tree is defined recursively:
    - a tree of order 0 is a single node
    - a tree of order k has a root node whose children are
      roots of binomial trees of orders k-1, k-2... 1, 0,
      in this order. *)

Fixpoint bltree (n: nat) : Type :=
  match n with
    | 0 => A
    | S n' => prod ptr (bltree n')
  end.

Eval simpl in bltree 2.
Definition t2 := (1, (0, a)) : bltree 2. 
Definition t3 := (2, (1, (0, a))) : bltree 3.

(* The modelling type is a binary tree. *)
Fixpoint btree (n: nat) : Type:=
  match n with
    | 0 => A
    | S n' => prod (btree n') (btree n')
  end.

Notation "'kids'" := snd.
Notation "'head'" := fst. 

Fixpoint rep' n :      btree n -> bltree n -> hprop :=
 match n   as n return btree n -> bltree n -> hprop with
  | O    => fun a a' => [a = a']
  | S n' => fun bt bl => rep' n' (kids bt) (kids bl) * 
              Exists bl' :@ bltree n', head bl --> bl' * rep' n' (head bt) bl'
 end.  

Definition rep (n: nat) (bt: btree n) (p: ptr) : hprop :=
 Exists bl :@ bltree n, p --> bl * rep' n bt bl.

Ltac t := unfold rep; unfold rep'; try match goal with 
                                     | [ h : (?a, ?b) = (?c, ?d) |- _ ] => 
                                       let y := fresh "y" in 
                                       let z := fresh "z" in 
                                         assert (a = c); try congruence; subst;  
                                         assert (b = d); try congruence; subst; clear h 
                                   end; simpl in *.
Ltac f := solve [ repeat (t; sep auto) | match goal with [n: nat |- _ ] => destruct n; repeat (t; sep auto) end].

Definition NewBl : forall hd, STsep __ (rep O hd).
 intros. refine ( {{ New hd }} ); f. Defined. 

Definition FreeBl : forall (p: ptr) (hd: [btree O]),
 STsep (hd ~~ rep 0 hd p) (fun _:unit => __).
 intros. refine ( {{ Free p }} ); f. Defined. 

(* Merging is attaching one tree as the leftmost child of the other.
   This spec, which updates in place, requires strong update, because the type
   of the node changes (it increases by one level)  
Conjecture merge : forall n p1 p2 (bt1 bt2: btree n), 
 STsep (rep n bt1 p1 * rep n bt2 p2)
       (fun r:unit => rep (S n) (bt1, bt2) p2).
 intros. refine ( oldp2node <- p2 !! (fun oldp2node:bltree n => rep n p1 bt1 * rep' n oldp2node bt2) ;
                  {{ p2 ::= (p1, oldp2node) }} ). *)
 
(* Update in place can be done by switching to a 
   bltree that returns a Set rather than a Type.
   Or just create a new pointer. *)
Definition merge' : forall p1 p2 n (bt1 bt2: [btree n]), 
 STsep ((bt1 ~~ rep n bt1 p1) * (bt2 ~~ rep n bt2 p2))
       (fun ps => bt1 ~~ bt2 ~~ Exists x :@ bltree n, 
                    p2 --> x * ps --> (p1, x) * 
                    rep' (S n)(bt1, bt2) (p1, x)   ).
intros. refine ( x <- p2 !! (fun x => (bt1 ~~ rep n bt1 p1) * (bt2 ~~ rep' n bt2 x)) ;
                 {{ New (p1, x) }} ); f. Qed. (* Maybe Qed is faster *)  

(* In these specs, n is not computationally irrelevent. *)

Definition asbtree' :       forall n        (bt: [btree n]) (bl: bltree n), STsep (bt ~~ rep' n bt bl) (fun r: btree n => bt ~~ rep' n bt bl * [r = bt]).
 refine (fix F (n: nat) {struct n} : forall (bt: [btree n]) (bl: bltree n), STsep (bt ~~ rep' n bt bl) (fun r: btree n => bt ~~ rep' n bt bl * [r = bt])   := 
            match n as n return      forall (bt: [btree n]) (bl: bltree n), STsep (bt ~~ rep' n bt bl) (fun r: btree n => bt ~~ rep' n bt bl * [r = bt])  with 
              | O    => fun bt bl => {{ SepReturn bl <@> _  }}
              | S n' => fun bt bl => x   <- head bl !! fun x:bltree n' =>       (bt ~~ rep' n' (kids bt) (kids bl)* rep' n' (head bt) x) ;     
                                     bth <- F n' (bt ~~~ head bt) x         <@> (bt ~~ head bl --> x * rep' n' (kids bt) (kids bl))  ; 
                                     btk <- F n' (bt ~~~ kids bt) (kids bl) <@> (bt ~~ head bl --> x * rep' n' (head bt) x * [bth = head bt]) ;
                                     {{ SepReturn (bth, btk) <@> (bt ~~ [(bth, btk) = bt] * rep' (S n') (bth, btk) bl) }}
            end)
; f. Qed.

Definition asbtree n (bt: [btree n]) (p: ptr) : 
  STsep (bt ~~ rep n bt p) (fun r: btree n => bt ~~ rep n bt p * [r = bt]).
 intros. refine ( x <- ! p;
                  {{ asbtree' n bt x <@> p --> x }} ); f. Qed.


(* Closing this takes minutes on my laptop *)
End BINOMIAL_HEAP.

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

Print asbtree'.
