(*

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

*)