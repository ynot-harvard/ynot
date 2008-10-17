<<<<<<< local
=======

>>>>>>> other

Require Import List.
Require Import Ynot.

<<<<<<< local
Set Implicit Arguments.  
=======
Set Implicit Arguments.
>>>>>>> other

<<<<<<< local
Open Scope hprop_scope. 
Open Scope stsep_scope.
Open Scope stsepi_scope.
=======
Module Type LIST.
  Variable value_t : Set.
End LIST.
>>>>>>> other

<<<<<<< local
Section LINKED_LIST.
=======
>>>>>>> other

<<<<<<< local
Variable A: Set.
=======
(*********************************************)
(* The functional model -- linked lists      *)
(*********************************************)
Module LinkedList(L : LIST).
>>>>>>> other

<<<<<<< local
(* I'm taking these definitions from wikipedia. *)
Record Node : Set := node {
  data: A;         (* data being stored in the node *)
  next: option ptr (* a reference to the next node, none for last node *)
}.
=======
  Definition list_t := list L.value_t.
>>>>>>> other

<<<<<<< local
(* ptr to
     (some (ptr to first node of list) | none) *)
Definition LinkedList : Set := ptr.
=======
  Definition tail(l : list_t) : list_t :=
    match l with
      | nil => nil
      | _ :: l => l
    end.
      
>>>>>>> other

<<<<<<< local
Fixpoint rep' (m: list A) (p: option ptr) {struct m} : hprop :=
 match m with
  | nil => [p = None]
  | a :: b => Exists p' :@ ptr, [p = Some p'] * 
              Exists tl :@ option ptr, p' --> node a tl * rep' b tl
 end.  
=======
End LinkedList.
>>>>>>> other

<<<<<<< local
Definition rep (m: list A) (ll: LinkedList) : hprop :=
 Exists n :@ option ptr, ll --> n * rep' m n.
=======
(*********************************************)
(* The interface -- linked lists             *)
(*********************************************)
>>>>>>> other

<<<<<<< local
Definition new : STsep __ (rep nil).
refine ( {{ New None }} ); unfold rep; sep auto.  
Defined.
=======
>>>>>>> other

<<<<<<< local
Definition free (ll: LinkedList) :
 STsep (rep nil ll) (fun _:unit => __).
intros ll; refine ( {{ FreeT ll :@ option ptr }} ); unfold rep; sep auto.
Defined.  
=======
(***************************************************)
(* The implementation -- encapsulated linked lists *)
(***************************************************)
Module RefLinkedList(List:LIST).
  Module L  := List.
  Module LL := LinkedList(L).
>>>>>>> other

<<<<<<< local
(* Our ultimate goal is
 Definition insertFront01 (ll: LinkedList) (m: list A) (a: A) :
 STsep (rep m ll)
       (fun _:unit => rep (a::m) ll ).
=======
  Definition llist_t := ptr.
>>>>>>> other

<<<<<<< local
There are three computations that are bound together: 
=======
  Open Local Scope stsep_scope.
  Open Local Scope hprop_scope.
>>>>>>> other

<<<<<<< local
 x <- SepRead ll;       -- 0A
 r <- New (node a x);   -- AB
 ll := Some r           -- B1
=======
  Definition rep (l : llist_t) (l' : LL.list_t) : hprop  := (l --> l').
>>>>>>> other

<<<<<<< local
0A and AB around bound to create 0B, which is bound with B1
to create 01.  A B stand for the intermediate heap specs 
and 0 for the overall insert front spec. Since monads are
associative, we could also create A1 instead.
*)
=======
  (** new :: () -> LinkedList T
   ** Create a new linked list.
   **)
  Definition new : STsep __ (fun (ans:llist_t) => rep ans nil) :=
    New nil.
>>>>>>> other

<<<<<<< local
Ltac t := unfold rep; unfold rep'; sep auto.
=======
  (** free :: LinkedList T -> ()
   ** Delete the linked list.
   **)
  Definition free(this : llist_t) :
      STsep (Exists l :@ LL.list_t, rep this l) (fun (_:unit) => __) :=
    FreeT this :@ LL.list_t.
>>>>>>> other

<<<<<<< local
=======
  (** cons :: LinkedList T -> T -> ?? -> ()
   ** Add an element to the beginning of the list.
   **)
  Definition cons(this : llist_t) (v : L.value_t) (P : LL.list_t -> hprop) :
      STsep (Exists l :@ LL.list_t, rep this l * P l) 
            (fun (_:unit) => Exists l :@ LL.list_t, rep this (v :: l) * P l).
    intros.
    refine (l <- this !! P ;
            this ::= (v :: l) <@> (P l) @> _); sep auto.
    Defined.
>>>>>>> other

<<<<<<< local
Definition insertFront (ll : LinkedList) (m : [list A]) (a : A) : 
  STsep (m ~~ rep m ll)
        (fun _:unit => m ~~ rep (a::m) ll ).
  intros ll m a.
  refine ( x <- ll !! (fun x => m ~~ rep' m x)
         ; r <- New (node a x)
         ; {{ll ::= Some r}}); t.
Defined.
(**
Definition insertFront0A (ll: LinkedList) (m: [list A]) (a: A) :
 STsep (m ~~ rep m ll)
       (fun x:option ptr => m ~~ ll --> x * rep' m x ).
intros ll m _. refine (
 {{ SepRead ll (fun x:option ptr => m ~~ rep' m x) }} ); unfold rep; sep auto. 
Defined.
=======
  (** tail :: LinkedList T -> ?? -> ()
   ** Remove the first element in the list.
   **)
  Definition tail(this : llist_t) (P : LL.list_t -> hprop) :
    STsep (Exists l :@ LL.list_t, rep this l * P l)
          (fun (_:unit) => Exists l :@ LL.list_t, rep this (LL.tail l) * P l).
    intros;
    refine (l <- this !! P ;
            this ::= LL.tail l <@> (P l) @> _); sep auto.
    Defined.
>>>>>>> other

<<<<<<< local
Definition insertFrontAB (ll: LinkedList) (m: [list A]) (a: A) (x: option ptr)  :
 STsep (m ~~ ll --> x * rep' m x )
       (fun r:ptr => m ~~ ll --> x * rep' m x * r --> node a x).
intros ll m a x. refine (
 {{ New (node a x) }} ); unfold rep; sep auto. Defined.
=======
End RefLinkedList.
>>>>>>> other

<<<<<<< local
Definition insertFrontB1 (ll: LinkedList) (m: [list A]) (a: A) (r: ptr) :
 STsep (m ~~ Exists x :@ option ptr, ll --> x * rep' m x * r --> node a x)
       (fun _:unit => m ~~ rep (a::m) ll ).
 intros ll m a r. 
 refine ( {{ ll ::= Some r }} ); unfold rep; sep auto. Defined. 
=======
>>>>>>> other

<<<<<<< local
Definition insertFront0B (ll: LinkedList) (m: [list A]) (a: A) :
 STsep (m ~~ rep m ll) (fun r:ptr => m ~~ Exists x :@ option ptr, ll --> x * rep' m x * r --> node a x).
 intros ll m a. refine (
 x <- insertFront0A ll m a;
 {{ insertFrontAB ll m a x }} ); sep auto. Defined.

Definition insertFront01 (ll: LinkedList) (m: [list A]) (a: A) :
 STsep (m ~~ rep m ll)
       (fun _:unit => m ~~ rep (a::m) ll ).
intros ll m a. refine (
 r <- insertFront0B ll m a;
 {{ insertFrontB1 ll m a r }} ); unfold rep; sep auto. Defined.
**)

(*  With just insertFront and removeFront, a 
   linked list implements a stack. *)
Definition removeFront: forall (ll: LinkedList) (m: list A) ,
 STsep (rep m ll)
       (fun r:option A => match r with
                                 | None => [m = nil] 
                                 | Some r' => match m with
                                                | nil => [False]
                                                | a :: b => [r' = a]
                                              end
                               end).
  intros ll m.
  refine ( x <- ll !! (fun x => rep' m x)
         ; match x as x with 
             | None => {{Return None}}
             | Some r' =>
               n <- r' !! (fun n => match m with 
                                      | nil => [False]
                                      | _ :: t => ll --> x * rep' t (next n)
                                    end)
               ; z <- ll ::= next n
               ; {{Return (Some (data n))}}
           end); t. fold rep'. 


(* With computing the elements in the linked list,
   and add and remove after elements, we have 
   a random access list. *)
Conjecture getElements : forall (ll: LinkedList) (m: [list A]) ,
 STsep (m ~~ rep m ll)
       (fun elts: list A => m ~~ rep m ll * [elts = m]).

Conjecture insertAfter : forall (ll: LinkedList) (a c: [list A]) (b d: A) ,
 STsep (a ~~ c ~~ rep (a ++ b :: c) ll)
       (fun _:unit => a ~~ c ~~ rep (a ++ b :: d :: c) ll).

(* This is a slightly different style of remove than above. *)
Conjecture removeAfter : forall (ll: LinkedList) (a c: [list A]) (b d: A) ,
 STsep (a ~~ c ~~ rep (a ++ b :: d :: c) ll )
       (fun _:unit => a ~~ c ~~ rep (a ++ b :: c) ll ).

(* The ultimate goal is an effectful iterator *)
=======
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-R" "../src" "Ynot" "-R" "/Users/greg/Devel/ynot/coq/adam/examples" "Examples") ***
*** End: ***
*).>>>>>>> other
