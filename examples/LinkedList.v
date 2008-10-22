Require Import List.
Require Import Ynot.

Set Implicit Arguments.  


Open Scope hprop_scope. 
Open Scope stsep_scope.
Open Scope stsepi_scope.

Section LINKED_LIST.

Variable A: Set.

(* I'm taking these definitions from wikipedia. *)
Record Node : Set := node {
  data: A;         (* data being stored in the node *)
  next: option ptr (* a reference to the next node, none for last node *)
}.

(* ptr to
     (some (ptr to first node of list) | none) *)
Definition LinkedList : Set := ptr.



Fixpoint rep' (m: list A) (p: option ptr) {struct m} : hprop :=
 match m with
  | nil => [p = None]
  | a :: b => match p with
                | None => [False]
                | Some hd => Exists nxt :@ option ptr, hd --> node a nxt * rep' b nxt
              end
 end.  


Definition rep (m: list A) (ll: LinkedList) : hprop :=
 Exists n :@ option ptr, ll --> n * rep' m n.

Definition new : STsep __ (rep nil).
refine ( {{ New None }} ); unfold rep; sep auto.  
Defined.

Definition free (ll: LinkedList) :
 STsep (rep nil ll) (fun _:unit => __).
intros ll; refine ( {{ FreeT ll :@ option ptr }} ); unfold rep; sep auto.
Defined.  

(* Our ultimate goal is
 Definition insertFront01 (ll: LinkedList) (m: list A) (a: A) :
 STsep (rep m ll)
       (fun _:unit => rep (a::m) ll ).

There are three computations that are bound together: 

 x <- SepRead ll;       -- 0A
 r <- New (node a x);   -- AB
 ll := Some r           -- B1

0A and AB around bound to create 0B, which is bound with B1
to create 01.  A B stand for the intermediate heap specs 
and 0 for the overall insert front spec. Since monads are
associative, we could also create A1 instead.
*)

Ltac t := unfold rep; unfold rep'; sep auto; fold rep'; fold rep.

Definition insertFront (ll : LinkedList) (m : [list A]) (a : A) : 
  STsep (m ~~ rep m ll)
        (fun _:unit => m ~~ rep (a::m) ll ).
  intros ll m a.
  refine ( x <- !ll (** !! (fun x => m ~~ rep' m x) **)
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

Definition insertFrontAB (ll: LinkedList) (m: [list A]) (a: A) (x: option ptr)  :
 STsep (m ~~ ll --> x * rep' m x )
       (fun r:ptr => m ~~ ll --> x * rep' m x * r --> node a x).
intros ll m a x. refine (
 {{ New (node a x) }} ); unfold rep; sep auto. Defined.

Definition insertFrontB1 (ll: LinkedList) (m: [list A]) (a: A) (r: ptr) :
 STsep (m ~~ Exists x :@ option ptr, ll --> x * rep' m x * r --> node a x)
       (fun _:unit => m ~~ rep (a::m) ll ).
 intros ll m a r. 
 refine ( {{ ll ::= Some r }} ); unfold rep; sep auto. Defined. 

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

Axiom todo : forall A, A.

Definition removeFront: forall (ll: LinkedList) (m: [list A]) ,
 STsep (m ~~ rep m ll)
       (fun r:option A => m ~~ match r with
                                 | None => [m = nil] * rep m ll
                                 | Some r' => Exists m' :@ list A, [m = r' :: m'] * rep m' ll
                               end).
  intros ll m.
  refine ( x <- ll !! (fun x => m ~~ rep' m x) (** read ll and bind result to x **)
         ; IfNull x As h Then
             {{Return None}}
           Else
             (** HERE I KNOW THAT x = Some h **)
               n <- !h(** !! (fun n => m ~~ match m with 
                                         | nil => [False]
                                         | _ :: t => ll --> (Some h) * rep' t (next n)
                                       end) **)
             ; ll ::= next n (** <@> (m ~~ rep' m (Some h)) **)
             ;; Free h
             ;; {{Return (Some (data n))}}
         ); try solve [ t | hdestruct m; t ]. t. unfold rep'.


try solve [ t | hdestruct m; t ]; t.


unfold rep'. destruct x0. t.
         ; {{match x as x return STsep (ll --> x * (m ~~ rep' m x))
                                     (fun (r:option A) =>  m ~~ match r with
                                                                  | None => [m = nil]  * ll --> None
                                                                  | Some r' => ll --> Some r' * 
                                                                    match m with
                                                                      | nil => [False]
                                                                      | a :: b => [r' = a] * rep' b x
                                                                    end
                                                                end) with
             | None => {{Return None}}
             | Some r' => (** I need to know that l --> Some r' **)
             
           end}}); t. 


 destruct x0. simpl. sep auto. discriminate. sep auto.  inversion H0. subst. sep auto. Show Existentials.




t. change (

    ll --> x *
    hprop_unpack m
      (fun m0 : list A =>
       (fix rep' (m1 : list A) (p : option ptr) {struct m1} : hprop :=
          match m1 with
          | nil => [p = None]
          | a :: b =>
              Exists p' :@ ptr,
              [p = Some p'] *
              (Exists tl :@ option ptr, p' --> node a tl * rep' b tl)
          end) m0 x) ==>
   (Exists v :@ Node,
    r' --> v *
    hprop_unpack m
      (fun m0 : list A =>
       match m0 with
       | nil => [False]
       | _ :: t => ll --> x * rep' t (next v)
       end))). t. destruct x0. simpl.


; t. destruct x0. sep auto.

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
