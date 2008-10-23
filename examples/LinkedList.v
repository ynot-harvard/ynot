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
Definition null : option ptr := None.

Fixpoint rep' (m : list A) (p : option ptr) {struct m} : hprop :=
  match p with 
    | None => [m = nil]
    | Some hd => match m with
                   | a :: b => Exists nxt :@ option ptr, hd --> node a nxt * rep' b nxt
                   | nil => [False]
                 end
  end.

(**
Fixpoint rep' (m: list A) (p: option ptr) {struct m} : hprop :=
 match m with
  | nil => [p = None]
  | a :: b => match p with
                | None => [False]
                | Some hd => Exists nxt :@ option ptr, hd --> node a nxt * rep' b nxt
              end
 end.
**)  


Definition rep (m: list A) (ll: LinkedList) : hprop :=
 Exists n :@ option ptr, ll --> n * rep' m n.

Ltac t := unfold rep; unfold rep'; sep auto.
Ltac f := fold rep'; fold rep.

Definition new : STsep __ (rep nil).
refine ( {{ New None }} ); unfold rep; sep auto.  
Defined.

Definition free (ll: LinkedList) :
 STsep (rep nil ll) (fun _:unit => __).
intros ll; refine ( {{ FreeT ll :@ option ptr }} ); solve [ t | t; destruct v; t ].
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
  refine ( x <- ll !! (fun x => m ~~ rep' m x) (** read ll and bind result to x **); _ ).
    t. 
    t.
  refine (IfNull x As h Then _
          Else _).
  refine ({{Return None}}). t. hdestruct m; t.

  fold rep'.
  refine (Assert (m ~~ ll --> (Some h) * Exists nde :@ Node, Exists m' :@ list A, [m = (data nde) :: m'] * h --> nde * rep' m' (next nde));; _).
    subst. hdestruct m. t. t.
    intros. instantiate (1 := hprop_unpack m
     (fun m0 : list A =>
      ll --> Some h *
      (Exists nde :@ Node,
       (Exists m' :@ list A,
        [m0 = data nde :: m'] * h --> nde * rep' m' (next nde))))). t.

  refine (n <- h !! (fun n : Node => ll --> Some h *
    (m ~~ Exists m' :@ list A,
      [m = data n :: m'] * rep' m' (next n))); _). t. t.

  refine (ll ::= next n;; _). t. t.

  refine (Free h;; _). t. t.

  refine ({{Return (Some (data n))}}). t. t.
Defined.

Definition removeFront': forall (ll: LinkedList) (m: [list A]) ,
 STsep (m ~~ rep m ll)
       (fun r:option A => m ~~ match r with
                                 | None => [m = nil] * rep m ll
                                 | Some r' => Exists m' :@ list A, [m = r' :: m'] * rep m' ll
                               end).
  intros ll m.
  refine (x <- !ll (** !! (fun x => m ~~ rep' m x) **); 
          IfNull x As h
          Then {{Return None}}
          Else (Assert (m ~~ ll --> (Some h) * Exists nde :@ Node, Exists m' :@ list A, [m = (data nde) :: m'] * h --> nde * rep' m' (next nde));;
                n <- !h (** !! (fun n : Node => 
                             ll --> Some h * (m ~~ Exists m' :@ list A, [m = data n :: m'] * rep' m' (next n))) **);
                ll ::= next n;;
                Free h;;
                {{Return (Some (data n))}})); solve [ t | hdestruct m; t].
Defined.

(* With computing the elements in the linked list,
   and add and remove after elements, we have 
   a random access list. *)
Definition getElements' (hd : option ptr) (m: [list A]) :
 STsep (m ~~ rep' m hd)
       (fun res:list A => m ~~ [res = m] * rep' m hd).
 refine ((fix getElements'' (hd : option ptr) (m: [list A]) {struct m} :
            STsep (m ~~ rep' m hd)
                  (fun res:list A => m ~~ [res = m] * rep' m hd) :=
            IfNull hd As p Then
              {{Return nil}}
            Else 
              n <- p !! (fun n : Node => m ~~ Exists m' :@ list A, [m = (data n) :: m'] * rep' m' (next n)); 
              rest <- getElements'' (next n) _ <@> (p --> n); _)); 

try solve [ t | hdestruct m; t ]. 
  (** How do I get the ghost list corresponding to the tail in order to pass it to the call? **)
    
             
              
t. hdestruct 



              rest <- getElements'' (next n) _; _) hd _); try solve [ t | hdestruct m t | hdestruct m0; t ]. 


 subst. 


              {{Return ((data n) :: rest)}}) hd _); try solve [ t | hdestruct m; t | hdestruct m0; t ].

   t.



Definition getElements : forall (ll: LinkedList) (m: [list A]) ,
 STsep (m ~~ rep m ll)
       (fun elts: list A => m ~~ rep m ll * [elts = m]).
 intros ll m.
 

Conjecture insertAfter : forall (ll: LinkedList) (a c: [list A]) (b d: A) ,
 STsep (a ~~ c ~~ rep (a ++ b :: c) ll)
       (fun _:unit => a ~~ c ~~ rep (a ++ b :: d :: c) ll).

(* This is a slightly different style of remove than above. *)
Conjecture removeAfter : forall (ll: LinkedList) (a c: [list A]) (b d: A) ,
 STsep (a ~~ c ~~ rep (a ++ b :: d :: c) ll )
       (fun _:unit => a ~~ c ~~ rep (a ++ b :: c) ll ).

(* The ultimate goal is an effectful iterator *)
(**
Definition iterCallback (a : A) (I : hprop) := STsep (I) (fun _:unit => I).

Definition iterate : forall (this : LinkedList) (f : A -> STsep) (ls : [list A]),
  STsep (ls ~~ rep ls this)
        (
**)