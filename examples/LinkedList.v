Require Import List.
Require Import Ynot.

Set Implicit Arguments.  

Open Local Scope hprop_scope.
Open Local Scope stsep_scope.
Open Local Scope stsepi_scope.

Section LINKED_LIST.

Variable A: Set.

Record Node : Set := node {
  data: A;
  next: option ptr
}.

(* ptr to
     (some (ptr to first node of list) | none) *)
Definition LinkedList : Set := ptr.

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
  | a :: b => Exists p' :@ ptr, [p = Some p'] * 
              Exists tl :@ option ptr, p' --> node a tl * rep' b tl
 end.
**)

Definition rep (m: list A) (ll: LinkedList) : hprop :=
  Exists n :@ option ptr, ll --> n * rep' m n.

Definition head (ls : list A) :=
  match ls with
    | nil => None
    | x :: _ => Some x
  end.

Definition tail (ls : list A) :=
  match ls with
    | nil => nil
    | _ :: ls' => ls'
  end.

Ltac simplr := repeat (try discriminate;
  match goal with
    | [ H : head ?x = Some _ |- _ ] =>
      destruct x; simpl in *; [
        discriminate
        | injection H; clear H; intros; subst
      ]
    | [ |- match ?v with
             | Some _ => _
             | None   => _
           end ==> _] => destruct v
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H; clear H; intros; subst
  end).

Ltac t := unfold rep; unfold rep'; sep simplr.
Ltac f := fold rep'; fold rep.

Definition new : STsep __ (rep nil).
  refine {{ New None }};
    t.
Qed.

Definition free (ll: LinkedList) :
  STsep (rep nil ll) (fun _:unit => __).
  intros; refine {{ FreeT ll :@ option ptr }};
    t.
Qed.

(**
Definition freeAll' (hd : option ptr) (m : [list A]) : 
  STsep (m ~~ rep' m hd)
        (fun _:unit => __).
  intros.
  refine (Fix2
    (fun hd m => m ~~ rep' m hd)
    (fun _ _ _ => __)
    (fun self hd m =>
      IfNull hd Then
        {{Return tt}}
      Else
        Assert (m ~~ Exists nde :@ Node, [head m = Some (data nde)] * 
          hd --> nde * rep' (tail m) (next nde));;
        n <- !hd;
        self (next n) (m ~~~ tail m);;
        Free hd;;
        {{Return tt}}) hd m). t. hdestruct m0; t. hdestruct m0; t. t. t. t. t.
  
        

Definition freeAll (ll : LinkedList) : 
  STsep (Exists m :@ list A, rep m ll)
        (fun _:unit => __).
  intros.
  refine (match 
**)

Definition insertFront (ll : LinkedList) (m : [list A]) (a : A) : 
  STsep (m ~~ rep m ll)
        (fun _:unit => m ~~ rep (a::m) ll ).
  intros;
  refine ( x <- !ll;
    r <- New (node a x);
    {{ll ::= Some r}});
  t.
Qed.

Definition removeFront (ll: LinkedList) (m: [list A]) :
  STsep (m ~~ rep m ll)
        (fun r:option A => m ~~ match r with
                                  | None => [m = nil] * rep m ll
                                  | Some r' => Exists m' :@ list A, [m = r' :: m'] * rep m' ll
                                end).
  intros;
  refine (x <- !ll;
          IfNull x As h Then 
            {{Return None}}
          Else 
            Assert (m ~~ ll --> (Some h) * 
                    Exists nde :@ Node, Exists m' :@ list A, [m = (data nde) :: m'] * 
                    h --> nde * rep' m' (next nde));;
            n <- !h;
            ll ::= next n;;
            Free h;;
            {{Return (Some (data n))}});
  solve [ t | hdestruct m; t ].
Qed.

Lemma eta_node : forall fn, fn = node (data fn) (next fn).
  destruct fn; reflexivity.
Qed.

Hint Resolve eta_node.

Definition getElements' (hd : option ptr) (m: [list A]) :
  STsep (m ~~ rep' m hd)
        (fun res:list A => m ~~ [res = m] * rep' m hd).
  refine (Fix2
    (fun hd m => m ~~ rep' m hd)
    (fun hd m o => m ~~ [o = m] * rep' m hd)
    (fun self hd m => 
      IfNull hd Then
        {{Return nil}}
      Else
        Assert (m ~~ Exists nde :@ Node, [head m = Some (data nde)] * 
          hd --> nde * rep' (tail m) (next nde));;
        fn <- !hd;
        Assert ((m ~~ [head m = Some (data fn)] * hd --> fn)
          * (m' :~~ (m ~~~ tail m) in rep' m' (next fn)));;
        rest <- self (next fn) (m ~~~ tail m) <@> _;
        {{Return (data fn :: rest)}}));
  solve [ t | hdestruct m; t ].
Qed.

Definition getElements (ll: LinkedList) (m: [list A]) :
  STsep (m ~~ rep m ll)
        (fun elts: list A => m ~~ rep m ll * [elts = m]).
  intros; refine (hd <- !ll;
    Assert (ll --> hd * (m ~~ rep' m hd));;
    {{getElements' hd m <@> _}});
  t.
Qed.

Hint Resolve app_cons_not_nil.

(**
Definition insertAfter' : forall (ll: option ptr) (a c: [list A]) (b d: A),
  STsep (a ~~ c ~~ rep' (a ++ b :: c) ll)
        (fun _:unit => a ~~ c ~~ rep' (a ++ b :: d :: c) ll).
  intros.
  refine (Fix2
    (fun hd a => a ~~ c ~~ rep' (a ++ b :: c) hd)
    (fun hd a _ => a ~~ c ~~ rep' (a ++ b :: d :: c) hd)
    (fun self hd a =>
      IfNull hd Then
        {{Return tt}}
      Else {{_}}) ll a). t. simpl. subst. t. remember (x ++ b :: x0) as H. induction (H). 
  pose app_cons_not_nil.  unfold not in n. apply n in HeqH. destruct HeqH.
**)
  
  

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

End LINKED_LIST.
