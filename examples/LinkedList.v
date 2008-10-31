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

Fixpoint rep' (p : option ptr) (m : list A) {struct m} : hprop :=
  match p with 
    | None => [m = nil]
    | Some hd => match m with
                   | a :: b => Exists nxt :@ option ptr, hd --> node a nxt * rep' nxt b
                   | nil => [False]
                 end
  end.

Definition rep (ll: LinkedList) (m : list A) : hprop :=
  Exists n :@ option ptr, ll --> n * rep' n m.

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
    | [ H : next _ = _ |- _ ] => rewrite -> H
  end).

Ltac t := unfold rep; unfold rep'; sep fail simplr.
Ltac f := fold rep'; fold rep.

Definition new : STsep __ (fun r => rep r nil).
  refine {{ New None }};
    t.
Qed.

Definition free (ll: LinkedList) :
  STsep (rep ll nil) (fun _:unit => __).
  intros; refine {{ FreeT ll :@ option ptr }};
    t.
Qed.

Definition insertFront (ll : LinkedList) (m : [list A]) (a : A) : 
  STsep (m ~~ rep ll m)
        (fun _:unit => m ~~ rep ll (a::m)).
  intros;
  refine ( x <- !ll;
    r <- New (node a x);
    {{ll ::= Some r}});
  t.
Qed.

Definition removeFront (ll: LinkedList) (m: [list A]) :
  STsep (m ~~ rep ll m)
        (fun r:option A => m ~~ match r with
                                  | None => [m = nil] * rep ll m
                                  | Some r' => Exists m' :@ list A, [m = r' :: m'] * rep ll m'
                                end).
  intros;
  refine (x <- !ll;
          IfNull x As h Then 
            {{Return None}}
          Else 
            Assert (m ~~ ll --> (Some h) * 
                    Exists nde :@ Node, Exists m' :@ list A, [m = (data nde) :: m'] * 
                    h --> nde * rep' (next nde) m');;
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
  STsep (m ~~ rep' hd m)
        (fun res:list A => m ~~ [res = m] * rep' hd m).
  refine (Fix2
    (fun hd m => m ~~ rep' hd m)
    (fun hd m o => m ~~ [o = m] * rep' hd m)
    (fun self hd m => 
      IfNull hd Then
        {{Return nil}}
      Else
        Assert (m ~~ Exists nde :@ Node, [head m = Some (data nde)] * 
          hd --> nde * rep' (next nde) (tail m));;
        fn <- !hd;
        Assert ((m ~~ [head m = Some (data fn)] * hd --> fn)
          * (m' :~~ (m ~~~ tail m) in rep' (next fn) m'));;
        rest <- self (next fn) (m ~~~ tail m) <@> _;
        {{Return (data fn :: rest)}}));
  solve [ t | hdestruct m; t ].
Qed.

Definition getElements (ll: LinkedList) (m: [list A]) :
  STsep (m ~~ rep ll m)
        (fun elts: list A => m ~~ rep ll m * [elts = m]).
  intros; refine (hd <- !ll;
    Assert (ll --> hd * (m ~~ rep' hd m));;
    {{getElements' hd m <@> _}});
  t.
Qed.

Lemma cons_nil : forall l2 x0 x, rep' l2 x0 * rep' None x ==> rep' l2 (x ++ x0).
  destruct x; t.
Qed.
Lemma node_something : forall nde p,  next nde = p -> nde = node (data nde) p.
  destruct nde; simpl; congruence.
Qed.

Hint Resolve cons_nil.
Hint Resolve node_something.

Definition append' : forall (l1 : ptr) (l2 : option ptr) (m1 m2 : [list A]),
  STsep (m1 ~~ m2 ~~ rep' (Some l1) m1 * rep' l2 m2)
        (fun _:unit => m1 ~~ m2 ~~ rep' (Some l1) (m1 ++ m2)).
  intros;
  refine (Fix2
    (fun hd m => m ~~ m2 ~~ rep' (Some hd) m * rep' l2 m2)
    (fun hd m _c => m ~~ m2 ~~ rep' (Some hd) (m ++ m2))
    (fun self hd m =>
      Assert (m ~~ Exists nde :@ Node, [head m = Some (data nde)] * 
        hd --> nde * rep' (next nde) (tail m) * (m2 ~~ rep' l2 m2));;
      nde <- !hd;
      IfNull (next nde) As p Then
        (hd ::= node (data nde) l2;;
         {{Return tt}})
      Else
        {{self p (m ~~~ tail m) <@> (hd --> nde * (m ~~ [head m = Some (data nde) /\ m <> nil]))}}) l1 m1);
  try solve [ t | hdestruct m; t ].
Qed. 

Definition append : forall (l1 l2 : LinkedList) (m1 m2 : [list A]),
  STsep ((m1 ~~ rep l1 m1) * (m2 ~~ rep l2 m2))
        (fun _:unit => m1 ~~ m2 ~~ rep l1 (m1 ++ m2) * rep l2 nil).
  intros;
  refine (hd1 <- !l1;
    hd2 <- !l2;
    l2 ::= None;;
    IfNull hd1 Then
      {{l1 ::= hd2}}
    Else
      {{append' hd1 hd2 m1 m2 <@> (l1 --> Some hd1 * l2 --> None)}}); t.
Qed.

(*
Definition insertAfter' : forall (ll: option ptr) (a c: [list A]) (b d: A),
  STsep (a ~~ c ~~ rep' ll (a ++ b :: c))
        (fun _:unit => a ~~ c ~~ rep' ll (a ++ b :: d :: c)).
  intros.
  refine (Fix2
    (fun hd a => a ~~ c ~~ rep' hd (a ++ b :: c))
    (fun hd a _ => a ~~ c ~~ rep' hd (a ++ b :: d :: c))
    (fun self hd a =>
      IfNull hd Then
        {{Return 0}}
      Else
        Assert (m ~~ Exists nde :@ Node, [head m = Some (data nde)] * 
          hd --> nde * rep' (tail m) (next nde));;
        fn <- !hd;
        Assert ((m ~~ [head m = Some (data fn)] * hd --> fn)
          * (m' :~~ (m ~~~ tail m) in rep' m' (next fn)));;
        rest <- self (next fn) (m ~~~ tail m) <@> _;
        {{Return (1 + rest)}}));
  solve [ t | hdestruct m; t ].
Qed.
        {{Return tt}}
      Else {{_}}) ll a). t. simpl. subst. t. remember (x ++ b :: x0) as H. induction (H). 
  pose app_cons_not_nil.  unfold not in n. apply n in HeqH. destruct HeqH.



  
Definition length' (hd : option ptr) (m: [list A]) :
  STsep (m ~~ rep' hd m)
        (fun res:nat => m ~~ [res = length m] * rep' hd m).


Definition length (ll: LinkedList) (m: [list A]) :
  STsep (m ~~ rep m ll)
        (fun res:nat => m ~~ rep m ll * [res = length m]).
  intros; refine (hd <- !ll;
    Assert (ll --> hd * (m ~~ rep' hd m));;
    {{length' hd m <@> _}});
  t.
Qed.

Conjecture insertAfter : forall (ll: LinkedList) (a c: [list A]) (b d: A) ,
  STsep (a ~~ c ~~ rep (a ++ b :: c) ll)
        (fun _:unit => a ~~ c ~~ rep (a ++ b :: d :: c) ll).
 

(* This is a slightly different style of remove than above. *)
Conjecture removeAfter : forall (ll: LinkedList) (a c: [list A]) (b d: A) ,
 STsep (a ~~ c ~~ rep (a ++ b :: d :: c) ll )
       (fun _:unit => a ~~ c ~~ rep (a ++ b :: c) ll ).

(* The ultimate goal is an effectful iterator *)

Definition iterCallback (a : A) (I : hprop) := STsep (I) (fun _:unit => I).

Definition foreach : forall (this : LinkedList) (f : A -> STsep) (ls : [list A]),
  STsep (ls ~~ rep ls this)
        (
**)

End LINKED_LIST.

(*
Definition SepWhile : forall I P
  (test : STsep (I) (fun r:{P} + {~P} => I)) 
  (body : STsep ([P] * I) (fun _:unit => I)),
  STsep (I) (fun _:unit => I).
  intros;
  refine (Fix (dom := unit) (ran := fun _ => unit)
              (fun _ => I)
              (fun _ _ => I)
              (fun self _ => 
                continue <- test;
                if continue then
                  body;; self tt
                else
                  {{Return tt}}) tt);
  solve [ t | destruct continue; t ].
Qed.

(**
Definition insertAfter' : forall (ll: option ptr) (a c: [list A]) (b d: A),
  STsep (a ~~ c ~~ rep' ll (a ++ b :: c))
        (fun _:unit => a ~~ c ~~ rep' ll (a ++ b :: d :: c)).
  intros.
  refine (Fix2
    (fun hd a => a ~~ c ~~ rep' hd (a ++ b :: c))
    (fun hd a _ => a ~~ c ~~ rep' hd (a ++ b :: d :: c))
    (fun self hd a =>
      IfNull hd Then
        {{Return 0}}
      Else
        Assert (m ~~ Exists nde :@ Node, [head m = Some (data nde)] * 
          hd --> nde * rep' (tail m) (next nde));;
        fn <- !hd;
        Assert ((m ~~ [head m = Some (data fn)] * hd --> fn)
          * (m' :~~ (m ~~~ tail m) in rep' m' (next fn)));;
        rest <- self (next fn) (m ~~~ tail m) <@> _;
        {{Return (1 + rest)}}));
  solve [ t | hdestruct m; t ].
Qed.
        {{Return tt}}

Definition freeAll' (hd : option ptr) (m : [list A]) : 
  STsep (m ~~ rep' hd m)
        (fun _:unit => __).
  intros.
  refine (Fix2
    (fun hd m => m ~~ rep' hd m)
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

*)