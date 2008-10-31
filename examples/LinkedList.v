Require Import List.
Require Import Ynot.

Set Implicit Arguments.  

Open Local Scope hprop_scope.
Open Local Scope stsep_scope.
Open Local Scope stsepi_scope.

Section LINKED_LIST.

Variable A: Set.

(******************************************************************************)
(* Representation                                                             *)
(******************************************************************************)
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

(******************************************************************************)
(* Tactics and Lemmas                                                         *)
(******************************************************************************)
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
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
  end).

Ltac t := unfold rep; unfold rep'; sep simplr.
Ltac f := fold rep'; fold rep.

Lemma eta_node : forall fn, fn = node (data fn) (next fn).
  destruct fn; reflexivity.
Qed.

Hint Resolve eta_node.

Lemma ll_concat : forall nde a b c hd, Some (data nde) = head a ->
  rep' (next nde) (tail a ++ b :: c) * hd --> nde ==> rep' (Some hd) (a ++ b :: c).
  induction a; t.
Qed.

Hint Resolve ll_concat.
Lemma cons_nil : forall l2 x0 x, rep' l2 x0 * rep' None x ==> rep' l2 (x ++ x0).
  destruct x; t.
Qed.
Lemma node_next : forall nde p,  next nde = p -> nde = node (data nde) p.
  destruct nde; simpl; congruence.
Qed.

Hint Resolve cons_nil.
Hint Resolve node_next.


(******************************************************************************)
(* Implementation                                                             *)
(******************************************************************************)
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

Definition SepPose : forall (H : hprop) (P : hprop) (pf : __ ==> P),
  STsep H (fun _:unit => H * P).
  intros.
  refine ({{Return tt}}); sep simpl.
Qed.

Notation "'Pose' P" := (SepAssert (_ * P)) (at level 75) : stsepi_scope.

(** This isn't the correct type for the function. It is possible for the equality check to succeed
 ** before the end of a. What we need is an index into the list or a proof that b is not in a.
 **)


Definition insertAfter' : forall (ll: option ptr) (eq : forall q r : A, {q = r} + {q <> r}) 
  (b d: A) (a' c: [list A]),
  STsep (a' ~~ c ~~ rep' ll (a' ++ b :: c) * [~In b a'])
        (fun _:unit => a' ~~ c ~~ rep' ll (a' ++ b :: d :: c) * [~In b a']). 
  intros;
  refine (Fix2
    (fun hd a => a ~~ c ~~ rep' hd (a ++ b :: c) * [~In b a])
    (fun hd a _ => a ~~ c ~~ rep' hd (a ++ b :: d :: c) * [~In b a])
    (fun self hd a => 
      IfNull hd Then
        {{!!!}}
      Else
        Assert (a ~~ c ~~ [~In b a] *
                  match a with 
                    | nil    => Exists nde :@ Node, hd --> nde * [b = data nde] * rep' (next nde) c
                    | v :: r => Exists nde :@ Node, hd --> nde * [v = data nde] * rep' (next nde) (r ++ b :: c)
                  end);;
        nde <- hd !! (fun nde:Node => a ~~ c ~~ [~In b a] *
                        match a with
                          | nil    => [b = data nde] * rep' (next nde) c
                          | v :: r => [v = data nde] * rep' (next nde) (r ++ b :: c)
                        end);
        if eq (data nde) b then
          Assert (a ~~ c ~~ hd --> nde * [~In b a] * [a = nil] * [b = data nde] * rep' (next nde) c);;
          n <- New (node d (next nde));
          hd ::= (node (data nde) (Some n));;
          {{Return tt}}
        else
          Assert (a ~~ c ~~ hd --> nde * [a <> nil] * [Some (data nde) = head a] * [~In b a] * rep' (next nde) (tail a ++ b :: c));;
          {{self (next nde) (a ~~~ tail a) <@> (a ~~ hd --> nde * [Some (data nde) = head a] * [a <> nil])}}) ll a');
  solve [ t | hdestruct a; t ].
Qed.

Definition insertAfter : forall (ll: LinkedList) (eq : forall q r : A, {q = r} + {q <> r})
  (a c: [list A]) (b d: A),
  STsep (a ~~ c ~~ rep ll (a ++ b :: c) * [~In b a])
        (fun _:unit => a ~~ c ~~ rep ll (a ++ b :: d :: c) * [~In b a]).
  intros;
  refine (hd <- !ll; {{insertAfter' hd eq b d a c <@> (ll --> hd)}});
    t.
Qed.

Definition insertAt' : forall (hd' : option ptr) (m' : [list A]) (pos' : nat) (v : A),
  STsep (m' ~~ rep' hd' m' * [pos' <= length m'])
        (fun _:unit => m' ~~ Exists a :@ list A, Exists b :@ list A, [m' = a ++ b] * [length a = pos'] * rep' hd' (a ++ v :: b)). 
  intros.
  refine (Fix3
    (fun hd m pos =>   m ~~ rep' hd m * [pos <= length m])
    (fun hd m pos (_:unit) => m ~~ Exists a :@ list A, Exists b :@ list A, [m = a ++ b] * [length a = pos] * rep' hd (a ++ v :: b))
    (fun self hd a => 
      IfNull hd Then
        _
      Else
        _) hd' m' pos').
        Assert (a ~~ c ~~ [~In b a] *
                  match a with 
                    | nil    => Exists nde :@ Node, hd --> nde * [b = data nde] * rep' (next nde) c
                    | v :: r => Exists nde :@ Node, hd --> nde * [v = data nde] * rep' (next nde) (r ++ b :: c)
                  end);;
        nde <- hd !! (fun nde:Node => a ~~ c ~~ [~In b a] *
                        match a with
                          | nil    => [b = data nde] * rep' (next nde) c
                          | v :: r => [v = data nde] * rep' (next nde) (r ++ b :: c)
                        end);
        if eq (data nde) b then
          Assert (a ~~ c ~~ hd --> nde * [~In b a] * [a = nil] * [b = data nde] * rep' (next nde) c);;
          n <- New (node d (next nde));
          hd ::= (node (data nde) (Some n));;
          {{Return tt}}
        else
          Assert (a ~~ c ~~ hd --> nde * [a <> nil] * [Some (data nde) = head a] * [~In b a] * rep' (next nde) (tail a ++ b :: c));;
          {{self (next nde) (a ~~~ tail a) <@> (a

Definition insertAt : forall (ll : LinkedList) (m : [list A]) (pos : nat) (v : A),
  STsep (m ~~ rep ll m * [pos <= length m])
        (fun _:unit => m ~~ Exists a :@ list A, Exists b :@ list A, [m = a ++ b] * [length a = pos] * rep ll (a ++ v :: b)). 
  intros.



Definition filter : forall (ll : LinkedList) (m : [list A]) (I : hprop) (pred : A -> bool),
  STsep (m ~~ rep ll m)
        (fun _:unit => m ~~ 

Definition removeAfter' : forall (hd': option ptr) (eq : forall q r : A, {q = r} + {q <> r})
  (a' c: [list A]) (b d: A),
  STsep (a' ~~ c ~~ rep' hd' (a' ++ b :: d :: c) * [~In b a'])
        (fun _:unit => a' ~~ c ~~ rep' hd' (a' ++ b :: c) * [~In b a']).
  intros.
  refine (Fix2
    (fun hd a => a ~~ c ~~ rep' hd (a ++ b :: d :: c) * [~In b a])
    (fun hd a _ => a ~~ c ~~ rep' hd (a ++ b :: c) * [~In b a])
    (fun self hd a => 
      IfNull hd Then
        {{!!!}}
      Else
        Assert (a ~~ c ~~ [~In b a] *
                  match a with 
                    | nil    => Exists nde :@ Node, hd --> nde * [b = data nde] * rep' (next nde) (d :: c)
                    | v :: r => Exists nde :@ Node, hd --> nde * [v = data nde] * rep' (next nde) (r ++ b :: d :: c)
                  end);;
        nde <- hd !! (fun nde:Node => a ~~ c ~~ [~In b a] *
                        match a with
                          | nil    => [b = data nde] * rep' (next nde) (d :: c)
                          | v :: r => [v = data nde] * rep' (next nde) (r ++ b :: d :: c)
                        end);
        if eq (data nde) b then
          Assert (a ~~ c ~~ hd --> nde * [~In b a] * [a = nil] * [b = data nde] * rep' (next nde) (d :: c));;
          
          hd ::= (node (data nde) (next nde));;
          {{Return tt}}
        else
          Assert (a ~~ c ~~ hd --> nde * [a <> nil] * [Some (data nde) = head a] * [~In b a] * rep' (next nde) (tail a ++ b :: c));;
          {{self (next nde) (a ~~~ tail a) <@> (a ~~ hd --> nde * [Some (data nde) = head a] * [a <> nil])}}) hd' a').
  hdestruct a; t.
  t.
  hdestruct a; t.
  t.
  hdestruct a; t.
  t.
  hdestruct a. t.f.



Definition removeAfter : forall (ll: LinkedList) (eq : forall q r : A, {q = r} + {q <> r})
  (a c: [list A]) (b d: A),
  STsep (a ~~ c ~~ rep ll (a ++ b :: d :: c) * [~In b a])
        (fun _:unit => a ~~ c ~~ rep ll (a ++ b :: c) * [~In b a]).
  intros;
  refine (hd <- !ll; {{removeAfter' hd eq a c b d <@> (ll --> hd)}}); t.
Qed.
  


  
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

