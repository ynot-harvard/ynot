Require Import List.
Require Import Ynot.

Set Implicit Arguments.

Open Local Scope hprop_scope.
Open Local Scope stsep_scope.
Open Local Scope stsepi_scope.

Section ASSOC_LIST.

Variables K V: Set.
Variable eqK : forall (k1 k2: K), {k1=k2} + {k1<>k2}.

Record Node : Set := node {
  key: K;
  value: V;
  next: option ptr
}.

(* ptr to
     (some (ptr to first node of list) | none) *)
Definition AssocList : Set := ptr.

Fixpoint rep' (m : list (prod K V)) (p : option ptr) {struct m} : hprop :=
  match p with
    | None => [m = nil]
    | Some hd => match m with
                   | (k,v) :: b => Exists nxt :@ option ptr, hd --> node k v nxt * rep' b nxt
                   | nil => [False]
                 end
  end.

Definition rep (m: list (prod K V)) (ll: AssocList) : hprop :=
  Exists n :@ option ptr, ll --> n * rep' m n.

Definition head (ls : list (prod K V)) :=
  match ls with
    | nil => None
    | x :: _ => Some x
  end.

Definition tail (ls : list (prod K V)) :=
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
    | [ |- context[ if (eqK ?v1 ?v2) then _ else _ ] ] => destruct (eqK v1 v2)
    | [ x : option _ |- _ ] => destruct x 
    | [ H : Some ?a = Some ?b |- _ ] => assert (a = b); congruence 
  end).

Ltac t := unfold rep; unfold rep'; try congruence; try subst; sep simplr.
Ltac f := fold rep'; fold rep.

Definition new : STsep __ (rep nil).
  refine {{ New None }};
    t.
Qed.

Definition free (ll: AssocList) :
  STsep (rep nil ll) (fun _:unit => __).
  intros; refine {{ FreeT ll :@ option ptr }};
    t.
Qed.

Fixpoint insert (l: list (prod K V)) (k: K) (v: V)  :=
 match l with
  | nil => (k, v)::nil
  | (k', v')::b => if eqK k k' 
                   then (k, v) :: b
                   else (k', v') :: insert b k v
 end.

Fixpoint lookup (k: K) (l: list (prod K V)) : option V :=
 match l with
  | nil => None
  | (k', v)::b => if eqK k k'
                  then Some v
                  else lookup k b
 end.

Parameter ff:False.

(* ptr to
     (some (ptr to first node of list) | none) *)

Lemma eta_node : forall fn, fn = node (key fn) (value fn) (next fn).
  destruct fn; reflexivity.
Qed.
Hint Resolve eta_node.

Lemma eta_node2 : forall fn a b, Some (a, b) = Some (key fn, value fn) -> fn = node a b (next fn).
 intros fn a b pf; assert (a = key fn); try congruence; assert (b = value fn); try congruence; subst; apply eta_node. 
Qed.
Hint Resolve eta_node2.


Definition sub1 (k: K) (v: V) (hdptr: ptr) m fn :
 STsep               ([m =  (key fn, value fn)::nil] * [next fn = None] * hdptr --> fn * [k <> key fn])
       (fun r:option V => rep' ((key fn, value fn)::(k, v)::nil) (Some hdptr)).
intros. refine ( xx <- New (node k v None);
                 hdptr ::= node (key fn) (value fn) (Some xx) ;;
        {{ Return None }});  solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ]. 
Defined.


Definition put' (k: K) (v: V) (hdptr: ptr) m :
  STsep (rep' m (Some hdptr))
        (fun r => [r = lookup k m] * rep' (insert m k v) (Some hdptr)).
intros k v. 
refine (Fix2 
    (fun hdptr m => rep' m (Some hdptr))
    (fun hdptr m r => [r = lookup k m] * rep' (insert m k v) (Some hdptr))
    (fun F hdptr m => Assert (Exists fn :@ Node, [head m = Some (key fn, value fn)] * hdptr --> fn * rep' (tail m) (next fn)) ;; 
                      fn <- !hdptr ;     
                      Assert (hdptr --> fn * [head m = Some (key fn, value fn)] * rep' (tail m) (next fn)) ;; 
                      if eqK k (key fn) 
                      then hdptr ::= node k v (next fn)  ;;
                           {{ Return Some (value fn) }} 
                      else IfNull (next fn) As nxt
                           Then xx <- New (node k v None);
                                hdptr ::= node (key fn) (value fn) (Some xx) ;; 
                                {{ Return None }}
                           Else {{ F nxt (tail m) <@> _ }} )). 
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ].
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ].
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ].
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ].
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ].
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ].
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ].
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ].
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ].
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ].
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ].
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ].
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ].
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ].
 solve [ t | repeat (destruct m; t) | destruct fn; destruct m; t; destruct m; t; t ]. t. f.
rewrite _0. t. f. destruct m. t. simpl. destruct p. destruct (eqK k k0). t. t. 
rewrite _0. t. f. destruct m. t. simpl. destruct p. destruct (eqK k k0). t. t.  rewrite <- _0.
assert (k0 = key fn). congruence. subst k0. assert (v0 = value fn). congruence. subst v0. auto.
assert (k0 = key fn). congruence. subst k0. assert (v0 = value fn). congruence. subst v0. auto.
rewrite <- _0. auto. Defined.

Definition put (k: K) (v: V) (p : ptr) (m : list (prod K V))  :
  STsep (rep m p)
        (fun r => [r = lookup k m] * rep (insert m k v) p ).
intros; refine(
   opthd <- p !! fun opthd => rep' m opthd ;
      match opthd return  STsep (p --> opthd * rep' m opthd) (fun r => [r = lookup k m] * rep (insert m k v) p)  with 
         | None => xx <- New (node k v None) ;
                   p ::= Some xx ;;
                   {{ Return None }} 
         | Some hdptr => {{ put' k v hdptr m <@> p --> Some hdptr }}
      end);  try solve [ t | repeat (destruct m; t; try (destruct m; t)) ]. Defined.

Definition get'' (k: K) (hd: option ptr) (m: [list (prod K V)]):
 STsep (m ~~ rep' m hd)
       (fun res:option V => m ~~ [res = lookup k m] * rep' m hd).
intro k.
refine (Fix2
    (fun hd m => m ~~ rep' m hd)
    (fun hd m o => m ~~ [o = lookup k m] * rep' m hd)
    (fun self hd m =>
      IfNull hd 
      Then {{ Return None }}
      Else fn <- hd !! fun fn => m ~~ [head m = Some (key fn, value fn)] * rep' (tail m) (next fn) ;
           if eqK (key fn) k  
           then {{ Return (Some (value fn)) }} 
           else {{ self (next fn) (m ~~~ tail m) <@> (m ~~ hd --> fn * [head m = Some (key fn, value fn)]) }} 
      ));  try solve [ t | repeat (hdestruct m; t) ].
Defined.

Definition get (k: K) (ll: AssocList) (m: [list (prod K V)]) :
  STsep (m ~~ rep m ll)
        (fun r:option V => m ~~ rep m ll * [r = lookup k m]).
intros; refine (hd <- !ll;
    Assert (ll --> hd * (m ~~ rep' m hd));;
    {{get'' k hd m <@> _}});
  t. Defined. 

End ASSOC_LIST.

