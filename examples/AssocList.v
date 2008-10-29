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
  end).

Ltac t := unfold rep; unfold rep'; sep simplr.
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

Definition put (ll : AssocList) (m : [list (prod K V)]) (k : K) (v : V) :
  STsep (m ~~ rep m ll)
        (fun _:unit => m ~~ rep ((k,v)::m) ll ).
  intros;
  refine ( x <- !ll;
    r <- New (node k v x);
    {{ll ::= Some r}});
  t.
Qed.

Fixpoint lookup (k: K) (l: list (prod K V)) : option V :=
 match l with
  | nil => None
  | (k', v)::b => if eqK k k'
                  then Some v
                  else lookup k b
 end.

Lemma eta_node : forall fn, fn = node (key fn) (value fn) (next fn).
  destruct fn; reflexivity.
Qed.
Hint Resolve eta_node.

Lemma eta_node2 : forall fn a b, Some (a, b) = Some (key fn, value fn) -> fn = node a b (next fn).
 intros fn a b pf; assert (a = key fn); try congruence; assert (b = value fn); try congruence; subst; apply eta_node. 
Qed.
Hint Resolve eta_node2.

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
      )); try solve [ t | hdestruct m; t ]. 
Defined.

End ASSOC_LIST.