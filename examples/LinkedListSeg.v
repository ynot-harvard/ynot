Require Import Ynot.
Require Import List.

Set Implicit Arguments.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Section LINKED_LIST_SEG.

Variable A : Set.

(** LLSeg : pointer to a node or none **)
Definition LinkedList : Set := option ptr.

Record Node : Set := node {
  data: A;
  next: LinkedList
}.

Definition ptr_eq : forall (p q : ptr), {p = q} + {p <> q}.
  decide equality.
Qed.

Definition ptr_eq' : forall (p q : option ptr), {p = q} + {p <> q}.
  decide equality.
  apply ptr_eq.
Qed.


Fixpoint llseg (s : LinkedList) (e : LinkedList) (m : list A) {struct m} : hprop :=
(**  if ptr_eq' s e then 
    [m = nil]
  else
**)    
  match m with
    | nil    => [s = e]
    | a :: b => match s with 
                  | None   => [False]
                  | Some p => Exists nde :@ Node, p --> nde * [a = data nde] * llseg (next nde) e b
                end
  end.

Ltac simplr := repeat (try discriminate;
  match goal with
    | [ H : next _ = _ |- _ ] => rewrite -> H
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
  end).

Ltac t := unfold llseg; sep simplr.
Ltac f := fold llseg.


Definition empty : STsep __ (fun r:LinkedList => llseg r r nil).
  refine ({{Return None}});
    t.
Qed.

Definition cons : forall (v : A) (r : LinkedList) (q : [LinkedList]) (m : [list A]),
  STsep (q ~~ m ~~ llseg r q m           )
        (fun r:LinkedList => q ~~ m ~~ llseg r q (v :: m)).
  intros;
  refine (l <- New (node v r); {{Return (Some l)}});
    t.
Qed.

Definition single : forall (v : A),
  STsep __ (fun r:LinkedList => llseg r None (v :: nil)).
  refine (fun v => {{cons v None [None] [nil]}});
    t.
Qed.

Definition freeHead : forall (p : LinkedList) (q : [LinkedList]) (b : [A]) (ls : [list A]),
  STsep (ls ~~ q ~~ b ~~ llseg p q (b :: ls))
        (fun r => ls ~~ q ~~ llseg r q ls).
  intros;
  refine (
    IfNull p Then
      {{!!!}}
    Else
      Assert (ls ~~ q ~~ b ~~ Exists nde :@ Node, p --> nde * [b = data nde] * llseg (next nde) q ls);;
      nde <- !p;
      Free p;;
      {{Return (next nde)}});
    t.
Qed.

Definition copy : forall (p' : LinkedList) (q : LinkedList) (ls' : [list A]),
  STsep (ls' ~~ llseg p' q ls')
        (fun r:LinkedList => ls' ~~ llseg p' q ls' * llseg r q ls').
  intros.
  refine (Fix2
    (fun p ls   => ls ~~ llseg p q ls)
    (fun p ls r => ls ~~ llseg p q ls * llseg r q ls)
    (fun self p ls =>
      if ptr_eq' p q then
        {{Return q}}
      else
        IfNull p Then
          {{!!!}}
        Else
          nde <- !p;
          rr <- self (next nde) (ls ~~~ tail ls) <@> (ls ~~ p --> nde * [head ls = Some (data nde)]);
          _) p' ls').
  t.
  f. hdestruct ls. t. t. f.
  

  t.
  hdestruct ls; t.
  t.