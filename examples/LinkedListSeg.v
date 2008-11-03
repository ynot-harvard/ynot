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
  decide equality; apply ptr_eq.
Qed.

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

Fixpoint llseg (s : LinkedList) (e : LinkedList) (m : list A) {struct m} : hprop :=
  match m with 
    | nil => [s = e]
    | v :: r => [s <> e] * match s with
                             | None => [False]
                             | Some p => Exists nde :@ Node, p --> nde * [v = data nde] * llseg (next nde) e r
                           end
  end.

Definition llist (s : LinkedList) (m : list A) : hprop :=
  llseg s None m.

Ltac simplr := repeat (try discriminate;
  match goal with
    | [ H : next _ = _ |- _ ] => rewrite -> H
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
    | [ |- context[ptr_eq' ?X ?Y] ] => destruct (ptr_eq' X Y)
    | [ |- context[llseg None None ?L] ] => destruct L
  end).

Ltac t := unfold llist; unfold llseg; sep simplr.
Ltac f := fold llseg; fold llist.

Definition empty : STsep __ (fun r:LinkedList => llseg r r nil).
  refine ({{Return None}});
    t. 
Qed.

Definition cons : forall (v : A) (r : LinkedList) (q : [LinkedList]) (m : [list A]),
  STsep (q ~~ m ~~ llseg r q m)
        (fun r:LinkedList => q ~~ m ~~ llseg r q (v :: m)).
  intros;
  refine (l <- New (node v r); {{Return (Some l)}}).
Admitted.

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
          Assert (ls ~~ Exists nde :@ Node, [Some p <> q] * p --> nde * [head ls = Some (data nde)] * llseg (next nde) q (tail ls));;
          nde <- !p;
          rr <- self (next nde) (ls ~~~ tail ls) <@> (ls ~~ p --> nde * [head ls = Some (data nde)]);
          res <- cons (data nde) rr [q] (ls ~~~ tail ls) <@> (ls ~~ [Some p <> q] * p --> nde * [head ls = Some (data nde)] * llseg (next nde) q (tail ls));
          {{Return res}}) p' ls');
  solve [ t | hdestruct ls; t ].
Qed.

Definition append : forall (p' : LinkedList) (q : LinkedList)
  (lsp' lsq : [list A]), 
  STsep (lsp' ~~ lsq ~~ llist p' lsp' * llist q lsq)
        (fun r:LinkedList => lsp' ~~ lsq ~~ llist r (lsp' ++ lsq)).
  intros.
  refine (Fix2 
    (fun p lsp   => lsp ~~ lsq ~~ llist p lsp * llist q lsq)
    (fun p lsp r => lsp ~~ lsq ~~ llist r (lsp ++ lsq))
    (fun self p lsp =>
      IfNull p Then 
        {{Return q}}
      Else
        Assert (lsp ~~ lsq ~~ Exists nde :@ Node, p --> nde * [head lsp = Some (data nde)] * llist (next nde) (tail lsp) * llist q lsq);;
        nde <- !p;
        IfNull next nde As p' Then
          p ::= node (data nde) q;;
          {{Return (Some p)}}
        Else
          _
    ) p' lsp').
  t.
  hdestruct lsp; t.
  hdestruct lsp; t.
  t.
  t.
  t.
  t.
  t.
  t.
  f. hdestruct lsp. t. f.t. f.

  Lemma seg_none_none : forall (l : list A), llseg None None l ==> [l = nil].
    destruct l; t.
  Qed.
  destruct lsp; t.