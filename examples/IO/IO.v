Require Import Ynot.
Require Import List Ascii.

Set Implicit Arguments.

Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.

(* Mimic open types *)
Axiom axiom_Action : Set.
Definition Action := axiom_Action.
Definition Action_model := unit.
                                
Definition Trace := list Action.
Definition TraceModel := list Action_model.

Axiom axiom_traced : Trace -> hprop.
Definition traced := axiom_traced.
Definition traced_model (t: TraceModel) := [True]. 

Definition forever : forall (I : Trace -> hprop)
  (B : forall t', STsep (t' ~~ traced t' * I t')
        (fun t'':[Trace] => t' ~~ t'' ~~ traced (t'' ++ t') * I (t'' ++ t')))
  (t' : [Trace]), 
  STsep (t' ~~ traced t' * I t')
        (fun _:Empty_set => t' ~~ Exists t'' :@ Trace, traced (t'' ++ t') * I (t'' ++ t') * [False]).
  refine (fun I B t' =>
    Fix (fun t => t ~~ traced t * I t)
        (fun t (_:Empty_set) => t ~~ Exists t'' :@ Trace, traced (t'' ++ t) * I (t'' ++ t) * [False])
        (fun self t =>
          tr' <- B t;
          {{self (inhabit_unpack' t (fun t => inhabit_unpack tr' (fun tr' => tr' ++ t))) }}
        ) t'); 
  sep fail auto.
Qed.

Definition foreverInv : forall (CTX : Type) (ctx : CTX) (I : CTX -> Trace -> hprop)
  (B : forall ctx t', 
         STsep (t' ~~ traced t' * I ctx t')
               (fun ctx':CTX * [Trace] => t' ~~ t'' :~~ snd ctx' in traced (t'' ++ t') * I (fst ctx') (t'' ++ t')))
  (t' : [Trace]), 
  STsep (t' ~~ traced t' * I ctx t')
        (fun _:Empty_set => t' ~~ Exists t'' :@ Trace, Exists ctx' :@ CTX, traced (t'' ++ t') * I ctx' (t'' ++ t') * [False]).
  intros. refine (
    Fix2 (fun ctx t => t ~~ traced t * I ctx t)
         (fun ctx t (_:Empty_set) => t ~~ Exists t'' :@ Trace, Exists ctx' :@ CTX, traced (t'' ++ t) * I ctx' (t'' ++ t) * [False])
         (fun self ctx t =>
           ctx' <- B ctx t;
           {{self (fst ctx') (inhabit_unpack' t (fun t => inhabit_unpack (snd ctx') (fun tr' => tr' ++ t))) }}
         ) ctx t').
    solve [ sep fail auto ].
    solve [ sep fail auto ].
    sep fail auto. inhabiter. rewrite H in H1. simpl in H1. sep fail auto.
    solve [ sep fail auto ].
Qed.

(***********************************************)

(* A type of invariant preserving computations
   that make progress.  We repeat this forever
   to get a server. *)

Definition server_t (I: Trace -> Prop) (pf_startable: I nil) := forall (tr: [Trace]),
 STsep                (tr ~~ traced       tr  * [I       tr])
(fun r:[Trace] => r ~~ tr ~~ traced (r ++ tr) * [I (r ++ tr)] * [r <> nil]).


Require Export RSep.
