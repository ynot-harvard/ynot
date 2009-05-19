Require Import Ynot Basis IO.
Require Import List.
Require Import Parsers.
Require Import GradebookModel AppServer.

(* An implementation must specify the following: *)
Module Type GradebookImpl.
  Open Scope hprop_scope.
  Parameter T: Set.
  Parameter rep : forall (t: T) (m: (Config * list (ID * (list Grade)))), hprop.
  Parameter exec' : forall (t : T) (q : ParseCommand) (m : [(Config * list (ID * (list Grade)))]),
    STsep (m ~~ rep t m * [store_inv (snd m) (fst m) = true] ) 
    (fun r : Status => m ~~ [r  = fst (mutate (compileCommand (fst m) q) m)] *  
                            rep t (snd (mutate (compileCommand (fst m) q) m)) * 
                            [store_inv (snd m) (fst m) = true] ).
  Parameter init :
    STsep (__)
          (fun tm : T * [(Config * list (ID * (list Grade)))] => 
            hprop_unpack (snd tm) (fun m => rep (fst tm) m * 
              ([store_inv (snd m) (fst m) = true]))).

  Parameter cleanup : forall (t : T) (m : [(Config * list (ID * (list Grade)))]),
    STsep (m ~~ rep t m * [store_inv (snd m) (fst m) = true])
          (fun _:unit => __).

End GradebookImpl.

Module Type GradebookType.
  Definition Q : Set := ParseCommand.
  Definition RR : Set := Status.

  Definition M : Set := (Config * list (ID * (list Grade)))%type. 
  Parameter T : Set.

  Parameter rep : T -> M -> hprop.

  Parameter func : Q -> M -> (RR * M).
  Parameter AppIO : Q -> M -> RR -> M -> Trace.

  Parameter I : M -> Prop.

  Parameter func_preserves_I : forall q m, I m -> I (snd (func q m)).

  Open Local Scope hprop_scope.
  Parameter exec : forall (t : T) (q : Q) (m : [M]) (tr : [Trace]),
    STsep (tr ~~ m ~~ rep t m  * traced tr * [I m]  ) 
          (fun r : RR => tr ~~ m ~~ 
             let m' := snd (func q m)
             in  [r = fst (func q m)] * rep t m' * [I m'] *
                 traced (AppIO q m r m' ++ tr)  ).
  
  Parameter init :
    STsep (__)
          (fun tm : T * [M] => hprop_unpack (snd tm) (fun m => rep (fst tm) m * [I m])).

  Parameter cleanup : forall (t : T) (m : [M]),
    STsep (m ~~ rep t m * [I m])
          (fun _:unit => __).

End GradebookType.


(* From that, we can build a runnable app. *)
Module Gradebook (X: GradebookImpl) : GradebookType.
  Export X. 

  Definition Q : Set := ParseCommand.
  Definition M : Set := (Config * list (ID * (list Grade)))%type. 
  Definition T := T. 
  Definition RR : Set := Status.

  Definition rep := rep.

  Definition func (q: Q) (m: M) : (RR * M).
    unfold Q. unfold M. unfold RR. intros q m. exact (mutate (compileCommand (fst m) q) m). 
  Defined.
  Definition AppIO (_:Q) (_:M) (_:RR) (_:M) := (@nil Action).

  Open Scope hprop_scope.
  Open Scope stsepi_scope.

  Definition exec' := exec'.  

  Open Scope string_scope. 

  Definition I m : Prop := store_inv (snd m) (fst m) = true .

  Definition func_preserves_I : forall q m, I m -> I (snd (func q m)).
   intros. unfold I in *. unfold func. destruct m. simpl in H. unfold store_inv in *. 
   assert (store_inv1 l c = true /\ total_dec (students c) l = true).
   destruct (store_inv1 l c). destruct (total_dec (students c) l). 
   firstorder. simpl in H. discriminate.
   simpl in H. discriminate. 
   simpl.
   Ltac exhaustive solver :=
    simpl; 
    repeat (match goal with 
              | [ |- context [ if ?X then _ else _ ] ] => case_eq X
              | [ |- context [ match ?X with | Some _ => _ | None => _ end ] ] => case_eq X
              | [ |- context [ match ?X with | SetGrade _ _ _ _ _ => _ | GetGrade _ _ _ _ => _ | Average _ _ _ => _ end ] ] => case_eq X
            end; intros; simpl; try solver).
   Hint Resolve insert_preserves_inv insert_preserves_total_dec insert_preserves_noduples.
   all; each; exhaustive ltac:(auto).
 Qed.

 
 Definition exec (t : T) (q : Q) (m : [M]) (tr : [Trace]) :
   STsep (tr ~~ m ~~ rep t m  * traced tr * [I m]  ) 
         (fun r : RR => tr ~~ m ~~ 
           let m' := snd (func q m)
           in  [r = fst (func q m)] * rep t m' * [I m'] *
               traced (AppIO q m r m' ++ tr)  ).
   intros; refine ( 
     r <- exec' t q m <@> (tr ~~ traced tr) ;
     {{ Return r }}).
   solve [ sep fail auto ].
   solve [ sep fail auto ].
   solve [ sep fail auto ].
   solve [ sep fail auto; pose (i := func_preserves_I q x0); unfold I in *; sep fail auto ].
 Qed. 

Definition init := init.

Definition cleanup := cleanup.

End Gradebook.

Require Export List.
Require Export GradebookModel AppServer.