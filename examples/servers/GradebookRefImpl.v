Require Import Ynot RSep.
Require Import GradebookApp GradebookModel AppServer.

(* Reference to a logical model. *)
Module GradebookRefImpl : GradebookImpl.
  Open Scope hprop_scope.
  Open Scope stsepi_scope.

  Definition T := ptr.

  Definition rep (t: T) (m: (Config * list (ID * (list Grade)))) : hprop := ( t --> m ).

  Definition exec' : forall (t : T) (q : ParseCommand) (m : [(Config * list (ID * (list Grade)))]),
    STsep (m ~~ rep t m * [store_inv (snd m) (fst m) = true] ) 
          (fun r : Status => m ~~ [r  = fst (mutate (compileCommand (fst m) q) m)] *  rep t (snd (mutate (compileCommand (fst m) q) m)) * 
            [store_inv (snd m) (fst m) = true] ).
    intros. refine ( x <- ! t ;
                     let res := mutate (compileCommand (fst x) q) x in
                     t ::= snd res ;;
                     {{ Return (fst res) }} ); unfold rep;
    try solve [ sep fail auto | unfold res; rsep fail auto; subst; sep fail auto].
  Qed.

  Export ExampleConfig.
  Definition init :
    STsep (__)
          (fun tm : T * [(Config * list (ID * (list Grade)))] => hprop_unpack (snd tm) 
            (fun m => rep (fst tm) m * [store_inv (snd m) (fst m) = true] )).
    unfold rep; refine ( x <- New test_model ;
                         {{ Return (x, inhabits test_model) }} ); pose test_cfg_inv;
    sep fail auto. 
  Qed.

  Definition cleanup (t : T) (m : [(Config * list (ID * (list Grade)))]) :
    STsep (m ~~ rep t m * [store_inv (snd m) (fst m) = true])
          (fun _:unit => __).
    intros. refine {{Free t}}.
    unfold rep. sep fail auto.
    rsep fail auto.
  Qed.

End GradebookRefImpl. 

Module theApp : App := GradebookApp.Gradebook (GradebookRefImpl).
