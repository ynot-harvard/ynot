Require Import GradebookModel. (* change this module name or move to here *)
Require Import List.

Set Implicit Arguments.

Module Config.
  (* privacy respecting queries can probably stay the same *)
  Definition P (cfg: Config) (q: Command) := True.
  (* likewise with correct queries *)
  Definition E (cfg: Config) (q: Command) := True. 
  (* todo add definition of privacy and wellformedness of q *)
  Parameter P_dec : forall cfg q, {P cfg q} + {~P cfg q}. (* privacy *)
  Parameter E_dec : forall cfg q, {E cfg q} + {~E cfg q}. (* valid query *)
End Config.

Module Type Model.
  Export Config.
  Parameter M : Type.
  Parameter I : Config -> M -> Prop.
  Parameter mutate : forall (cfg: Config) (q: Command) (m: M), (Status * M).
  Parameter pres_I : forall cfg q m,
    I cfg (snd (mutate cfg q m)).
End Model.

Require Import Ynot.
Module Type Impl (X: Model).
 Export X.
  Parameter T: Set.
  Parameter rep : forall (t: T) (m: M), hprop.

  Open Local Scope hprop_scope.
  Parameter imp_mutate : forall cfg t q (m: [M]),
    STsep (m ~~ rep t m * [I cfg m] * [P cfg q] * [E cfg q]) 
          (fun r : Status => m ~~ let (r', m') := (mutate cfg q m)
                                  in  [r' = r] * rep t m'). 
End Impl.
 
(* our spec is a distinguished model *) 
Module Spec : Model.
 Export Config.
   Definition  M := ID -> Assignment -> option Grade. 
   
   Definition  I : Config -> M -> Prop. 
   Admitted.
  
  Parameter mutate : forall (cfg: Config) (q: Command) (m: M), (Status * M).

    Theorem pres_I : forall cfg q m,
    I cfg (snd (mutate cfg q m)).
    Admitted.
End Spec.

(* The model of the imperative implementation *)
Module TupleModel : Model.
 Export Config.
   Definition  M := ID -> Assignment -> option Grade. 
   
   Definition  I : Config -> M -> Prop. 
   Admitted.
  
  Parameter mutate : forall (cfg: Config) (q: Command) (m: M), (Status * M).

    Theorem pres_I : forall cfg q m,
    I cfg (snd (mutate cfg q m)).
    Admitted.
End TupleModel.

(* equivalences of models *)
Module Type ModelIso.
  Export Config.
  Declare Module S : Model.
  Declare Module T : Model.

  Parameter f : forall cfg, sigT (S.I cfg) -> sigT (T.I cfg).
  Parameter g : forall cfg, sigT (T.I cfg) -> sigT (S.I cfg).

  (* we probably don't want 
  Parameter Correct : forall cfg t, f (cfg:=cfg)(g t) = t. *)
  
  Parameter Correct : forall cfg t, 
   projT1 (f (g (cfg:=cfg) t)) = projT1 t. 
End ModelIso.

Module CorrectRefl (X: Model) : ModelIso with Module S := X 
                                         with Module T := X.
  Export Config.
  Module S := X.
  Module T := X.

  Definition f cfg (x: sigT (S.I cfg)) := x.
  Definition g cfg (y: sigT (T.I cfg)) := y. 

  Theorem Correct : forall cfg t, 
   projT1 (f (g (cfg:=cfg) t)) = projT1 t. 
  Proof.
    compute. intros. eauto. Qed.
End CorrectRefl.

(* todo the isomorphism of the models isn't quite implementation
   correctness.  technically we need to take into account
   the outer wrapping where the invariant is checked, where
   privacy is checked, etc.  But that should be easy enough
   to build off of this. *)
Module ImplCorrect : ModelIso with Module S := Spec 
                              with Module T := TupleModel.
  Export Config.
  Module S := Spec.
  Module T := TupleModel.
   
  Definition f cfg (x: sigT (S.I cfg)) : sigT (T.I cfg). 
  Admitted.
  Definition g cfg (y: sigT (T.I cfg)) : sigT (S.I cfg). 
  Admitted. 

  Theorem Correct : forall cfg t, 
   projT1 (f (g (cfg:=cfg) t)) = projT1 t. 
  Proof.
  Admitted.
End ImplCorrect.

(* we want to say that given a model and
   an imperative realization of that model, that
   we can build an app 
Require Import AppServer.

Module BuildApp (X: Model) (Y: Impl X) : App.
 Module C := Y X.
 Export C.
 Open Local Scope hprop_scope.
 Definition Q := Command.
 Definition T : Set := (Config * C.T)%type.
 Definition RR : Set := Status.
 Definition M := (Config * X.M)%type.
 Definition rep (t: T) (m: M) : hprop := [fst t = fst m] * C.rep (snd t) (snd m).
 Definition I (m: M) : Prop := X.I (fst m) (snd m).
 
 Definition func := X.mutate.

End BuildApp.
*)

(* these wrappers may come in handy 
   for above. *)
Module WrapModel (X: Model).
  Export X.

  Definition wrap cfg q m (pf_I: I cfg m) :=
    match P_dec cfg q with
      | left  pf_P => match E_dec cfg q with
                        | left  pf_E => mutate cfg q m  
                        | right pf_badgrade => (ERR_BADGRADE, m) 
                      end
      | right pf_notpriv => (ERR_NOTPRIVATE, m)
    end.
End WrapModel.

Require Import Ynot.
Module WrapImpl (X: Model) (Y: Impl).
 Module Z := Y X.
 Export Z.
 Module W := WrapModel X.
 Export W.

 Open Local Scope stsepi_scope.
 Open Local Scope hprop_scope.
 Definition imp_wrap cfg t q m : 
  STsep (m ~~ rep t m * [I cfg m] * [P cfg q] * [E cfg q]) 
   (fun r : Status => m ~~ Exists pf1 :@ I cfg m, 
                           let (r', m') := (wrap q pf1 )
                           in  [r' = r] * rep t m').
 Admitted. 
End WrapImpl.

Require Import Store.

(* And we need to do this as well
Module StoreImpl (s: Store) : Impl TupleModel .
 
End StoreImpl.
*)
