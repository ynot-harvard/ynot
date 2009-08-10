Require Import GradebookModel. (* change this module name or move to here *)
Require Import List.

Set Implicit Arguments.

(*
Module Config.
  (* privacy respecting queries can probably stay the same *)
  Definition P (cfg: Config) (q: Command) := True.
  (* likewise with correct queries *)
  Definition E (cfg: Config) (q: Command) := True. 
  (* todo add definition of privacy and wellformedness of q *)
  Parameter P_dec : forall cfg q, {P cfg q} + {~P cfg q}. (* privacy *)
  Parameter E_dec : forall cfg q, {E cfg q} + {~E cfg q}. (* valid query *)
End Config.
*)

Module Type Model.

  Parameter M : Type.
  Parameter I : Config -> M -> Prop.

  Parameter mutate : forall (cfg: Config) (m : M) (pfI : I cfg m) (q: Command), (Status * M).
  Parameter PreservesI : forall (cfg: Config) (m : M) (pfI: I cfg m) (q: Command),
    I cfg (snd (mutate pfI q)).

End Model.

(* equivalences of models *)
Module Type ModelIso.
  Declare Module S : Model.
  Declare Module T : Model.

  Parameter f : forall cfg, sigT (S.I cfg) -> sigT (T.I cfg).

  Parameter Correct : forall (cfg : Config) (m : S.M) (pfI : S.I cfg m) (q : Command),
    let t    := f (existT (S.I cfg) m pfI) in
    let sres := @S.mutate cfg m pfI q in
    let tres := @T.mutate cfg (projT1 t) (projT2 t) q in
    let t'   := @f cfg (@existT S.M (S.I cfg) (snd sres) (@S.PreservesI cfg m pfI q)) in
    fst sres = fst tres /\ projT1 t' = snd tres.

End ModelIso.

Module Spec <: Model.
  Definition M : Type := list (ID * list Grade).
  Definition I (cfg : Config) (m : M) : Prop :=
    store_inv m cfg = true.

  Definition mutate (cfg: Config) (m : M) (pfI : I cfg m) (q: Command) : (Status * M) :=
    if private cfg q
    then match q with
           | SetGrade id pass x a g => 
             if inbounds g a (totals cfg) 
             then match lookup x m with
                    | None => (ERR_NOINV, m)
                    | Some g' => (OK, insert x (nth_set g a g') m)  
                  end
             else (ERR_BADGRADE, m)
           | GetGrade id pass x a =>
             match lookup x m with
               | None => (ERR_NOINV, m) 
               | Some g' => match nth_get a g' with
                              | None => (ERR_BADGRADE, m)
                              | Some g'' => (RET g'', m)
                            end
             end
           | Average  id pass a => 
             if validAssignment cfg a then  
               match proj a m with
                 | None => (ERR_NOINV, m)
                 | Some x => (RET (avg x), m)
               end
               else (ERR_BADGRADE, m)
         end
      else (ERR_NOTPRIVATE, m).


  Theorem PreservesI : forall (cfg: Config) (m : M) (pfI: I cfg m) (q: Command),
    I cfg (snd (mutate pfI q)).
  Proof.
    unfold I. intros. unfold mutate.
    destruct q;
      [ exhaustive assumption
      | simpl in *; exhaustive assumption
      | simpl in *; exhaustive assumption ].
    unfold store_inv in *. all.
    Hint Resolve insert_preserves_noduples.
    Hint Resolve insert_preserves_total_dec.
    Hint Resolve insert_preserves_inv.
    each; auto.
  Qed.

End Spec.

(**
Module StoreModel <: Model.
  Require Import GradebookStoreImpl.
  Require Import Store.
  Export GradesStoreMapping.
  
  Definition M : Type := forall (cfg : Config), Table (S (length (totals cfg))).
  Definition I (cfg : Config) (m : M) : Prop :=
    True. (** TODO **)

  (** TODO **)
  Definition mutate (cfg: Config) (m : M) (pfI : I cfg m) (q: Command) : (Status * M) :=
    if private cfg q
    then match q with
           | SetGrade id pass x a g => (ERR_BADGRADE, m)
(*
             if inbounds g a (totals cfg) 
             then match lookup x m with
                    | None => (ERR_NOINV, m)
                    | Some g' => (OK, insert x (nth_set g a g') m)  
                  end
             else (ERR_BADGRADE, m)
*)
           | GetGrade id pass x a =>
             match nthget a (select (get_query id cfg) (m cfg)) with 
               | None => (ERR_NOINV, m) (** MAYBE **)
               | Some None => (ERR_BADGRADE, m) (** MAYBE **)
               | Some (Some g') => (RET g', m)
             end
           | Average  id pass a =>  (ERR_BADGRADE, m)
(*
             if validAssignment cfg a then  
               match proj a m with
                 | None => (ERR_NOINV, m)
                 | Some x => (RET (avg x), m)
               end
               else (ERR_BADGRADE, m)
*)
         end
      else (ERR_NOTPRIVATE, m).

  Theorem PreservesI : forall (cfg: Config) (m : M) (pfI: I cfg m) (q: Command),
    I cfg (snd (mutate pfI q)).
  Proof.
  Admitted.

End StoreModel.
**)

(**
(* our spec is a distinguished model *) 
Module Spec : Model.
  Definition  M := ID -> Assignment -> option Grade.
   
  Definition I (c : Config) (m : M) : Prop :=
    fold_right (fun (p : Prop) (rr : Prop) => p /\ rr) True
      (flat_map (fun id : ID => 
        map (fun x : Assignment * Grade =>
          match m id (fst x) with
            | Some g => g <= (snd x)
            | None => False
          end) (combine (seq 0 (length (totals c))) (totals c)))
      (students c)).
  
  Parameter mutate : forall (cfg: Config) (q: Command) (m: M), (Status * M).

  Theorem pres_I : forall cfg q m,
    I cfg (snd (mutate cfg q m)).
  Admitted.
End Spec.

(* The model of the imperative implementation *)
Module TupleModel : Model.
   Definition  M := ID -> Assignment -> option Grade. 
   
   Definition  I : Config -> M -> Prop. 
   Admitted.
  
  Parameter mutate : forall (cfg: Config) (q: Command) (m: M), (Status * M).

    Theorem pres_I : forall cfg q m,
    I cfg (snd (mutate cfg q m)).
    Admitted.
End TupleModel.


Module CorrectRefl (X: Model) : ModelIso with Module S := X 
                                         with Module T := X.
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
*)

Module Type Impl.
  Declare Module M : Model.
End Impl.

Require Import Ynot.

Module Type ImplF (X: Model).
 Export X.
  Parameter T: Set.
  Parameter rep : forall (t: T) (m: M), hprop.

  Open Local Scope hprop_scope.
(*
  Parameter imp_mutate : forall cfg t q (m: [M]),
    STsep (m ~~ rep t m * [I cfg m] * [P cfg q] * [E cfg q]) 
          (fun r : Status => m ~~ let (r', m') := (mutate cfg q m)
                                  in  [r' = r] * rep t m'). 
*)
End ImplF.

Require Import AppServer.

Module StoreImpl <: Impl with Module M := TupleModel.
  Module M := TupleModel.
End StoreImpl.

Module BuildApp (Y: Impl) : App.
 Module X := Y.M.

 Print X.
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

Require Import Ynot.
 


Require Import Store.

(* And we need to do this as well
Module StoreImpl (s: Store) : Impl TupleModel .
 
End StoreImpl.
*)
**)