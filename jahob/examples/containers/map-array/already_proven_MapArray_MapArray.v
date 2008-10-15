(* This is just the beginning *)

Require Import Finite_sets_facts.
 Require Import Jahob.
 Require Import Omega.


Lemma MapArray_MapArray_InitialPartOfProcedure2 : forall  (tt : obj) (MapArray_maxSize_4 : (obj -> nat)) (MapArray_map_1 : (obj -> Ensemble ((obj * obj)))) (MapArray_map_3 : (obj -> (Ensemble ((obj * obj))))) (s : nat) (tmp_1_6 : obj) (Array : Ensemble obj) (tmp_1 : obj) (this : obj) (MapArray_map : (obj -> Ensemble ((obj * obj)))) (Node_value : (obj -> obj)) (MapArray_size : (obj -> nat)) (Object_alloc : Ensemble obj) (MapArray : Ensemble obj) (Array_arrayState : (obj -> (nat -> obj))) (Node_key : (obj -> obj)) (MapArray_a : (obj -> obj)) (Array_length : (obj -> nat)) (MapArray_maxSize : (obj -> nat)), 

((MapArray_maxSize = (fun(this:obj) => ((Array_length (MapArray_a this))))) /\  (* noDuplicates *) (forall (this:obj) (i:nat) (j:nat) (ni:obj) (nj:obj), (((((Node_key ni) = (Node_key nj)) /\ (ni = (Array_arrayState (MapArray_a this) i)) /\ (0 <= j) /\ (0 <= i) /\ (In _ MapArray this) /\ (In _ Object_alloc this) /\ (i<(MapArray_size this)) /\ (j<(MapArray_size this)) /\ (nj = (Array_arrayState (MapArray_a this) j)) /\ ((Node_value ni) = (Node_value nj))) -> (i = j)))) /\  (* arraysDisjoint *) (forall (ma1:obj) (ma2:obj) (n1:obj) (i:nat) (j:nat), ((((n1 <> null) /\ (j<(Array_length ma2)) /\ (i<(Array_length ma1)) /\ (In _ MapArray ma2) /\ (In _ Object_alloc ma2) /\ (In _ Object_alloc ma1) /\ (In _ MapArray ma1) /\ (0 <= i) /\ (0 <= j) /\ (n1 = (Array_arrayState (MapArray_a ma1) i)) /\ (n1 = (Array_arrayState (MapArray_a ma2) j))) -> (ma1 = ma2)))) /\ (MapArray_map = (fun(this:obj) => ((fun(p:(obj * obj)) => ((exists k, ((exists v, (((p = (k, v)) /\ (exists i, ((exists n, (((k = (Node_key n)) /\ (n = (Array_arrayState (MapArray_a this) i)) /\ (0 <= i) /\ (i<(MapArray_size this)) /\ (n <> null) /\ (v = (Node_value n))))))))))))))))) /\  (* thisNotNull *) (this <> null) /\  (* tmp_1_type *) (In _ Array tmp_1) /\  (* tmp_1_type *) (In _ Object_alloc tmp_1) /\ ((Array_length tmp_1_6) = s) /\ (forall (y:obj), (((Node_key y) <> tmp_1_6))) /\ (forall (y:obj), (((Node_value y) <> tmp_1_6))) /\ ((Node_key tmp_1_6) = null) /\ ((Node_value tmp_1_6) = null) /\ ~ (In _ Object_alloc tmp_1_6) /\ (tmp_1_6 <> null) /\ (MapArray_map_3 = (fun(this__6:obj) => ((fun(p:(obj * obj)) => ((exists k, ((exists v, (((p = (k, v)) /\ (exists i, ((exists n, (((k = (Node_key n)) /\ (n = (Array_arrayState ((fieldWrite MapArray_a this tmp_1_6) this__6) i)) /\ (0 <= i) /\ (i<(MapArray_size this__6)) /\ (n <> null) /\ (v = (Node_value n))))))))))))))))) /\ (MapArray_map_1 = (fun(this__4:obj) => ((fun(p:(obj * obj)) => ((exists k, ((exists v, (((p = (k, v)) /\ (exists i, ((exists n, (((k = (Node_key n)) /\ (n = (Array_arrayState ((fieldWrite MapArray_a this tmp_1_6) this__4) i)) /\ (0 <= i) /\ (i<((fieldWrite MapArray_size this 0) this__4)) /\ (n <> null) /\ (v = (Node_value n))))))))))))))))) /\ (MapArray_maxSize_4 = (fun(this__5:obj) => ((Array_length ((fieldWrite MapArray_a this tmp_1_6) this__5))))) /\ (forall (ma:obj), (((In _ Object_alloc ma) -> (In _ Object_alloc (MapArray_a ma))))) /\  (* thisType *) (In _ MapArray this) /\  (* thisType *) (In _ Object_alloc this) /\ (In _ (Setminus _  Object_alloc (Singleton _ tmp_1_6)) tt) /\ (In _ MapArray tt) /\ (tt <> this) ->  (* othersSame *) ( Same_set _ (MapArray_map_1 tt) (MapArray_map tt))).
Proof.
intros . intuition simpl.  subst .  unfold Same_set.
 split ; unfold Included ; intros ; unfold In in *|-*  ; 
destruct H0 ; exists x0 ; destruct H0 ; exists x1 ;
intuition simpl ; destruct H6 ; exists x2 ; destruct H0 ;
exists x3 ; intuition simpl . 
try rewrite fieldwrite_def2 in H0 ; try eauto .
try rewrite fieldwrite_def2 in H14 ; try eauto.
rewrite fieldwrite_def2 ; eauto. 
rewrite fieldwrite_def2; eauto. 
Qed.
Hint Resolve MapArray_MapArray_InitialPartOfProcedure2.

