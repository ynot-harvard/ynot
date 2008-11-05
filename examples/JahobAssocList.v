
Module Type NONDEP_ASSOCIATION.
  (* This is weaker than the real ynot finite map because the
     type of a value does not depend on its key.
     However, it corresponds to Jahob when V := ptr. *) 
  Variables K V : Set.
  Variable  eqK : forall (k1 k2: K), {k1 = k2} + {k1 <> k2}.
End NONDEP_ASSOCIATION.

Module NondepAssocListModel(A : NONDEP_ASSOCIATION).
 Export A.
 Require Export List.
 Set Implicit Arguments.

 Check fold_left.

 Fixpoint update l (k: K) (v: V)  :=
   match l with
     | nil => nil
     | (k', v')::b => if eqK k k' then (k, v) :: b else (k', v') :: update b k v
    end.

 Fixpoint delete (l: list (prod K V)) (k: K) :=
  match l with
    | nil => nil
    | (k', v')::b => if eqK k k'  then b else (k',v') :: (delete b k)
  end.

 Fixpoint insert l (k: K) (v: V)  :=
   match l with
     | nil => (k, v)::nil
     | (k', v')::b => if eqK k k' then (k, v) :: b else (k', v') :: insert b k v
   end.

 Fixpoint lookup l (k: K) : option V :=
   match l with
    | nil => None
    | (k', v)::b => if eqK k k' then Some v else lookup b k
   end.
End NondepAssocListModel.

(* This is the interface for the Jahob AssocList example.
   (Minus containsKey, which is essentially a duplicate of get).
   Specs are written using the 'operational' definitions
   above rather than set theory. *)
Module Type JAHOB_ASSOC_LIST.
 Require Export List.
 Declare Module A  : NONDEP_ASSOCIATION.
 Module AL := NondepAssocListModel(A).
 Import AL.

 Require Export Ynot.
 Open Scope hprop_scope.

 Parameter t   : Set.
 Parameter rep : list (prod K V) -> t -> hprop.

 Parameter new : STsep __ (rep nil).
 Parameter free: forall (p: t),
   STsep (rep nil p) (fun _: unit => __).

 Parameter add: forall k v (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep m p * [lookup m k = None])
        (fun _:unit => m ~~ rep ((k,v)::m) p).

 Parameter replace: forall k v (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep m p * Exists v :@ V, [lookup m k = Some v])
        (fun r:V => m ~~ rep (update m k v) p).

 Parameter remove: forall k (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep m p * Exists v :@ V, [lookup m k = Some v])
        (fun r:V => m ~~ rep (delete m k) p * [Some r = lookup m k]).

 Parameter put: forall k v (p: t) (m: [list (prod K V)]), 
   STsep (m ~~ rep m p)
         (fun r => m ~~ [r = lookup m k] * rep (insert m k v) p).

 Parameter get: forall k   (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep m p)
         (fun r => m ~~ [r = lookup m k] * rep m p).

 Parameter isEmpty: forall (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep m p) (fun r:bool => m ~~ rep m p * if r then [m = nil] else [m <> nil]).

End JAHOB_ASSOC_LIST.

Module JahobAssocList(A : NONDEP_ASSOCIATION) : JAHOB_ASSOC_LIST with Module A := A.
 Module A := A.
 Module AL := NondepAssocListModel(A).
 Import AL.
 Require Import Ynot.
 Open Scope hprop_scope.

(* Representation ***********************************************)

  Definition t : Set := ptr.
 
  Record Node : Set := node {
    key  : K;
    value: V;
    next : option ptr
  }.

  Fixpoint rep' m (op: option ptr) {struct m} :=
    match op with
      | None => [m = nil]
      | Some h => match m with
                    | (k,v) :: b => 
                        Exists nxt :@ option ptr, 
                          h --> node k v nxt * rep' b nxt
                    | nil => [False]
                   end
    end.

  Definition rep m p : hprop :=
    Exists n :@ option ptr, p --> n * rep' m n.

(* Reasoning **************************************************)

 Lemma eta_node : forall fn, fn = node (key fn) (value fn) (next fn).
   destruct fn; reflexivity.
  Qed.
  Hint Resolve eta_node.

  Lemma eta_node2 : forall fn a b, 
   Some (a, b) = Some (key fn, value fn) -> 
   fn = node a b (next fn).
    intros fn a b pf; assert (a = key fn); try congruence; assert (b = value fn); try congruence; subst; apply eta_node. 
  Qed.
  Hint Resolve eta_node2.

  Ltac simplr := repeat (try discriminate;
  match goal with
    | [ H : head ?x = Some _ |- _ ] =>
      destruct x; simpl in *; [
        discriminate
        | injection H; clear H; intros; subst
      ]
    | [ |- context[ match ?v with
             | Some _ => _
             | None   => _ 
           end ==> _] ] => destruct v  
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H; clear H; intros; subst
    | [ |- context[ if (eqK ?v1 ?v2) then _ else _ ] ] => destruct (eqK v1 v2)
    | [ H : Specif.value ?a = Some ?b |- _ ] =>  unfold Specif.value in H; assert (a = b); congruence 
  end).

 Ltac printGoal := match goal with [ |- ?g ] => idtac g end.

 Ltac t := unfold rep; unfold rep'; try congruence; try subst; sep fail simplr.
 Ltac f := fold rep'; fold rep.


(* Implementation ***************************************************)

  Open Scope stsepi_scope.

  Definition new : STsep __ (rep nil).
    refine {{ New (@None ptr) }};
      t.
  Qed.

  Definition free  p: STsep (rep nil p) (fun _:unit => __).
  intros; refine {{ Free p }}; 
     t.
  Qed.  

  Definition get'' (k: K) (hd: option ptr) (m: [list (prod K V)]):
    STsep (m ~~ rep' m hd) (fun r => m ~~ [r = lookup m k] * rep' m hd).
  intro k.
  refine (Fix2
    (fun hd m => m ~~ rep' m hd)
    (fun hd m o => m ~~ [o = lookup m k] * rep' m hd)
    (fun self hd m =>
      IfNull hd 
      Then {{ Return None }}
      Else  Assert (m ~~ Exists fn :@ Node, [head m = Some (key fn, value fn)] * hd --> fn * rep' (tail m) (next fn)) ;; 
            fn <- !hd ;     
            if eqK (key fn) k  
            then {{ Return (Some (value fn)) }} 
            else {{ self (next fn) (m ~~~ tail m) <@> (m ~~ hd --> fn * [head m = Some (key fn, value fn)]) }} 
      ));  try solve [ t | repeat (hdestruct m; t) ]. Defined.

  Definition get (k: K) (p: ptr) (m: [list (prod K V)]) :
    STsep (m ~~ rep m p)
          (fun r:option V => m ~~ [r = lookup m k] * rep m p ).
  intros; refine (hd <- !p;
                  Assert (p --> hd * (m ~~ rep' m hd));;
                  {{get'' k hd m <@> _}});
    t. Defined. 

 (* This will verify even without the lookup m k = None
    condition.  Rather than 'bake in' the uniqueness of keys into
    the heap invariant we can instead only expose operations
    that preserve this additional property.  However, I think
    this might be cheating because you can't take an arbitary
    pointer satisfying the invariant and claim that it actually
    models an association list without also knowing that 
    nothing else has messed it up.  So I need to go back and
    change the invariant. *)    
 Definition add: forall k v (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep m p * [lookup m k = None])
        (fun _:unit => m ~~ rep ((k,v)::m) p).
 intros. refine ( op <- ! p ;
                  n  <- New (node k v op) ;
                  {{ p ::= (Some n) }} ); try t. Defined.

 Conjecture replace: forall k v (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep m p * Exists v :@ V, [lookup m k = Some v])
        (fun r:V => m ~~ rep (update m k v) p).

 Conjecture remove: forall k (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep m p * Exists v :@ V, [lookup m k = Some v])
        (fun r:V => m ~~ rep (delete m k) p * [Some r = lookup m k]).

 Conjecture put: forall k v (p: t) (m: [list (prod K V)]), 
   STsep (m ~~ rep m p)
         (fun r => m ~~ [r = lookup m k] * rep (insert m k v) p).

 Conjecture isEmpty: forall (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep m p) (fun r:bool => m ~~ rep m p * if r then [m = nil] else [m <> nil]).


 (* The Jahob put operation traverses the list several times.  
    This implements a faster, in-place put that isn't found in Jahob. *)

 Definition putFast' (k: K) (v: V) (hdptr: ptr) (m: [list (prod K V)]) :
  STsep (m ~~ rep' m (Some hdptr))
        (fun r => m ~~ [r = lookup m k] * rep' (insert m k v) (Some hdptr)).
intros k v. 
refine (Fix2 
    (fun hdptr m => m ~~ rep' m (Some hdptr))
    (fun hdptr m r => m ~~ [r = lookup m k] * rep' (insert m k v) (Some hdptr))
    (fun F hdptr m => Assert (m ~~ Exists fn :@ Node, [head m = Some (key fn, value fn)] * hdptr --> fn * rep' (tail m) (next fn)) ;; 
                      fn <- !hdptr ;     
                      if eqK k (key fn) 
                      then  hdptr ::= node k v (next fn)  ;;
                           {{ Return Some (value fn) }} 
                      else  IfNull (next fn) As nxt
                           Then xx <- New (node k v None);
                                hdptr ::= node (key fn) (value fn) (Some xx) ;; 
                                {{ Return None }}
                           Else {{ F nxt (m ~~~ tail m) <@> (m ~~ hdptr --> fn  * [head m = Some (key fn, value fn)]) }} )); 
 try solve [ t | progress (hdestruct m; t) | destruct fn; hdestruct m; t; destruct m; t; t ]. Defined. 


Definition putFast (k: K) (v: V) (p : ptr) (m : [list (prod K V)])  :
  STsep (m ~~ rep m p)
        (fun r => m ~~ [r = lookup m k] * rep (insert m k v) p ).
intros; refine(
   opthd <- !p ;
   IfNull opthd
   Then xx <- New (node k v None) ;
        p ::= Some xx ;;
        {{ Return None }}
   Else {{ putFast' k v opthd m <@> _ }} );
 try solve [ t | progress (hdestruct m; t) | destruct fn; hdestruct m; t; destruct m; t; t ]. Defined.

End JahobAssocList.

