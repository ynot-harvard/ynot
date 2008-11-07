
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

 (* This model is slightly different from Jahob's model
    using sets.  We expose lists, but with the with unique 
    keys invariant, these operations can implement
    the same list mutations that Jahob gets using set deletion 
    and union. *)  

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

End NondepAssocListModel.

(* This is the interface for the Jahob AssocList example. *)
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

 Parameter containsKey: forall k (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep m p)
         (fun r:bool => m ~~ rep m p * if r then Exists v :@ V, [In (k,v) m] 
                                            else [lookup m k = None]).
 (* todo: ~ Exists v, In (k,v) m] *)

 Parameter add: forall k v (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep m p * [~ In (k,v) m])
        (fun _:unit => m ~~ rep ((k,v)::m) p).

 Parameter replace: forall k v (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep m p * Exists v0 :@ V, [In (k,v0) m] )
        (fun r:V => m ~~ [In (k, r) m] * rep ((k,v)::(delete m k)) p).

 Parameter put: forall k v (p: t) (m: [list (prod K V)]), 
   STsep (m ~~ rep m p)
         (fun r => m ~~ [r = lookup m k] * rep (insert m k v) p).

 Parameter get: forall k   (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep m p)
         (fun r => m ~~ rep m p * match r with
                                    | None => [lookup m k = None]
                                    | Some v => [In (k, v) m]
                                  end).

(* todo [~ Exists v @: V, In m (k, v) *)

 Parameter isEmpty: forall (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep m p) (fun r:bool => m ~~ rep m p * if r then [m = nil] else [m <> nil]).

 Parameter remove: forall k (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep m p * Exists v :@ V, [In (k,v) m])
        (fun r:V => m ~~ [In (k, r) m] * rep (delete m k) p).

(* todo: classical logic -> proof irrelevence -> inconsistency *)

End JAHOB_ASSOC_LIST.

(* This uses the same implementation code as Jahob *)
Module JahobAssocList(A : NONDEP_ASSOCIATION) : JAHOB_ASSOC_LIST with Module A := A.
 Module A := A.
 Module AL := NondepAssocListModel(A).
 Require Import Ynot.
 Import AL.

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
                    | (k,v) :: b =>  Exists nxt :@ option ptr,
                          h --> node k v nxt * rep' b nxt * [lookup b k = None]
                    | nil => [False]
                   end
    end.

  Definition rep m p : hprop :=
    Exists n :@ option ptr, p --> n * rep' m n.

(* Reasoning **************************************************)


 Lemma nilrep : forall m k, 
  rep' m None ==> rep' m None * [lookup m k = None].
   intros. destruct m. sep fail auto. simpl. assert (p :: m = nil -> False).
   discriminate. sep fail auto. Defined.

 Hint Resolve nilrep.

 Lemma eta_node : forall fn, fn = node (key fn) (value fn) (next fn).
   destruct fn; reflexivity.
  Qed.
  Hint Resolve eta_node.

  Lemma eta_node2 : forall fn a b, 
   Some (a, b) = Some (key fn, value fn) -> 
   fn = node a b (next fn).
    intros fn a b pf; assert (a = key fn); try congruence; 
   assert (b = value fn); try congruence; subst; apply eta_node. 
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
    | [ H : Some ?a = Some ?b |- _ ] => assert (a = b); congruence; subst 
  end).

 Ltac printGoal := match goal with [ |- ?g ] => idtac g end.

 Ltac t := unfold rep; unfold rep'; try congruence; try subst; sep fail simplr.
 Ltac f := fold rep'; fold rep.

 Lemma reprev : forall hd0 m,
   rep' m (Some hd0) ==> Exists n :@ Node,
   [head m = Some (key n, value n)] * hd0 --> n *
   rep' (tail m) (next n). 
 intros. destruct m. t. t. Defined.

 Lemma lkup : forall v k x, Some v = lookup x k -> In (k, v) x.
  induction x; simpl; t. destruct a as [k0 v0]; destruct (eqK k k0); [ left; congruence | right; apply IHx; assumption ]. Qed.

(* Implementation ***************************************************)

  Open Scope stsepi_scope.

  Definition new : STsep __ (rep nil).
    refine {{ New (@None ptr) }}; t. Qed.

  Definition free  p: STsep (rep nil p) (fun _:unit => __).
  intros; refine {{ Free p }}; t. Qed.  

  (* This is get duplicated, so I'm going to defer until get is nicer *)
  Parameter containsKey: forall k (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep m p)
         (fun r:bool => m ~~ rep m p * if r then Exists v :@ V, [In (k,v) m] 
                                            else [lookup m k = None]).

  Definition add': forall k v (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep m p * [lookup m k = None])
         (fun _:unit => m ~~ rep ((k,v)::m) p).
   intros. refine ( op <- ! p ;
                    n  <- New (node k v op) ;
                    {{ p ::= (Some n) }} ); t. Qed.

  Conjecture add: forall k v (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep m p * [~ In (k,v) m])
        (fun _:unit => m ~~ rep ((k,v)::m) p).
  (* intros. refine ( {{ add' k v p m }}).  *)
  

(* Replace        **********)

 Parameter replace: forall k v (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep m p * Exists v0 :@ V, [In (k,v0) m] )
        (fun r:V => m ~~ [In (k, r) m] * rep ((k,v)::(delete m k)) p).

 (* Put           *********)

 Parameter put: forall k v (p: t) (m: [list (prod K V)]), 
   STsep (m ~~ rep m p)
         (fun r => m ~~ [r = lookup m k] * rep (insert m k v) p).

 (* Get           **********)

  Definition get'' (k: K) (hd: option ptr) (m: [list (prod K V)]):
    STsep (m ~~ rep' m hd) (fun r => m ~~ [r = lookup m k] * rep' m hd).
  intro k.
  refine (Fix2
    (fun hd m => m ~~ rep' m hd)
    (fun hd m o => m ~~ [o = lookup m k] * rep' m hd)
    (fun self : forall hd m, STsep (m ~~ rep' m hd) (fun r => m ~~ [r = lookup m k] * rep' m hd) => fun hd m => 
      IfNull hd
      Then  Assert (m ~~ [m = nil]) ;;
            {{ Return None }}
      Else  fn <- SepRead hd (fun fn => m ~~  [head m = Some (key fn, value fn)] * 
                                              rep' (tail m) (next fn) *
                                              [lookup (tail m) (key fn) = None] *
                                              [lookup m (key fn) = Some (value fn)] );
            if eqK (key fn) k 
            then {{ Return (Some (value fn)) 
                     <@>              (hd --> fn * (m ~~ 
                                              [head m = Some (key fn, value fn)] * 
                                              rep' (tail m) (next fn)  *
                                              [lookup (tail m) (key fn) = None] *    
                                              [lookup m k = Some (value fn)] ))  }}  
            else {{ self (next fn) (m ~~~ tail m) 
                     <@>             (hd --> fn * (m ~~  
                                              [head m = Some (key fn, value fn)] * 
                                              [lookup (tail m) (key fn) = None] )) }} ));
  try solve [ t | repeat (hdestruct m; t) ]. Qed.

  Definition get' (k: K) (p: ptr) (m: [list (prod K V)]) :
    STsep (m ~~ rep m p)
          (fun r:option V => m ~~ rep m p * [r = lookup m k] ).
  intros; refine (hd <- !p;
                  Assert (p --> hd * (m ~~ rep' m hd));;
                  {{get'' k hd m <@> _}}); t. Qed.

  Definition get: forall k   (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep m p)
         (fun r => m ~~ rep m p * match r with
                                    | None => [lookup m k = None]
                                    | Some v => [In (k, v) m]
                                  end).
  intros; refine ( {{ get' k p m }} ); [ t | intro v; destruct v; pose lkup; t ]. Qed.

 (* isEmpty         ********)

 Definition isEmpty: forall (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep m p) (fun r:bool => m ~~ rep m p * if r then [m = nil] else [m <> nil]).
 intros; refine ( ohd <- ! p ;
                   Assert (m ~~ p --> ohd * rep' m ohd) ;;
                  {{ Return (match ohd with | None => true | Some _ => false end) }} );
 solve [ t | hdestruct m; t ]. Qed.

 (* Remove         *********)

 Parameter remove: forall k (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep m p * Exists v :@ V, [In (k,v) m])
        (fun r:V => m ~~ [In (k, r) m] * rep (delete m k) p).

Parameter ff: False.

Definition cmp fn m v k hdptr p : STsep ([k = key fn] * [lookup m k = Some v] * p --> Some hdptr * 
                                                         hdptr --> fn * rep' (tail m) (next fn) * [lookup (tail m) (key fn) = None] * [head m = Some (key fn, value fn)]) 
                                          (fun r =>             [lookup m k = Some r] * rep (delete m k) p *
                                                                                                  [lookup (tail m) (key fn) = None] * [head m = Some (key fn, value fn)] ).
 intros. refine ( Free hdptr ;; p ::= next fn ;; {{ Return (value fn) }} ); t. Qed.

Definition remove'' k v (prev: ptr) (pn: Node) (m: list (prod K V)) : STsep
   ( Exists ck :@ K, Exists cv :@ V, [lookup m k = Some v] * [head m = Some (ck, cv)] * prev --> pn * rep' m (next pn) )
   (fun r:V => [Some r = lookup m k] * rep' ((key pn, value pn)::(delete m k)) (Some prev)).
intros k v. refine (Fix3 (fun prev pn m => Exists ck :@ K, Exists cv :@ V, [lookup m k = Some v] * [head m = Some (ck, cv)] * prev --> pn * rep' m (next pn) )
                         (fun prev pn m r => [Some r = lookup m k] * rep' ((key pn, value pn)::(delete m k)) (Some prev))
                         (fun F prev (pn: Node) m => 
  IfNull (next pn) As cur
  Then {{ !!! }}
  Else n <- ! cur ;
       if eqK (key n) k
       then prev ::= node (key pn) (value pn) (next n) ;;
            {{ Return (value n) }}
       else IfNull (next n) As nxt
            Then {{ !!! }}
            Else {{ F cur n (tail m) }})). Admitted.

 Definition remove' : forall k v (p: t) (m: list (prod K V)),
                     STsep (                        [lookup m k = Some v] * rep m p) 
                         (fun r:V =>                [lookup m k = Some r] * rep (delete m k) p).
 intros. refine ( 
 ohdptr <- ! p ;
 match ohdptr with
   | None => {{ !!! }}
   | Some hdptr => hd <- ! hdptr ;
                   match eqK (key hd) k with
                     | left _  => p ::= None ;;
                                  {{ Return (value hd) }}
                     | right _ => {{ remove'' k v hdptr hd (tail m) }} 
                   end
 end). Admitted.

                                                     
(* technically want rep -> uniq lemma *)


 (* The Jahob put operation traverses the list several times.  
    This implements a faster, in-place put that isn't found in Jahob. *)
(* This hasn't been updated for the uniqueness part of the invariant 
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

*)

End JahobAssocList.

