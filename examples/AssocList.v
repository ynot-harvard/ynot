Require Import List.
Require Import Ynot.

Set Implicit Arguments.

Open Local Scope hprop_scope.
Open Local Scope stsep_scope.
Open Local Scope stsepi_scope.

Section ASSOC_LIST.

Variables K V: Set.
Variable eqK : forall (k1 k2: K), {k1=k2} + {k1<>k2}.

Record Node : Set := node {
  key: K;
  value: V;
  next: option ptr
}.

(*
Theorem t : forall p1 p2 (a1 a2: K), (p1 --> a1 * p2 --> a2 ==> p1 --> a1 * p2 --> a2 * [p1 <> p2]) .
 intros. unfold hprop_imp. sep auto. repeat (destruct H). destruct H0.
 exists ((x * x0)%heap). exists empty.  sep auto. exists x. exists x0. sep auto. split_prover'. compute.
 split. apply ext_eq. auto. intros. subst.  
compute in H. compute in H2. pose (H p2). pose (H2 p2). destruct H3. destruct H0. compute in H1. compute in H0. rewrite H1 in *. rewrite H0 in *. assumption. Defined.
*)

(* ptr to
     (some (ptr to first node of list) | none) *)
Definition AssocList : Set := ptr.

Fixpoint rep' (m : list (prod K V)) (p : option ptr) {struct m} : hprop :=
  match p with
    | None => [m = nil]
    | Some hd => match m with
                   | (k,v) :: b => Exists nxt :@ option ptr, hd --> node k v nxt * rep' b nxt
                   | nil => [False]
                 end
  end.

Definition rep (m: list (prod K V)) (ll: AssocList) : hprop :=
  Exists n :@ option ptr, ll --> n * rep' m n.

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

Ltac simplr := repeat (try discriminate;
  match goal with
    | [ H : head ?x = Some _ |- _ ] =>
      destruct x; simpl in *; [
        discriminate
        | injection H; clear H; intros; subst
      ]
    | [ |- match ?v with
             | Some _ => _
             | None   => _
           end ==> _] => destruct v
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H; clear H; intros; subst
    | [ |- context[ if (eqK ?v1 ?v2) then _ else _ ] ] => destruct (eqK v1 v2)
    | [ x : option _ |- _ ] => destruct x 
(*    | [ H : Some ?a = Some ?b |- _ ] => assert (a = b); congruence *)
  end).

Ltac t := unfold rep; unfold rep'; try congruence; try subst; sep simplr.
Ltac f := fold rep'; fold rep.

Definition new : STsep __ (rep nil).
  refine {{ New None }};
    t.
Qed.

Definition free (ll: AssocList) :
  STsep (rep nil ll) (fun _:unit => __).
  intros; refine {{ FreeT ll :@ option ptr }};
    t.
Qed.

Fixpoint insert (l: list (prod K V)) (k: K) (v: V)  :=
 match l with
  | nil => (k, v)::nil
  | (k', v')::b => if eqK k k' 
                   then (k, v) :: b
                   else (k', v') :: insert b k v
 end.

Fixpoint lookup (k: K) (l: list (prod K V)) : option V :=
 match l with
  | nil => None
  | (k', v)::b => if eqK k k'
                  then Some v
                  else lookup k b
 end.

Parameter ff:False.

(* ptr to
     (some (ptr to first node of list) | none) *)

Lemma eta_node : forall fn, fn = node (key fn) (value fn) (next fn).
  destruct fn; reflexivity.
Qed.
Hint Resolve eta_node.

Lemma eta_node2 : forall fn a b, Some (a, b) = Some (key fn, value fn) -> fn = node a b (next fn).
 intros fn a b pf; assert (a = key fn); try congruence; assert (b = value fn); try congruence; subst; apply eta_node. 
Qed.
Hint Resolve eta_node2.


Definition sub1 (k: K) (v: V) (hdptr: ptr) m fn :
 STsep               (match m with | nil => [False] 
                                   | (k0,v0)::tl => match tl with | _ :: _ => [False]
                                                                  | nil => [fn = node k0 v0 None] * hdptr --> fn * [k <> k0] end  
                      end)
       (fun r:option V => match m with | nil => [False]  
                                   | (k0,v0)::tl => match tl with | _ :: _ => [False]
                                                                  | nil => [r = None] * [fn = node k0 v0 None] * rep' ((k0, v0)::(k, v)::nil) (Some hdptr) * [k <> k0] end 
                         end).
intros. refine ( xx <- New (node k v None) <@> match m with 
                                                 | nil => [False] 
                                                 | (k0,v0)::tl => match tl with | _ :: _ => [False]
                                                                                | nil => [fn = node k0 v0 None] * hdptr --> fn * [k <> k0] end  
                                               end ;

                       hdptr ::= node (key fn) (value fn) (Some xx) <@> (match m with
                                                                          | nil => [False]
                                                                          | (k0,v0)::tl => match tl with | _ :: _ => [False] 
                                                                                                         | nil => [fn = node k0 v0 None] * 
                                                                            [k <> k0] * xx --> node k v None end
                                                                        end) ;; 
                       {{ Return None <@> match m with
                                            | nil => [False]
                                            | (k0,v0)::tl => match tl with | _ :: _ => [False] 
                                                                           | nil => [fn = node k0 v0 None] *
                                              [k <> k0] * xx --> node k v None * hdptr --> node k0 v0 (Some xx) end
                                       end }} ) .
 solve [ t | repeat (destruct m; t) ].
 solve [ t | repeat (destruct m; t) ].
 solve [ t | repeat (destruct m; t) ].
 solve [ t | repeat (destruct m; t) ].
 solve [ t | repeat (destruct m; t) ].
 solve [ t | repeat (destruct m; t) ].
Defined.

Definition put' (k: K) (v: V) (hdptr: ptr) m  :
  STsep (match m with | nil => [False] | _ :: _ => rep' m (Some hdptr) end) 
        (fun r => match m with
                    | nil => [False]
                    | (k0,v0)::tl =>  match eqK k k0 with
                                        | left  _ =>  [r = Some v0] * rep' ((k,v)::tl) (Some hdptr)
                                        | right _ =>  [r = lookup k tl] * rep' ((k0,v0)::(insert tl k v)) (Some hdptr)
                                      end
                  end).
intros k v. refine ((Fix2 
    (fun hdptr m => (match m with | nil => [False] | _ :: _ => rep' m (Some hdptr) end))
    (fun hdptr m r => match m with
                    | nil => [False]
                    | (k0,v0)::tl =>  match eqK k k0 with
                                        | left  _ =>  [r = Some v0] * rep' ((k,v)::tl) (Some hdptr)
                                        | right _ =>  [r = lookup k tl] * rep' ((k0,v0)::(insert tl k v)) (Some hdptr)
                                      end
                  end)
    (fun F hdptr m => fn <- hdptr !! fun fn =>       (match m with | nil => [False] | (k0,v0)::tl => [k0 = key fn] * [v0 = value fn] * rep' tl (next fn) end) ;    
         {{ match eqK k (key fn) as eqx return STsep (match m with | nil => [False] | (k0,v0)::tl => [k0 = key fn] * [v0 = value fn] * rep' tl (next fn) * hdptr --> fn end)                                              (fun r => match m with | nil => [False] | (k0,v0)::tl => [k0 = key fn] * [v0 = value fn] *
                                                               match eqx with 
                                                                 | left _  => [r = Some v0] * rep' ((k,v)::tl) (Some hdptr)    
                                                                 | right _ => [r = lookup k tl] * rep' ((k0,v0)::(insert tl k v)) (Some hdptr)
                                                               end end) with
                             | left  _ => hdptr ::= node k v (next fn) <@> (match m with | nil => [False] | (k0,v0)::tl => 
                                                                             [k0 = key fn] * [v0 = value fn] * rep' (tail m) (next fn) end)  ;;
                                          {{ Return (Some (value fn)) }} 

                             | right _ => {{ match (next fn)  as nfn return STsep ( [next fn = nfn] *  match m with | nil => [False] 
                                                                                      | (k0,v0)::tl =>[k0 = key fn] * [v0 = value fn] * rep' tl nfn * hdptr --> fn end)
                                             (fun r =>  match m with | nil => [False] | (k0,v0)::tl => [k0 = key fn] * [v0 = value fn] * 
                                                                                ([r = lookup k tl] * rep' ((k0,v0)::(insert tl k v)) (Some hdptr)) end) with
                                              | None => Assert (match m with | nil => [False] | (k0,v0)::tl => [k0 = key fn] * [v0 = value fn] *  
                                                                                                 rep' tl None * hdptr --> fn * [next fn = None] end) ;;
                                                        {{ sub1 k v hdptr m fn  }}  
                                              | Some nxt => False_rect _ ff (* F nxt (tail m) *)   
                                       end  }}
           end }} ))).
 solve [ t | repeat (destruct m; t) ].
 solve [ t | repeat (destruct m; t) ].
 solve [ t | repeat (destruct m; t) ].
 solve [ t | repeat (destruct m; t) ].
 solve [ t | repeat (destruct m; t) ].
 solve [ t | repeat (destruct m; t) ].
 solve [ t | repeat (destruct m; t) ].
 solve [ t | repeat (destruct m; t) ].

Focus 3. solve [ t | repeat (destruct m; t) ].
Focus 3. solve [ t | repeat (destruct m; t) ].
Focus 3. solve [ t | repeat (destruct m; t) ].
Focus 3. solve [ t | repeat (destruct m; t) ].

Focus 2. destruct m. t. destruct m. simpl. t. t.
destruct m. t. destruct m. simpl. t. t. rewrite <- H0. t. t.
Defined.

Definition put (k: K) (v: V) (p : ptr) (m : list (prod K V))  :
  STsep (rep m p)
        (fun r => [r = lookup k m] * rep (insert m k v) p ).
intros; refine(
   opthd <- p !! fun opthd => rep' m opthd ;
      match opthd return  STsep (p --> opthd * rep' m opthd) (fun r => [r = lookup k m] * rep (insert m k v) p)  with 
         | None => xx <- New (node k v None) ;
                   p ::= Some xx ;;
                   {{ Return None }} 
         | Some hdptr => {{ put' k v hdptr m <@> p --> Some hdptr }}
      end);  try solve [ t | repeat (destruct m; t; try (destruct m; t)) ]. Defined.


Definition get'' (k: K) (hd: option ptr) (m: [list (prod K V)]):
 STsep (m ~~ rep' m hd)
       (fun res:option V => m ~~ [res = lookup k m] * rep' m hd).
intro k.
refine (Fix2
    (fun hd m => m ~~ rep' m hd)
    (fun hd m o => m ~~ [o = lookup k m] * rep' m hd)
    (fun self hd m =>
      IfNull hd 
      Then {{ Return None }}
      Else fn <- hd !! fun fn => m ~~ [head m = Some (key fn, value fn)] * rep' (tail m) (next fn) ;
           if eqK (key fn) k  
           then {{ Return (Some (value fn)) }} 
           else {{ self (next fn) (m ~~~ tail m) <@> (m ~~ hd --> fn * [head m = Some (key fn, value fn)]) }} 
      ));  try solve [ t | repeat (hdestruct m; t) ].
Defined.

Definition get (k: K) (ll: AssocList) (m: [list (prod K V)]) :
  STsep (m ~~ rep m ll)
        (fun r:option V => m ~~ rep m ll * [r = lookup k m]).
intros; refine (hd <- !ll;
    Assert (ll --> hd * (m ~~ rep' m hd));;
    {{get'' k hd m <@> _}});
  t. Defined. 

End ASSOC_LIST.

