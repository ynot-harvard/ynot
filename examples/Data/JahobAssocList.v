(* Copyright (c) 2008, Harvard University
 * All rights reserved.
 *
 * Author: Ryan Wisnesky
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - The names of contributors may not be used to endorse or promote products
 *   derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

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

 Fixpoint delete (l: list (prod K V)) (k: K) :=  
   match l with  
     | nil => nil
     | (k', v')::b => if eqK k k'  then delete b k  else (k',v') :: (delete b k)  
   end.

 Fixpoint lookup l (k: K) : option V         :=  
   match l with  
     | nil => None
     | (k', v)::b   => if eqK k k'  then Some v      else lookup b k               
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

(* This is the interface for the Jahob AssocList example,
   as expressed in Y0. *)
Module Type JAHOB_ASSOC_LIST.
 Require Export List.
 Declare Module A  : NONDEP_ASSOCIATION.
 Module AL := NondepAssocListModel(A).
 Import AL.

 Require Export Ynot.
 Open Scope hprop_scope.

 Parameter t   : Set.
 Parameter rep : t -> list (prod K V) -> hprop.

 Parameter new : STsep __ (fun r => rep r nil).
 Parameter free: forall (p: t),
   STsep (rep p nil) (fun _: unit => __).

 Parameter add: forall k v (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m * [lookup m k = None])
         (fun _:unit => m ~~ rep p ((k,v)::m)).

 Parameter put: forall k v (p: t) (m: [list (prod K V)]), 
   STsep (m ~~ rep p m)
         (fun r => m ~~ [lookup m k = r] * rep p ((k,v)::(delete m k))).

 Parameter get: forall k   (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m)
         (fun r:option V => m ~~ rep p m * [lookup m k = r] ).

 Parameter isEmpty: forall (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m) (fun r:bool => m ~~ rep p m * if r then [m = nil] else [m <> nil]).

 Parameter remove : forall k (p: t) (m: [list (prod K V)]),
                     STsep (m ~~ rep p m * Exists v :@ V, [lookup m k = Some v]) 
                (fun r:V => m ~~ rep p (delete m k) *     [lookup m k = Some r]).

 Parameter replace: forall k v (p: t) (m: [list (prod K V)]),
  STsep (m ~~             rep p m * Exists v0 :@ V,     [lookup m k = Some v0] )
        (fun r:V => m ~~  rep p ((k,v)::(delete m k)) * [lookup m k = Some r ] ).

(* technically want rep -> uniq lemma *)

(* drop contains key *)

End JAHOB_ASSOC_LIST.

(* This uses the same algorithms as Jahob *)
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

  Fixpoint rep' (op: option ptr) m {struct m} :=
    match op with
      | None => [m = nil] 
      | Some h => match m with
                    | (k,v) :: b =>  Exists nxt :@ option ptr,
                          h --> node k v nxt * rep' nxt b * [lookup b k = None]
                    | nil => [False]
                   end
    end.

  Definition rep p m : hprop :=
    Exists n :@ option ptr, p --> n * rep' n m.

(* Reasoning **************************************************)

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
    | [ |- _ ==> match ?v with
             | Some _ => _
                   | None   => _
                 end ] =>
      match type of v with
        | option ?T => equate v (@None T)
      end
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H; clear H; intros; subst
    | [ H : next _ = _ |- _ ] => rewrite -> H
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
    | [  H : ?a = ?b -> False , HH : (if (eqK ?a ?b) then Some _ else None) = Some _  |- _ ] => 
            destruct (eqK a b) ; [ contradiction | discriminate ] 
    | [  HH : (if (eqK ?a ?b) then Some _ else _) = None  |- _ ] => 
            destruct (eqK a b) ; [ discriminate | idtac ]
    | [  H : ?a = ?b -> False , HH : (if (eqK ?a ?b) then Some _ else Some ?v1) =
             Some ?v  |- context[Some ?v1 = Some ?v] ] => 
           destruct (eqK a b) ; [ try congruence | try contradiction ] 
    | [ _ : ?a = ?b -> False ,  HH : (if (eqK ?a ?b) then _ else ?c) = ?d  |- _ ] => 
           destruct (eqK a b) ; [ contradiction | idtac ]
    | [ |- context[ if eqK ?a ?a then _ else _ ] ] => destruct (eqK a a) 
    | [ H : ?a = ?b -> False |- context[ if eqK ?a ?b then _ else _ ] ] =>
             destruct (eqK a b); [ contradiction | idtac ] 
    | [  H : next ?nn = ?a |- ?n = node (key ?nn) (value ?nn) ?a ] =>
              rewrite <- H; destruct n; reflexivity
    | [ _ : (if eqK ?a ?b then Some _ else None) = Some _ |- _ ] => 
           destruct (eqK a b); [ idtac | discriminate ] 
    | [ _ : (if eqK ?a ?a then _ else _) = _ |- _ ] => destruct (eqK a a); [ idtac | intuition ] 
  end).

Ltac t := unfold rep; unfold rep'; sep fail simplr.
Ltac f := fold rep'; fold rep.

Lemma eta_node : forall fn, fn = node (key fn) (value fn) (next fn).
  destruct fn; reflexivity.
Qed.

Hint Resolve eta_node.

Lemma ll_concat : forall nde a b c hd, Some (key nde, value nde) = head a ->
  rep' (next nde) (tail a ++ b :: c) * hd --> nde *
   [lookup (tail a ++ b :: c) (key nde) = None] ==> rep' (Some hd) (a ++ b :: c)  .
  induction a; t.
Qed.

Hint Resolve ll_concat.
Lemma cons_nil : forall l2 x0 x, rep' l2 x0 * rep' None x ==> rep' l2 (x ++ x0).
  destruct x; t.
Qed.
Lemma node_next : forall nde p,  next nde = p -> nde = node (key nde) (value nde) p.
  destruct nde; simpl; congruence.
Qed.

Hint Resolve cons_nil.
Hint Resolve node_next.

Lemma lkup: forall m k x, 
 lookup m x = None -> lookup (delete m k) x = None. 
intros. induction m. t. trivial. simpl in *. destruct a. t.
 destruct (eqK x k0). t. destruct (eqK k k0). t. t. Qed.

(* Hint Resolve lkup. *)

Theorem rep'_None : forall ls,
  rep' None ls ==> [ls = nil].
  destruct ls; sep fail idtac.
Qed.

Theorem rep'_Some : forall ls hd,
  rep' (Some hd) ls ==> Exists k :@ K, Exists v :@ V, 
    Exists t :@ list (prod K V), Exists p :@ option ptr,
  [ls = (k,v) :: t] * hd --> node k v p * [lookup t k = None] * rep' p t.
  destruct ls; sep fail ltac:(try discriminate).
Qed.

Lemma node_eta : forall fn k v x,
  [fn = node k v x] ==> [key fn = k] * [value fn = v] * [next fn = x].
  destruct fn; sep fail ltac:(try congruence).
Qed.

Lemma cons_eta : forall x h t,
  [x = h :: t] ==> [head x = Some h] * [tail x = t].
  destruct x; sep fail ltac:(try congruence).
Qed.

Lemma rep'_eq : forall m x v0 v1 x0 fn,
  m = [x]%inhabited
  -> (m ~~~ tail m) = [x0]%inhabited
  -> tail x = v0
  -> next fn = v1
  -> rep' v1 v0 ==> rep' (next fn) x0.
  t.
Qed.

Hint Resolve rep'_eq.

Theorem rep_rep' : forall m p, rep p m ==>
  Exists n :@ option ptr, p --> n * rep' n m. t. Qed.

Hint Resolve rep_rep'.

Lemma repl : forall m p k, (rep p m * Exists v :@ V, [lookup m k = Some v]) ==>
 Exists x :@ option ptr, p --> x * (Exists cur :@ ptr, [x = Some cur] * rep' (Some cur) m * Exists v :@ V, [lookup m k = Some v]).
Proof.
  induction m. intros. sep fail auto. instantiate (1 := v). instantiate (1 := p). inversion H0.
  intros. destruct a. unfold rep; case_eq (eqK k k0); intros; subst; inhabiter.
  unfold lookup. rewrite H. simpl. destruct v0. sep fail auto. sep fail auto.
  instantiate (1 := None). instantiate (1:= p). inversion H3.
  simpl. rewrite H in *. destruct v0. inhabiter. sep fail auto. instantiate (1 := v1).
  sep fail auto.
  intro_pure. inversion H3.
Qed.

Hint Resolve repl.

Ltac simp_prem :=
  simpl_IfNull;
  repeat simpl_prem ltac:(apply rep'_None || apply rep'_Some || apply repl ||
                          apply node_eta || apply cons_eta || apply rep_rep');
    unpack_conc.

Ltac destr := match goal with [ x : list (prod K V) |- context[rep' None ?x] ] => destruct x; try t end.

Ltac t'' := unfold rep; fold rep'; sep simp_prem simplr.

Ltac t' := match goal with
             | [ |- _ ==> ?P ] =>
               match P with
                 | context[rep' (next _) _] =>
                   inhabiter; simp_prem;
                   intro_pure; simpl_prem ltac:(solve [ eauto ]); unintro_pure; canceler; t''
               end
             | _ => t''
           end.

Theorem lkup0 : forall ls k,
  lookup ls k = None -> ls = delete ls k.
 intros. induction ls. t. t. destruct a. destruct (eqK k k0). t. pose (IHls H). rewrite <- e. trivial. Qed.

Lemma lkpdel : forall m k, lookup (delete m k) k = None.
 intros. induction m. trivial. simpl. destruct a. destruct (eqK k k0). assumption. simpl. 
 destruct (eqK k k0). contradiction. assumption. Qed.

Ltac tx := match goal with | [ H : lookup ?ls ?n = None |- rep' ?x ?ls ==> rep' ?x (delete ?ls ?n) ] =>  rewrite <- (lkup0 ls n H) ; t end. 

(* Implementation ***************************************************)

  Open Scope stsepi_scope.

  Definition new : STsep __ (fun r => rep r nil).
    refine {{ New (@None ptr) }}; t. Qed.

  Definition free  p: STsep (rep p nil) (fun _:unit => __).
  intros; refine {{ Free p }}; t. Qed.

  Definition add: forall k v (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m * [lookup m k = None])
         (fun _:unit => m ~~ rep p ((k,v)::m)).
   intros. refine ( op <- ! p ;
                    n  <- New (node k v op) ;
                    {{ p ::= (Some n) }} ); t. Qed.

 (* Get           **********)

 Definition get' : forall (k: K) (hd: option ptr) (m: [list (prod K V)]), 
    STsep (m ~~ rep' hd m) (fun r => m ~~ [lookup m k = r] * rep' hd m).
  intro k.
  refine (Fix2
    (fun hd m => m ~~ rep' hd m)
    (fun hd m r => m ~~ [lookup m k = r] * rep' hd m)
    (fun self hd m =>  
      IfNull hd
      Then  {{ Return None }}
      Else  fn <- ! hd ;
            if eqK k (key fn) 
            then {{ Return (Some (value fn)) }} 
            else {{ self (next fn) (m ~~~ tail m)  <@> _  }})); pose lkup.
  (** TODO **)
  t'. t'. t'. t'. t'. t'. t'.
  Admitted.

  Definition get (k: K) (p: ptr) (m: [list (prod K V)]) :
    STsep (m ~~ rep p m)
          (fun r:option V => m ~~ rep p m * [lookup m k = r] ).
  intros; refine (hd <- !p;
                  {{ get' k hd m  <@> (p --> hd) }}); t. Qed.

 (* isEmpty         ********)

 Definition isEmpty: forall (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m) (fun r:bool => m ~~ rep p m * if r then [m = nil] else [m <> nil]).
   intros; refine ( ohd <- (p !! (fun ohd => m ~~ rep' ohd m))%stsep  ;
                    IfNull ohd 
                    Then  {{ Return true  }}
                    Else  {{ Return false }} ); t'. 
 Qed.

 (* Remove         *********)

Definition remove_pre' k ls prev pn cur n := 
 Exists t :@ list (K*V), prev --> pn * rep' (next n) t * 
(Exists v :@ V, [lookup ((key n, value n)::t) k = Some v] * [key n <> key pn] * 
   [ls = (key pn, value pn)::(key n, value n)::t] * [key pn <> k] *
   [next pn = Some cur] * [lookup ((key n, value n)::t) (key pn) = None] *
   [lookup t (key n) = None]).

Definition remove_pre k ls prev pn cur := (ls ~~ Exists n :@ Node, cur --> n * remove_pre' k ls prev pn cur n).

Definition remove_post k ls prev (pn:Node) (_:ptr) :=
(fun r:V => ls ~~ Exists pk :@ K, Exists pv :@ V, Exists x :@ list (prod K V), 
          [ls = (pk,pv) :: x] * rep' (Some prev) ((pk,pv)::(delete x k)) * [lookup x k = Some r]).

Definition remove_frame ls pn n k prev cur := Exists t :@ list (prod K V), [lookup t (key pn) = None] * 
  [ls = (key pn, value pn) :: (key n, value n) :: t]  * [k <> key n] * 
  [key pn <> key n] * prev --> node (key pn) (value pn) (Some cur).

Definition remove'' : forall k ls prev pn cur, STsep (remove_pre k ls prev pn cur) (remove_post k ls prev pn cur).             
intro k. refine (Fix4 (remove_pre k) (remove_post k)  
 (fun self ls prev pn cur =>        
  n <- (cur !! (fun n => ls ~~ remove_pre' k ls prev pn cur n))%stsep;
  if eqK k (key n)  
  then Free cur ;;
        prev ::= node (key pn) (value pn) (next n) ;;  
        {{ Return (value n) }}
  else IfNull (next n) As nt 
       Then  {{ !!! }} 
       Else {{ self (ls ~~~ tail ls) cur n nt <@> (ls ~~ remove_frame ls pn n k prev cur)  }})); 
unfold remove_pre; unfold remove_pre'; unfold remove_post; unfold remove_frame; pose lkup; pose lkup.
t. instantiate (1:=v1). t. t. t. t. t. t. t. t. fold rep'. erewrite <- lkup0; eauto.
t.
(** TODO **)
Admitted.


 Definition remove : forall k (p: t) (m: [list (prod K V)]),
                     STsep (m ~~ rep p m * Exists v :@ V, [lookup m k = Some v]) 
                (fun r:V => m ~~ rep p (delete m k) *     [lookup m k = Some r]).
 intros. refine ( 
  hdptr <- ! p ;
  IfNull hdptr 
  Then {{ !!! }} 
  Else hd <- (hdptr !! (fun hd => m ~~ Exists tl :@ list (prod K V), p --> Some hdptr * Exists v :@ V, [lookup m k = Some v] *
                                       [m = (key hd, value hd)::tl] * rep' (next hd) tl * [lookup tl (key hd) = None]))%stsep   ;
          if eqK k (key hd)
          then Free hdptr ;;
               p ::= next hd ;; 
               {{ Return (value hd) }}
          else IfNull (next hd) As nt 
               Then {{ !!! }}
               Else {{ remove'' k m hdptr hd nt <@> (m ~~ p --> Some hdptr * [head m = Some (key hd, value hd)] ) }}
  ); unfold remove_pre; unfold remove_pre'; unfold remove_post; pose lkup; pose lkup0; pose lkpdel.
(** TODO **)
Admitted.
(*
t. instantiate (1:=v0). t. t. instantiate (1:= v1). t. t'. t. t'. instantiate (1:=v0). t. t. instantiate (1:= v1). t.
t. t. t. t. t. t'. tx. sep fail auto. t'. t. t'. instantiate (1:=v0). t. t. Qed.
*)

 (* Replace        **********)

 Definition replace: forall k v (p: t) (m: [list (prod K V)]),
  STsep (m ~~             rep p m * Exists v0 :@ V,    [lookup m k = Some v0] )
        (fun r:V => m ~~  rep p ((k,v)::(delete m k)) * [lookup m k = Some r ]).
 intros. refine ( x <- remove k p m ;
                  add k v p (m ~~~ delete m k)  <@> (m ~~ [lookup m k = Some x]) ;;
                  {{ Return x }} ); pose lkup; pose lkup0; pose lkpdel. 
 sep fail auto. instantiate (1:=v0). t. t. t. t. t. t. Qed.

 (* Put           *********)

Definition put k v (p: t) (m: [list (prod K V)]):
   STsep (m ~~ rep p m)
         (fun r => m ~~ [lookup m k = r] * rep p ((k,v)::(delete m k))).
intros.
refine ( x <- get k p m ;
          (match x as x0 return STsep (m ~~ rep p m * [x =lookup m k] * [x = x0])
                                    (fun _:unit => m ~~ rep p (delete m k) * [x = lookup m k])  with
             | Some xx =>  z <- remove k p m <@> (m ~~ [Some xx =lookup m k] * [x = Some xx]) ;
                             {{ Return  tt  }}
            | None => {{  Return tt }} 
          end)  ;;
          add k v p (m ~~~ delete m k) <@> (m ~~ [x = lookup m k]) ;;
         {{ Return x }}
         ); pose lkup; pose lkpdel; pose lkup0; try solve [ t | t' | sep fail auto; symmetry in H; t'; tx ].
 sep fail auto. f. instantiate (1:=xx). t. t'. tx. Qed.

End JahobAssocList.

