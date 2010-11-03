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

Module BinaryTree.
 
 (* The modelling type is a binary tree. *)
 Fixpoint btree (A : Set) (n: nat) : Set :=
   match n with
     | 0 => A
     | S n' => prod (btree A n') (btree A n')
   end.

End BinaryTree.

Module Type BINOMIAL_TREE.

 Module BT := BinaryTree.
 Import BT.

 Require Export Ynot.
 Open Scope hprop_scope.
 Open Scope stsepi_scope.

 Parameter A   : Set.

 Parameter t   : Set.
 Parameter rep : forall n, btree A n -> t -> hprop.

 Parameter new : forall (a: A), STsep __ (rep O a).
 
 Parameter free: forall p, 
   STsep (Exists a :@ A, rep O a p) (fun _:unit => __).

 Parameter asbtree: forall n (bt: [btree A n]) p, 
   STsep (bt ~~ rep n bt p) (fun r => bt ~~ rep n bt p * [r = bt]).

 Parameter merge: forall p1 p2 n (bt1 bt2: [btree A n]), 
   STsep (bt1 ~~ bt2 ~~ rep n bt1 p1 * rep n bt2 p2)
         (fun r:unit => bt1 ~~ bt2 ~~ rep (S n) (bt1, bt2) p2).

 Parameter split: forall n (bt: [btree A (S n)]) p,
  STsep (bt ~~ rep (S n) bt p)
        (fun r => bt ~~ rep n (snd bt) p * rep n (fst bt) r). 

End BINOMIAL_TREE.

Module BinomialTree : BINOMIAL_TREE.
 Module BT := BinaryTree.
 Import BT.
 Require Export Ynot.

 Parameter A: Set.

 Open Scope hprop_scope.
 Open Scope stsepi_scope.

 (* Representation *)

 Definition t := ptr.

(*  A binomial tree is defined recursively:
     - a tree of order 0 is a single node
     - a tree of order k has a root node whose children are
       roots of binomial trees of orders k-1, k-2... 1, 0,
       in this order. *)

 Fixpoint bltree (n: nat) : Set :=
   match n with
     | 0 => A
     | S n' => prod ptr (bltree n')
   end.

  Notation "'kids'" := snd.
  Notation "'head'" := fst. 

  Fixpoint rep' n :      btree A n -> bltree n -> hprop :=
   match n   as n return btree A n -> bltree n -> hprop with
    | O    => fun a a' => [a = a']
    | S n' => fun bt bl => rep' n' (kids bt) (kids bl) * 
                Exists bl' :@ bltree n', head bl --> bl' * rep' n' (head bt) bl'
   end.  

  Definition rep (n: nat) (bt: btree A n) (p: ptr) : hprop :=
    Exists bl :@ bltree n, p --> bl * rep' n bt bl.
 
 (* Reasoning *)

  Ltac simplr := unfold rep; unfold rep'; try match goal with 
                                     | [ h : (?a, ?b) = (?c, ?d) |- _ ] => 
                                       let y := fresh "y" in 
                                       let z := fresh "z" in 
                                         assert (a = c); try congruence; subst;  
                                         assert (b = d); try congruence; subst; clear h 
                                   end; simpl in *.
 Ltac t := solve [ repeat (simplr; sep fail auto) | match goal with [n: nat |- _ ] => destruct n; repeat (simplr; sep fail auto) end].
 Ltac f := fold rep'; fold rep. 

(* Implementation *)

 Definition new : forall hd, STsep __ (rep O hd).
  intros. refine ( {{ New hd }} ). sep fail auto. t. Qed. 

 Definition free p : STsep (Exists a :@ A, rep O a p) (fun _:unit => __).
  intros. refine ( Assert (Exists a :@ A, p --> a) ;; 
                   {{ Free p }}); t. Qed.

(* Merging is attaching one tree as the leftmost child of the other.
   This spec, which updates in place, requires strong update, because the type
   of the node changes (it increases by one level) *) 
Definition merge : forall p1 p2 n (bt1 bt2: [btree A n]), 
 STsep (bt1 ~~ bt2 ~~ rep n bt1 p1 * rep n bt2 p2)
       (fun r:unit => bt1 ~~ bt2 ~~ rep (S n) (bt1, bt2) p2).
 intros p1 p2. refine (fun n bt1 bt2 => 
   oldp2node <- ! p2 ;
   Assert (bt1 ~~ bt2 ~~ rep n bt1 p1 * p2 --> oldp2node * rep' n bt2 oldp2node) ;;                  
   {{ p2 ::= (p1, oldp2node) }} ); t. Qed.

(* had to use SepRead here *)
Definition split: forall n (bt: [btree A (S n)]) p,
  STsep (bt ~~ rep (S n) bt p)
        (fun r => bt ~~ rep n (snd bt) p * rep n (fst bt) r). 
 refine (fun n bt p => bl <- (p !! (fun bl => bt ~~ rep' (S n) bt bl))%stsep  ;  
                       p ::= kids bl ;;
                       {{ Return (head bl) }}); t. Qed.

(* n is not computationally irrelevent *)

(* had to use SepRead here *)
Definition asbtree' : forall n (bt: [btree A n]) (bl: bltree n),
  STsep (bt ~~ rep' n bt bl) (fun r => bt ~~ rep' n bt bl * [r = bt]).
refine (fix F (n: nat) {struct n} : forall bt bl, STsep (bt ~~ rep' n bt bl) (fun r => bt ~~ rep' n bt bl * [r = bt]) :=
          match n as n return       forall (bt: [btree A n]) (bl: bltree n), STsep (bt ~~ rep' n bt bl) (fun r => bt ~~ rep' n bt bl * [r = bt])  with 
              | O    => fun bt bl => {{ SepReturn bl <@> _  }}
              | S n' => fun bt bl => x   <- ((head bl) !! (fun (x:bltree n') => bt ~~ rep' n' (kids bt) (kids bl)* rep' n' (head bt) x))%stsep ;      
                                     bth <- F n' (bt ~~~ head bt) x         <@> (bt ~~ head bl --> x * rep' n' (kids bt) (kids bl))   ; 
                                     btk <- F n' (bt ~~~ kids bt) (kids bl) <@> (bt ~~ head bl --> x * rep' n' (head bt) x * [bth = head bt])  ;
                                     {{ SepReturn (bth, btk) <@> _ }} 

            end); t. Qed.

Definition asbtree n (bt: [btree A n]) (p: ptr) : 
  STsep (bt ~~ rep n bt p) (fun r: btree A n => bt ~~ rep n bt p * [r = bt]).
 intros. refine ( x <- ! p;
                  {{ asbtree' n bt x <@> p --> x }} ); t. Qed.

End BinomialTree.
