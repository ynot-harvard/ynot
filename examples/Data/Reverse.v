(* Copyright (c) 2009, Harvard University
 * All rights reserved.
 *
 * Author: Adam Chlipala
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

Require Import List.

Require Import Ynot.

Set Implicit Arguments.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.


Module Type LIST.
  Parameter t : Set.
  Parameter rep : forall T : Set, t -> list T -> hprop.

  Parameter Nil : forall (T : Set),
    STsep __ (fun t => rep t (@nil T)).
  Parameter Cons : forall (T : Set) (ls : [list T]) (x : T) (v : t),
    STsep (ls ~~ rep v ls) (fun v' => ls ~~ rep v' (x :: ls)).

  Parameter Rev : forall (T : Set) (ls : [list T]) (v : t),
    STsep (ls ~~ rep v ls) (fun v' => ls ~~ rep v' (rev ls)).
End LIST.

Module List : LIST.
  Section List.
    Definition t := option ptr.
    Variable T : Set.

    Record node : Set := Node {
      head : T;
      tail : t
    }.

    Fixpoint rep (v : t) (ls : list T) {struct ls} : hprop :=
      match v, ls with
        | None, nil => [True]
        | Some p, x :: ls' => Exists v' :@ t,
          p --> Node x v' * [ls = x :: ls'] * rep v' ls'
        | _, _ => [False]
      end.

    Ltac t' := sep fail idtac.

    Lemma rep_None : forall ls,
      rep None ls ==> [ls = nil].
      destruct ls; t'.
    Qed.

    Lemma rep_Some : forall p ls,
      rep (Some p) ls ==> Exists x :@ T, Exists ls' :@ list T, Exists p' :@ option ptr,
      [ls = x :: ls'] * p --> Node x p' * rep p' ls'.
      destruct ls; t'.
    Qed.

    Ltac simplr :=
      simpl_IfNull;
      repeat simpl_prem ltac:(apply rep_None || apply rep_Some).

    Definition Tail (ls : list T) :=
      match ls with
        | nil => nil
        | _ :: ls' => ls'
      end.

    Lemma rev_Tail : forall (ls : list T) x ls',
      ls = x :: Tail ls
      -> rev (Tail ls) ++ x :: ls' = rev ls ++ ls'.
      intros; match goal with
                | [ H : _ |- _ ] => rewrite H
              end;
      simpl; rewrite app_ass; reflexivity.
    Qed.
    
    Hint Rewrite rev_Tail using assumption : Rev.

    Ltac t := sep simplr ltac:(autorewrite with Rev).

    Definition Nil : STsep __ (fun t => rep t (@nil T)).
      refine {{Return None}}; t.
    Qed.

    Definition Cons : forall (ls : [list T]) (x : T) (v : t),
      STsep (ls ~~ rep v ls) (fun v' => ls ~~ rep v' (x :: ls)).
      intros; refine (p <- New (Node x v);
        {{Return (Some p)}}); t.
    Qed.

    Definition Rev' : forall (lsX lsY : [list T]) (x y : t),
      STsep (lsX ~~ lsY ~~ rep x lsX * rep y lsY)
      (fun v => lsX ~~ lsY ~~ rep v (rev lsX ++ lsY)).
      refine (Fix4
        (fun lsX lsY x y => lsX ~~ lsY ~~ rep x lsX * rep y lsY)
        (fun lsX lsY _ _ v => lsX ~~ lsY ~~ rep v (rev lsX ++ lsY))
        (fun self lsX lsY x y =>
          IfNull x Then
            {{Return y}}
          Else
            nd <- !x;
            x ::= Node (head nd) y;;
            {{self (lsX ~~~ Tail lsX) (lsY ~~~ head nd :: lsY)
              (tail nd) (Some x)
              <@> (lsX ~~ [lsX = head nd :: Tail lsX]) }})); t.
    Qed.

    Hint Rewrite <- app_nil_end : Rev.

    Definition Rev : forall (ls : [list T]) (v : t),
      STsep (ls ~~ rep v ls) (fun v' => ls ~~ rep v' (rev ls)).
      intros; refine {{Rev' ls [nil] v None}}; t.
    Qed.

  End List.
End List.
