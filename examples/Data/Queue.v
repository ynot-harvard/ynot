(* Copyright (c) 2008, Harvard University
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

Module Type QUEUE.
  Parameter t : Set -> Set.
  Parameter rep : forall T, t T -> list T -> hprop.

  Parameter new : forall T,
    STsep __ (fun q : t T => rep q nil).
  Parameter free : forall T (q : t T),
    STsep (rep q nil) (fun _ : unit => __).

  Parameter enqueue : forall T (q : t T) (x : T) (ls : [list T]),
    STsep (ls ~~ rep q ls) (fun _ : unit => ls ~~ rep q (ls ++ x :: nil)).
  Parameter dequeue : forall T (q : t T) (ls : [list T]),
    STsep (ls ~~ rep q ls) (fun xo => ls ~~ match xo with
                                              | None => [ls = nil] * rep q ls
                                              | Some x =>
                                                match ls with
                                                  | nil => [False]
                                                  | x' :: ls' => [x' = x] * rep q ls'
                                                end
                                            end).
End QUEUE.

Module Queue : QUEUE.
  Section Queue.
    Variable T : Set.

    Record node : Set := Node {
      data : T;
      next : option ptr
    }.
    
    Fixpoint listRep (ls : list T) (hd tl : ptr) {struct ls} : hprop :=
      match ls with
        | nil => [hd = tl]
        | h :: t => Exists p :@ ptr, hd --> Node h (Some p) * listRep t p tl
      end.

    Record queue : Set := Queue {
      front : ptr;
      back : ptr
    }.

    Definition rep' ls fr ba :=
      match fr, ba with
        | None, None => [ls = nil]
        | Some fr, Some ba => Exists ls' :@ list T, Exists x :@ T,
          [ls = ls' ++ x :: nil] * listRep ls' fr ba * ba --> Node x None
        | _, _ => [False]
      end.
          
    Definition rep q ls := (Exists fr :@ option ptr, Exists ba :@ option ptr,
      front q --> fr * back q --> ba * rep' ls fr ba).

    Ltac simplr := repeat (try congruence;
      match goal with
        | [ x : option ptr |- _ ] => destruct x
        | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
        | [ H : nil = ?ls ++ _ :: nil |- _ ] => destruct ls; discriminate
      end);
    eauto.

    Lemma rep_nil : forall q,
      rep q nil ==> front q --> (@None ptr) * back q --> (@None ptr).
      unfold rep; sep fail simplr.
    Qed.

    Lemma app_nil_middle : forall (x1 x2 : T),
      x1 :: x2 :: nil = x1 :: nil ++ x2 :: nil.
      reflexivity.
    Qed.

    Lemma app_nil_middle' : forall (x1 x2 x3 : T) ls,
      x1 :: x2 :: ls ++ x3 :: nil = x1 :: (x2 :: ls) ++ x3 :: nil.
      reflexivity.
    Qed.

    Lemma list_cases : forall ls : list T,
      ls = nil
      \/ (exists x, ls = x :: nil)
      \/ (exists x1, exists ls', exists x2, ls = x1 :: ls' ++ x2 :: nil).
      Hint Immediate app_nil_middle app_nil_middle'.

      induction ls; simpl; firstorder; subst; eauto 6.
    Qed.

    Lemma app_inj_tail' : forall (x1 : T) ls' x2 v v0,
      x1 :: ls' ++ x2 :: nil = v ++ v0 :: nil
      -> x1 :: ls' = v /\ x2 = v0.
      intros; apply app_inj_tail; assumption.
    Qed.

    Implicit Arguments app_inj_tail' [x1 ls' x2 v v0].

    Lemma rep'_Some1 : forall ls fr ba,
      rep' ls (Some fr) ba
      ==> Exists nd :@ node, fr --> nd
      * Exists ls' :@ list T, [ls = data nd :: ls']
      * match next nd with
          | None => [ls' = nil]
          | Some fr' => rep' ls' (Some fr') ba
        end.
      Ltac list_simplr := repeat (simplr ||
        match goal with
          | [ ls' : list T |- _ ] =>
            match goal with
              | [ |- context[ ([_ :: _ = ls' ++ _ :: nil] * listRep ls' _ _) ] ] => destruct ls'
            end

          | [ |- context[[nil = _ ++ _ :: _]] ] =>
            inhabiter; search_prem ltac:(apply himp_inj_prem); intro
          | [ |- context[[_ :: _ ++ _ :: _ = _ ++ _ :: _]] ] =>
            inhabiter; search_prem ltac:(apply himp_inj_prem); intro

          | [ H : _ |- _ ] => generalize (app_inj_tail' H); clear H; intuition; subst; simpl
        end).

      destruct ba; simpl; [ | sep fail idtac ];
        generalize (list_cases ls); intuition; subst;
          repeat match goal with
                   | [ H : ex _ |- _ ] => destruct H
                 end;
          sep fail list_simplr.
    Qed.

    Lemma rep'_Some2 : forall ls o1 ba,
      rep' ls o1 (Some ba) ==> Exists ls' :@ list T, Exists x :@ T, Exists fr :@ ptr,
        [ls = ls' ++ x :: nil] * [o1 = Some fr] * listRep ls' fr ba * ba --> Node x None.
      unfold rep'; sep fail simplr.
    Qed.

    Ltac simp_prem :=
      idtac;
      simpl_prem ltac:(apply rep_nil ||
        match goal with
          | [|- rep' _ (Some _) _ ==> _] => apply rep'_Some1
          | [|- rep' _ _ (Some _) ==> _] => apply rep'_Some2
        end).

    Ltac t := unfold rep; simpl_IfNull; sep simp_prem simplr.
    
    Open Scope stsepi_scope.

    Definition new : STsep __ (fun q => rep q nil).
      refine (fr <- New (@None ptr);
        ba <- New (@None ptr);
        {{Return (Queue fr ba)}}); t.
    Qed.

    Lemma rep'_nil : __ ==> rep' nil None None.
      t.
    Qed.

    Hint Resolve rep'_nil.

    Definition free : forall q, STsep (rep q nil) (fun _ : unit => __).
      intros; refine (Free (front q);;
        {{Free (back q)}}); t.
    Qed.

    Lemma push_listRep : forall ba x nd ls fr,
      ba --> Node x (Some nd) * listRep ls fr ba ==> listRep (ls ++ x :: nil) fr nd.
      Hint Resolve himp_comm_prem.

      induction ls; t.
    Qed.

    Hint Immediate push_listRep.

    Lemma push_nil : forall (x : T) nd,
      __ ==> [x :: nil = nil ++ x :: nil] * listRep nil nd nd.
      t.
    Qed.

    Hint Immediate push_nil.
    Definition enqueue : forall q x ls, STsep (ls ~~ rep q ls) (fun _ : unit => ls ~~ rep q (ls ++ x :: nil)).
      intros; refine (ba <- !back q;
        nd <- New (Node x None);
        back q ::= Some nd;;

        IfNull ba Then
          {{front q ::= Some nd}}
        Else    
          ban <- !ba;
          ba ::= Node (data ban) (Some nd);;
          {{Return tt}}); t.
    Qed.

    Definition dequeue : forall q ls,
      STsep (ls ~~ rep q ls) (fun xo => ls ~~ match xo with
                                                | None => [ls = nil] * rep q ls
                                                | Some x =>
                                                  match ls with
                                                    | nil => [False]
                                                    | x' :: ls' => [x' = x] * rep q ls'
                                                  end
                                              end).
      intros; refine (fr <- !front q;

        IfNull fr Then
          {{Return None}}
        Else
          nd <- !fr;
          Free fr;;
          front q ::= next nd;;

          IfNull next nd As nnd Then
            back q ::= @None ptr;;
            {{Return (Some (data nd))}}
          Else    
            {{Return (Some (data nd))}}); t.
    Qed.
  End Queue.

  Definition t (_ : Set) := queue.
End Queue.
