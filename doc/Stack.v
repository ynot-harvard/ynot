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

(** remove printing * *)

(** %\chapter{Mutable Stacks}% *)

(** Our next example demonstrates one of the simplest imperative data structures that really deserves the name: polymorphic mutable stacks. *)

Require Import List.
Require Import Ynot.
Set Implicit Arguments.
Open Local Scope hprop_scope.


Module Type STACK.
  Parameter t : Set -> Set.
  Parameter rep : forall T, t T -> list T -> hprop.

  (** Compared to the [COUNTER] example, our new type [t] differs in being polymorphic in the type of data that we store.  The representation predicate is parameterized similarly, and we set the convention that the functional model of a [T] stack is a [T] list.

     The first three stack methods don't involve any new concepts. *)

  Parameter new : forall T : Set,
    Cmd __ (fun s : t T => rep s nil).
  Parameter free : forall (T : Set) (s : t T),
    Cmd (rep s nil) (fun _ : unit => __).

  Parameter push : forall (T : Set) (s : t T) (x : T) (ls : [list T]),
    Cmd (ls ~~ rep s ls) (fun _ : unit => ls ~~ rep s (x :: ls)).

  (** The type of the [pop] method demonstrates two important patterns.  First, we can use arbitrary Coq computation in calculating a precondition or postcondition.  Our [pop] method returns an [option T], which will be [None] when the stack is empty.  We use Coq's standard [match] expression form to case-analyze this return value, returning a different assertion for each case.  The [Some] case uses an [hprop] version of the standard existential quantifier. *)

  Parameter pop : forall (T : Set) (s : t T) (ls : [list T]),
    Cmd (ls ~~ rep s ls)
    (fun xo : option T => ls ~~ match xo with
                                  | None => [ls = nil] * rep s ls
                                  | Some x => Exists ls' :@ list T, [ls = x :: ls']
                                              * rep s ls'
                                end).
End STACK.

Module Stack : STACK.

  (** We use Coq's section mechanism to scope the type variable [T] over all of our definitions. *)

  Section Stack.
    Variable T : Set.

    (* We will represent stacks as singly-linked lists.  A node of a linked list consists of a data value and an optional pointer to the next node.  We use [option] types rather than baking in a concept of "null pointers." *)

    Record node : Set := Node {
      data : T;
      next : option ptr
    }.

    (** We can use a recursive [hprop]-valued function to define what it means for a particular list to be represented in the heap, starting from a particular head pointer. *)

    Fixpoint listRep (ls : list T) (hd : option ptr) {struct ls} : hprop :=
      match ls with
        | nil => [hd = None]
        | h :: t => match hd with
                      | None => [False]
                      | Some hd => Exists p :@ option ptr, hd --> Node h p * listRep t p
                    end
      end.

    (** As in the [Counter] example, we represent a stack as an untyped pointer, and we rely on the [rep] predicate to enforce proper typing of associated heap cells. *)

    Definition stack := ptr.
    Definition rep q ls := Exists po :@ option ptr, q --> po * listRep ls po.

    (** We define a tactic that will be useful for domain-specific goal simplification.  In larger examples, such a tactic definition would probably be significantly longer.  Here, we only need to ask Coq to try solving goals by showing that they are contradictory, because two equated values of a datatype are built from different constructors. *)

    Ltac simplr := try discriminate.

    (** A key component of effective Ynot automation is the choice of appropriate domain-specific %\emph{%#<i>#unfolding lemmas#</i>#%}%.  Such a lemma characterizes how an application of a representation predicate may be decomposed, when something is known about the structure of the arguments.  Our first simple unfolding lemma says that any functional list represented by a null pointer must be nil.  [sep] can complete the proof after we begin with a case analysis on the list. *)

    Theorem listRep_None : forall ls, listRep ls None ==> [ls = nil].
      destruct ls; sep fail idtac.
    Qed.

    (** A slightly more complicated lemma characterizes the shape of a list represented by a non-null pointer.  Here we put our [simplr] tactic to use as the second argument to [sep].  In general, the tactic given as that second argument is tried throughout proof search, in attempts to discharge goals that the separation logic simplifier can't prove alone. *)

    Theorem listRep_Some : forall ls hd,
      listRep ls (Some hd) ==> Exists h :@ T, Exists t :@ list T, Exists p :@ option ptr,
        [ls = h :: t] * hd --> Node h p * listRep t p.
      destruct ls; sep fail simplr.
    Qed.

    (** With these lemmas available, we are ready to define a tactic that will be passed as the first argument to [sep].  The tactic in that position is used to simplify the goal before beginning the main proof search.  The tactic [simp_prem] will perform that function for us. *)

    Ltac simp_prem :=
      simpl_IfNull;
      simpl_prem ltac:(apply listRep_None || apply listRep_Some).

    (** The [simpl_IfNull] tactic comes from the Ynot library.  It simplifies goal patterns that arise from a syntax extension that we will see shortly.  The more interesting part of [simp_prem] is the call to [simpl_prem], another tactic from the library.  [simpl_prem t] looks for premises (sub-formulas on the left of implications) that can be simplified by the tactic [t].  Here, we try to simplify by applying either of our unfolding lemmas.

       With these pieces in place, we define a final [t] solver tactic by dropping our two parameters into the version that we used for [Counter]. *)

    Ltac t := unfold rep; sep simp_prem simplr.
    
    Open Scope stsepi_scope.

    (** The first three method definitions are quite simple and use no new concepts. *)

    Definition new : Cmd __ (fun s => rep s nil).
      refine {{New (@None ptr)}}; t.
    Qed.

    Definition free : forall s, Cmd (rep s nil) (fun _ : unit => __).
      intros; refine {{Free s}}; t.
    Qed.

    Definition push : forall s x ls, Cmd (ls ~~ rep s ls) (fun _ : unit => ls ~~ rep s (x :: ls)).
      intros; refine (hd <- !s;
        nd <- New (Node x hd);
        {{s ::= Some nd}}
      ); t.
    Qed.

    (** The definition of [pop] introduces the [IfNull] syntax extension.  An expression [IfNull x Then e1 Else e2] expands to a test on whether the variable [x] of some [option] type is null.  If [x] is [None], then the result is [e1].  If [x] is [Some y], then the result is [e2], with all occurrences of [x] replaced by [y]. *)

    Definition pop : forall s ls,
      Cmd (ls ~~ rep s ls)
      (fun xo => ls ~~ match xo with
                         | None => [ls = nil] * rep s ls
                         | Some x => Exists ls' :@ list T, [ls = x :: ls']
                                     * rep s ls'
                       end).
      intros; refine (hd <- !s;

        IfNull hd Then
          {{Return None}}
        Else
          nd <- !hd;
          Free hd;;
          s ::= next nd;;
          {{Return (Some (data nd))}}); t.
    Qed.
  End Stack.

  (** Finally, since the signature makes the type [t] polymorphic, we define a trivial wrapper that discards the type paramter. *)

  Definition t (_ : Set) := stack.
End Stack.
