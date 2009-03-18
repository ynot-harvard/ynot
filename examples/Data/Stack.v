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


Module Type STACK.
  Parameter t : Set -> Set.
  Parameter rep : forall T, t T -> list T -> hprop.

  Parameter new : forall T,
    STsep __ (fun s : t T => rep s nil).
  Parameter free : forall T (s : t T),
    STsep (rep s nil) (fun _ : unit => __).

  Parameter push : forall T (s : t T) (x : T) (ls : [list T]),
    STsep (ls ~~ rep s ls) (fun _ : unit => ls ~~ rep s (x :: ls)).
  Parameter pop : forall T (s : t T) (ls : [list T]),
    STsep (ls ~~ rep s ls) (fun xo => ls ~~ match xo with
                                              | None => [ls = nil] * rep s ls
                                              | Some x => Exists ls' :@ list T, [ls = x :: ls'] * rep s ls'
                                            end).
End STACK.

Module Stack : STACK.
  Section Stack.
    Variable T : Set.

    Record node : Set := Node {
      data : T;
      next : option ptr
    }.

    Fixpoint listRep (ls : list T) (hd : option ptr) {struct ls} : hprop :=
      match ls with
        | nil => [hd = None]
        | h :: t => match hd with
                      | None => [False]
                      | Some hd => Exists p :@ option ptr, hd --> Node h p * listRep t p
                    end
      end%hprop.

    Definition stack := ptr.

    Definition rep q ls := (Exists po :@ option ptr, q --> po * listRep ls po)%hprop.

    Ltac simplr := try discriminate.

    Theorem listRep_None : forall ls,
      listRep ls None ==> [ls = nil].
      destruct ls; sep fail idtac.
    Qed.

    Theorem listRep_Some : forall ls hd,
      listRep ls (Some hd) ==> Exists h :@ T, Exists t :@ list T, Exists p :@ option ptr,
        [ls = h :: t] * hd --> Node h p * listRep t p.
      destruct ls; sep fail ltac:(try discriminate).
    Qed.

    Ltac simp_prem :=
      simpl_IfNull;
      simpl_prem ltac:(apply listRep_None || apply listRep_Some).

    Ltac t := unfold rep; sep simp_prem simplr.
    
    Open Scope stsepi_scope.

    Definition new : STsep __ (fun s => rep s nil).
      refine {{New (@None ptr)}}; t.
    Qed.

    Definition free : forall s, STsep (rep s nil) (fun _ : unit => __).
      intros; refine {{Free s}}; t.
    Qed.

    Definition push : forall s x ls, STsep (ls ~~ rep s ls) (fun _ : unit => ls ~~ rep s (x :: ls)).
      intros; refine (hd <- !s;
        nd <- New (Node x hd);
        {{s ::= Some nd}}
      ); t. 
    Qed.

    Definition pop : forall s ls,
      STsep (ls ~~ rep s ls) (fun xo => ls ~~ match xo with
                                                | None => [ls = nil] * rep s ls
                                                | Some x => Exists ls' :@ list T, [ls = x :: ls'] * rep s ls'
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

  Definition t (_ : Set) := stack.
End Stack.
