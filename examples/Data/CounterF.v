(* Copyright (c) 2008, Harvard University
 * All rights reserved.
 *
 * Author: Adam Chlipala and Avi Shinnar
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

Require Import Ynot.
Require Import Qcanon.
 
Set Implicit Arguments.

Local Open Scope hprop_scope.

Module Type COUNTER.
  Parameter t : Set.
  Parameter rep : perm -> t -> nat -> hprop.

  Parameter new : STsep __ (fun c => rep top c 0).
  Parameter free : forall c n, STsep (n ~~ rep top c n) (fun _ : unit => __).
  Parameter get : forall q c n, STsep (q ~~ n ~~ rep q c n) (fun n' => q ~~ n ~~ rep q c n * [n' = n]).
  Parameter inc : forall c n, STsep (n ~~ rep top c n) (fun _ : unit => n ~~ rep top c (S n)).
  Parameter psplit : forall c n q1 q2, q1 |#| q2 -> rep (q1+q2) c n ==> rep q1 c n * rep q2 c n.
  Parameter pjoin : forall c n q1 q2, q1 |#| q2 -> rep q1 c n * rep q2 c n ==> rep (q1+q2) c n.
End COUNTER.

Module Counter : COUNTER.
  Definition t := ptr.
  Definition rep (q:perm) (p : t) (n : nat) := (p -[q]-> n)%hprop.

  Ltac t := unfold rep; sep fail simpl.

  Open Scope stsepi_scope.

  Definition new : STsep __ (fun c => rep 0 c 0).
    refine {{New 0}}%nat; t.
  Qed.

  Definition free : forall c n, STsep (n ~~ rep 0 c n) (fun _ : unit => __).
    intros; refine {{Free c}}; t.
  Qed.

  (* TODO: this q should be infered *)
  Definition get : forall q c n, STsep (q ~~ n ~~ rep q c n) (fun n' => q ~~ n ~~ rep q c n * [n' = n]).
    intros; refine {{![q]c}}; t.
  Qed.
  
  Definition inc : forall c n, STsep (n ~~ rep 0 c n) (fun _ : unit => n ~~ rep 0 c (S n)).
    intros; refine (
      n' <- ! c;
      {{c ::= S n'}}
    ); t.
  Qed.

  Definition psplit : forall c n q1 q2, q1 |#| q2 -> rep (q1+q2) c n ==> rep q1 c n * rep q2 c n.
  Proof.
    t. apply himp_cell_split; auto.
  Qed.

  Definition pjoin : forall c n q1 q2, q1 |#| q2 -> rep q1 c n * rep q2 c n ==> rep (q1+q2) c n.
  Proof.
    t. apply himp_cell_join; auto.
  Qed.
 
End Counter.
