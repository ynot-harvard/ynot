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

Require Examples.Stack.
Module S := Examples.Stack.Stack.

Open Scope hprop_scope.
Open Scope stsepi_scope.

Set Implicit Arguments.

Definition iter (A : Set) (spec : list A -> hprop)
  (F : forall (x : A) (ls : list A), STsep (spec ls) (fun _ : unit => spec (x :: ls)))
  (ls : list A)
  : STsep (spec nil) (fun _ : unit => spec ls).
  do 3 intro.
  refine (fix self (ls : list A) : STsep (spec nil) (fun _ : unit => spec ls) :=
    match ls return STsep (spec nil) (fun _ : unit => spec ls) with
      | nil => {{Return tt}}
      | x :: ls' =>
        self ls';;
        F x ls'
    end); sep fail idtac.
Defined.

Open Scope inhabited_scope.

Definition stackFromList (A : Set) (ls : list A)
  : STsep __ (fun s : S.t A => S.rep s ls).
  intros; refine (s <- S.new _;
    iter (fun ls => S.rep s ls)
         (fun x ls => {{S.push s x [ls]}})
         ls;;
    {{Return s}}); sep fail idtac.
Qed.
