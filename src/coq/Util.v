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

Set Implicit Arguments.


Theorem push_and_ex : forall P T (P' : T -> Prop),
  (exists x, P /\ P' x)
  -> P /\ ex P'.
  firstorder.
Qed.


Ltac not_eq e1 e2 :=
  match e1 with
    | e2 => fail 1
    | _ => idtac
  end.
Ltac equate e1 e2 := not_eq e1 e2; let H := fresh in assert (H : e1 = e2); [reflexivity | clear H].


Notation "[ T ]" := (inhabited T) (at level 0, T at level 200) : type_scope.
Notation "[ v ]" := (inhabits v) (at level 0, v at level 200) : inhabited_scope.
Bind Scope inhabited_scope with inhabited.
Delimit Scope inhabited_scope with inhabited.


Ltac hdestruct x := let y := fresh in (dependent inversion x as [y]; clear x; rename y into x; destruct x).

Ltac meta_fail x :=
  match x with
    | x => idtac
    | _ => fail 1
  end.

Ltac goal_meta_fail := match goal with |- ?T => meta_fail T end.

Ltac dest_conj :=
  match goal with
    H : _ /\ _ |- _ => let H1 := fresh H "l" in
      let H2 := fresh H "r" in
        destruct H as [H1 H2]
  end.

Ltac dest_exists :=
  match goal with
    H : exists x : _, _ |- _ => 
      let x' := fresh x in
      destruct H as [x' H]
  end.

Definition block {A : Type} (a : A) := a.
