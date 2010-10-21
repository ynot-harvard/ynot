(* Copyright (c) 2008, Harvard University
 * All rights reserved.
 *
 * Authors: Adam Chlipala, Avi Shinnar
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

Require Import Separation.

Section ocase.
  Variables A B : Type.

  Variable disc : option A.

  Variable NoneCase : disc = None -> B.
  Variable SomeCase : forall v, disc = Some v -> B.

  Definition ocase :=
    match disc as disc' return (disc = disc' -> B) with
      | None => NoneCase
      | Some v => SomeCase _
    end (refl_equal _).
End ocase.

Implicit Arguments ocase [A B].

Notation "'IfNull' x 'Then' e1 'Else' e2" :=
  (ocase x (fun _ => e1) (fun x _ => e2))
  (no associativity, at level 90).
Notation "'IfNull' e 'As' x 'Then' e1 'Else' e2" :=
  (ocase e (fun _ => e1) (fun x _ => e2))
  (no associativity, at level 90).

Ltac simpl_IfNull :=
  repeat match goal with
           | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intro H; try (rewrite H in *; clear H)
           | [ H : ?p = None |- _ ] => rewrite H; mark_existential p
           | [ H : ?p = Some _ |- _ ] => rewrite H; mark_existential p
         end.

Section natcase.
  Variables B : Type.

  Variable disc : nat.

  Variable ZCase : disc = O -> B.
  Variable SCase : forall v, disc = S v -> B.

  Definition natcase :=
    match disc as disc' return (disc = disc' -> B) with
      | O => ZCase
      | S v => @SCase v 
    end (refl_equal _).
End natcase.

Implicit Arguments natcase [B].

Arguments Scope natcase [].
Notation "'IfZero' x 'Then' e1 'Else' e2" :=
  (natcase x (fun _ => e1) (fun x _ => e2))
  (no associativity, at level 90).
Notation "'IfZero' e 'As' x 'Then' e1 'Else' e2" :=
  (natcase e (fun _ => e1) (fun x _ => e2))
  (no associativity, at level 90).
Arguments Scope natcase [type_scope nat_scope _ _].