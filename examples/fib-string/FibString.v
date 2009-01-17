(* Copyright (c) 2008, Harvard University
 * All rights reserved.
 *
 * Author: Ryan Wisnesky, Gregory Malecha
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
Require Import Basis.
Require Import List.
Require Import String.

Open Local Scope string_scope.
Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.

Definition fib : nat -> STsep (__) (fun _ : string => __).
  intro y.
  refine (Fix
    (fun _ => hprop_empty)
    (fun _ _ => hprop_empty)
    (fun self x =>
      match x with
        | 0 =>   {{ Return "a" }}
        | S 0 => {{ Return "a" }}
        | S (S z) => a <- self z; 
                     b <- self (S z);
                     {{Return (a ++ b)}}
      end)
      y);
  sep fail auto.
Qed.

Definition main : STsep (__) (fun _:unit => __).
   refine (
     z <- fib 4 ;
     printStringLn z);
   sep fail auto.
Qed. 
  

 
