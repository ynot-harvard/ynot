(* Copyright (c) 2009, Harvard University
 * All rights reserved.
 *
 * Authors: Gregory Malecha, Ryan Wisnesky
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

Require Import Ynot.STsep.
Require Import Ynot.Hprop.

Require Import String.
Require Import List.
Require Import Ascii.

Open Local Scope hprop_scope.

(** String <-> List Conversion **)
Fixpoint str2la (str : string) : list ascii :=
  match str with
    | EmptyString => nil
    | String a b => a :: (str2la b)
  end.

Fixpoint la2str (la : list ascii) : string :=
  match la with
    | nil => EmptyString
    | a :: b => String a (la2str b)
  end.

Theorem str2la_inv_la2str : forall str, la2str (str2la str) = str.
  induction str; [ auto | simpl; rewrite IHstr; trivial ].
Qed.

Theorem la2str_inv_str2la : forall str, str2la (la2str str) = str.
  induction str; [ auto | simpl; rewrite IHstr; trivial ].
Qed.

(** Standard "println" **)
Axiom printString : forall (s : string),
  STsep (__) (fun _:unit => __).

Definition printStringLn (s : string) :
  STsep (__) (fun _:unit => __) :=
  printString (s ++ (String "010"%char (String "013"%char ""%string))).

Definition printString' (s : list ascii) :
  STsep (__) (fun _:unit => __) :=
  printString (la2str s).

Definition printStringLn' (s : list Ascii.ascii) :
  STsep (__) (fun _:unit => __) :=
  printStringLn (la2str s).

(** Numbers -> Strings **)

Open Local Scope char_scope.

Definition dd n :=
  match n with
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
    | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
    | _ => "x"
  end.

 Fixpoint div_mod_10 (a q : nat) {struct a} :=
   match a with
     | 0 => (q,0)
     | 1 => (q,1)
     | 2 => (q,2)
     | 3 => (q,3)
     | 4 => (q,4)
     | 5 => (q,5)
     | 6 => (q,6)
     | 7 => (q,7)
     | 8 => (q,8)
     | 9 => (q,9)
     | S (S (S (S (S (S (S (S (S (S n))))))))) => div_mod_10 n (S q)
   end.

 Fixpoint ntos (x : nat) (n : nat) (l : list ascii) {struct x} :=
   match n with
     | 0 => match l with
              | nil => "0" :: l
              | _ => l
            end
     | _ => let (q,r) := div_mod_10 n 0 in
       match x with
         | 0 => "t" :: "o" :: "o" ::" " :: "b" :: "i" :: "g" :: nil
         | S x' => ntos x' q (dd r :: l)
       end
   end.
