(* Copyright (c) 2008, Harvard University
 * All rights reserved.
 *
 * Author: Greg Morrisett
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
Require Import Arith.
Require Import Omega.
Set Implicit Arguments.

Open Local Scope stsep_scope.
Open Local Scope hprop_scope.

Section Array.

(*************************************************************************)

(* arrays are an abstract type *)
Parameter array : Set.
(* with an operation that returns the length *)
Parameter array_length : array -> nat.  

(* The array_plus operation is intended for specifications only, hence the 
 * return type of [ptr].  We want to rule out the possibility of doing this
 * pointer arithmetic at run-time, so that a garbage collector won't have
 * track interior pointers.  But this causes many headaches below...
 *)
Parameter array_plus : array -> nat -> [ptr].

(* The assumed operations on arrays -- note that operations such as sub and upd
 * only require that the location being manipulated point to something. *)

(* Create a new array of size n.  Notice that the array contents are not yet initialized. *)
Parameter new_array : forall (n:nat),
                        STsep __ (fun (a:array) => 
                                    [array_length a = n] *
                                    iter_sep
                                      (fun i => p :~~ array_plus a i in p -->? ) 0 n).

(* Destroy an array.  Note that the caller can't destroy part of the array. *)
Parameter free_array : forall (a:array),
                        STsep (iter_sep (fun i => p :~~ array_plus a i in p -->? ) 0 
                                         (array_length a))
                              (fun (_:unit) => __).

(* Read index i from the array.  This is similar to the ref-read in ST *)
Parameter sub_array : forall (A:Type)(a:array)(i:nat)(P : A -> hprop),
                        STsep (p :~~ array_plus a i in 
                                Exists v :@ A, p --> v * P v)
                              (fun (v:A) => 
                                p :~~ array_plus a i in p --> v * P v).

(* Update location a[i] with value v.  Note that this supports a strong update in
 * the sense that the type of v does not have to be the same as the old value in a[i].
 * In addition, note that this allows us to have arrays whose contents hold different
 * types of values at different indices. 
 *)
Parameter upd_array : forall (A:Type)(a:array)(i:nat)(v:A),
                        STsep (p :~~ array_plus a i in 
                                 Exists B :@ Set, Exists w :@ B, p --> w)
                              (fun (_:unit) => 
                                p :~~ array_plus a i in p --> v).
End Array.
