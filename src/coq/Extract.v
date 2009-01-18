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

Extraction Language Ocaml.

(** Standard Extractions **)
Require Import List.
Require Import String.

Extract Inductive unit    => "unit" [ "()" ].
Extract Inductive bool    => "bool" [ "true" "false" ]. 
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list    => "list" [ "[]" "(::)" ].
Extract Inductive string  => "MlCoq.ascii list" [ "[]" "(::)" ].

(** ST Extractions **)
Require Import Ynot.

Extract Constant ST "'t" => " 't STImpl.axiom_ST ".  

Extract Constant STBind       => "STImpl.axiom_STBind".
Extract Constant STReturn     => "STImpl.axiom_STReturn".
Extract Constant STContra     => "STImpl.axiom_STContra".
Extract Constant STWeaken     => "STImpl.axiom_STWeaken".
Extract Constant STStrengthen => "STImpl.axiom_STStrengthen".
Extract Constant STNew        => "STImpl.axiom_STNew".
Extract Constant STFree       => "STImpl.axiom_STFree".
Extract Constant STRead       => "STImpl.axiom_STRead".
Extract Constant STWrite      => "STImpl.axiom_STWrite".
Extract Constant STFix        => "STImpl.axiom_STFix".


(** Heap Extractions (Ptr) **)

Extract Constant axiom_ptr        => "HeapImpl.axiom_ptr".

Extract Constant axiom_ptr_eq_dec => "HeapImpl.axiom_ptr_eq_dec".

(** Library Extraction **)
Require Import Basis.

Extract Constant printString    => "BasisImpl.axiom_printString".
Extract Constant printStringLn  => "BasisImpl.axiom_printStringLn".
Extract Constant printString'   => "BasisImpl.axiom_printString".
Extract Constant printStringLn' => "BasisImpl.axiom_printStringLn".

(** Basic Types Extraction **)
Require Ascii.

Extract Inductive Ascii.ascii => "MlCoq.ascii" [ "MlCoq.Ascii" ].
Extract Inductive nat => "MlCoq.nat" [ "MlCoq.O" "MlCoq.S" ].

Extract Inlined Constant Bool.bool_dec => "(=)".
Extract Inlined Constant Ascii.ascii_dec => "(=)".