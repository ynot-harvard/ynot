(* Copyright (c) 2008, Harvard University
 * All rights reserved.
 *
 * Author: Gregory Malecha
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
Require Import Data.LinkedListSeg.
Require Import Ascii.
Require Import List.

Open Local Scope char_scope.
Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.

Definition CharLL := HeapLinkedListSeg ascii.

Definition llseg := @llseg ascii CharLL.
Definition nil_empty := @nil_empty ascii CharLL.
Definition cons := @LinkedListSeg.cons ascii CharLL.
Definition empty := @LinkedListSeg.empty ascii CharLL.
Definition append := @LinkedListSeg.append ascii CharLL.

Hint Resolve nil_empty.
Hint Resolve pack_injective.
Opaque LinkedListSeg.llseg.

Ltac unify' :=
  search_conc ltac:(idtac;match goal with
                            | [ |- _ ==> LinkedListSeg.llseg ?X _ _ * _ ] =>
                              search_prem ltac:(idtac;match goal with
                                                        | [ |- LinkedListSeg.llseg X _ _ * _ ==> _ ] => 
                                                          eapply himp_frame; eauto
                                                      end)
                          end).

Ltac tac :=
  solve [ unfold llist; intros; inhabiter; unpack_conc; sep fail auto
        | sep fail auto
        | unfold llist; intros; inhabiter; unpack_conc; sep fail auto;
          try match goal with
                | [ |- _ ==> llseg' None None ?X ] => equate X (@nil ascii)
              end;
          unify';
          sep fail auto ].

Definition main : STsep (__) (fun _:unit => __).
   refine (
     hello <- empty ;
     hello <- cons " " hello [None] _;
     hello <- cons "o" hello [None] _;
     hello <- cons "l" hello [None] _;
     hello <- cons "l" hello [None] _;
     hello <- cons "e" hello [None] _;
     hello <- cons "h" hello [None] _;

     world <- empty  <@> _;
     world <- cons "!" world [None] _ <@> _;
     world <- cons "d" world [None] _ <@> _;
     world <- cons "l" world [None] _ <@> _;
     world <- cons "r" world [None] _ <@> _;
     world <- cons "o" world [None] _ <@> _;
     world <- cons "w" world [None] _ <@> _;

     hello_world <- append hello world _ _ <@> _;
     
     str <- elements  hello_world _ _;
     printStringLn' (str) <@> _;;
     hello_world <- freeList  hello_world None _;
     {{Return tt}}
   );
   tac.
Qed.
