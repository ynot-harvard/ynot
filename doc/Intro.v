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

(** %\fi

\begin{document}

\maketitle

\chapter{Introduction}% *)

(** Ynot is a library for the Coq proof assistant.  Besides supporting mathematical theorem proving, Coq natively supports general functional programming, as its logic is an ML-like programming language.  To preserve logical consistency, Coq's language Gallina rules out non-termination and side effects.  Ynot adds those features in a controlled way, so that programs may be impure, while proofs remain pure and logically meaningful.  Ynot goes further, combining the new impure constructs with a Hoare-style logic for proving the correctness of programs, including support for reasoning in the style of separation logic.

   The basic approach stands in direct analogy with the way in which imperative features were added to Haskell.  Haskell's IO monad reifies imperative programs as data that may be constructed by pure programs.  Purity and referential transparency are preserved, as some system outside the scope of the language is responsible for "running" IO values.  The situation is the same in Ynot.  We define an indexed monad of impure programs, via uninterpreted Coq axioms.  Coq's extraction facility can be used to translate programs that use these axioms into OCaml, Haskell, or Scheme programs.  In these languages, the axioms can be realized via standard implementations of IO-style monads.

   The Ynot library is designed to support effective engineering of certified programs.  We include tactics that are able to automate much of reasoning about mutable heaps.  Within that general framework, the user can plug in his own domain-specific tactics.

   We will present the basics of the Ynot library through a series of examples.  We assume that the reader is already familiar with programming and proving in Coq.  There are a number of possible sources for this backround knowledge, including this draft textbook by the author of this tutorial:
   %\begin{center}\url{http://adam.chlipala.net/cpdt/}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/">http://adam.chlipala.net/cpdt/</a></tt></blockquote># *)
