(* Copyright (c) 2009, Harvard University
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

(** %\chapter{Compilation}% *)

(** In an ideal world, we would have a specialized compiler from Coq to native code.  More than one research group is working towards that goal today.  For now, we can compile Ynot developments to reasonably efficient binaries using Coq's extraction mechanism.  Some examples distributed with Ynot show how to do this, via extraction to OCaml, the primary extraction language supported by Coq.  OCaml's type system is much less expressive than Coq's, so some Coq programs will not be translated to valid OCaml programs, but Ynot developments that avoid Coq's more arcane features are likely to be handled properly.

   The basic extraction mechanism already does most of the work for us.  We just need to craft build infrastructures around it, including uses of Coq's extraction hints, to map particular Coq identifiers to particular OCaml identifiers.  This is especially necessary to realize the primitive program constructs of Ynot.  These constructs must remain as axioms in Coq, since it is impossible to write imperative programs directly.  Nonetheless, we achieve a consistent final result by instructing Coq to extract them as particular impure OCaml functions.  The Ynot distribution includes in the %\texttt{%#<tt>#src/ocaml/#</tt>#%}% directory such an implementation of the primitives that we need.

   The "Hello World" example in %\texttt{%#<tt>#examples/hello-world/#</tt>#%}% demonstrates how to build a program that uses IO, and the %\texttt{%#<tt>#linked-list#</tt>#%}% example demonstrates use of an imperative linked list ADT.  In this tutorial, we will not go into detail on how the build process works, since it involves no theoretically deep elements.  You can re-use our Makefiles to produce new programs to be compiled via OCaml by copying the simple file structure used for %\texttt{%#<tt>#hello-world#</tt>#%}%.

   %\begin{itemize}%#<ul>#
   %\item%#<li># %\texttt{%#<tt>#HelloWorld.v#</tt>#%}%, the Ynot development#</li>#
   %\item%#<li># %\texttt{%#<tt>#Extract.v#</tt>#%}%, the Coq code to generate an OCaml equivalent#</li>#
   %\item%#<li># %\texttt{%#<tt>#Makefile#</tt>#%}%, which defines some example-specific variables and calls out to a shared Makefile#</li>#
   %\item%#<li># %\texttt{%#<tt>#ocaml/main.ml#</tt>#%}%, which gives the OCaml code to run for the final program, calling the main entry point from the extracted development#</li>#
   #</ul>#%\end{itemize}%

   In a directory set up like this, running %\texttt{%#<tt>#make#</tt>#%}% builds only the Coq parts, and running %\texttt{%#<tt>#make build#</tt>#%}% generates the final executable.  The latter target produces a native code executable %\texttt{%#<tt>#main.native#</tt>#%}% and a bytecode version %\texttt{%#<tt>#main.byte#</tt>#%}%. *)
