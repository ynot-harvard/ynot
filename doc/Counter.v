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

(** remove printing * *)

(** %\chapter{Mutable Counters}% *)

(** Our first example is trivial, designed to introduce the main features of Ynot.  We will implement imperative natural number counters.  First, we import the Ynot library. *)

Require Import Ynot.

(** For this to work, the compiled Ynot modules must be in the module path.  Those modules can be compiled simply by running %\texttt{%#<tt>#make#</tt>#%}% in the root directory of the Ynot distribution.  In a batch build of a file like the one we are writing here, the path to the Ynot library may be specified like:
%\begin{verbatim}%#<pre>#
coqc -R /path/to/ynot/src Ynot Counter.v
#</pre>#%\end{verbatim}%

For interactive Emacs development with Proof General, it is useful to add a variable setting like this in your %\texttt{%#<tt>#.emacs#</tt>#%}% file.
%\begin{verbatim}%#<pre>#
(custom-set-variables
 '(coq-prog-args '("-R" "/path/to/ynot/src" "Ynot"))
 )
#</pre>#%\end{verbatim}%

With such a setting, you should be able to execute the [Require Import] line without complaint.  Afterward, we open a notation scope, to enable use of concise notations for assertions about heaps. *)

Open Local Scope hprop_scope.

(** Next, we write a module signature that defines the ADT (abstract data type) of mutable counters. *)

Module Type COUNTER.
  Parameter t : Set.
  Parameter rep : t -> nat -> hprop.

  (** A counter has type [t].  In ML, an abstract type within a module usually enforces proper usage implicitly, where the set of values that may be constructed is limited strategically through the choice of which methods to export.  With mutable data structures in Ynot, this regime will not generally be enough.  Instead, we employ an additional design pattern of %\emph{%#<i>#representation predicates#</i>#%}%, as illustrated by [rep] in this example.  A representation predicate takes a value of the ADT as an argument, and it usually also takes one or more other values that stand for %\emph{%#<i>#a pure functional model#</i>#%}% of the imperative value.  The type [hprop] stands for predicates over heaps.  Thus, for a counter [c] and its pure functional model [n], [rep c n] stands for the set of heaps that are consistent with the assumption that [c] represents [n].

     We see these parameters in use in the type of the counter [new] operation. *)

  Parameter new : STsep __ (fun c : t => rep c 0).

  (** This type uses the [STsep] type family, our main parameterized monad.  The two explicit arguments are a precondition and a postcondition for this method, in the tradition of Hoare logic.  The precondition [__] describes an empty heap, and the postcondition [fun c => rep c 0] says that, if method execution terminates with a counter [c], then [c] represents 0 in the final heap.
     
     The name [STsep] alludes to the foundation of this type family in %\emph{%#<i>#separation logic#</i>#%}%, following the %\emph{%#<i>#small footprint#</i>#%}% approach to specification.  The [new] method does not actually require that the heap be empty when the method is called.  Rather, the pre- and postconditions only specify the method's effects on %\emph{%#<i>#the part of the heap that the method touches#</i>#%}%.  We will see later how this property can be put to use in verification.

     The [free] method has a similar type, but it uses one new feature. *)

  Parameter free : forall (c : t) (n : [nat]), STsep (n ~~ rep c n) (fun _ : unit => __).

  (** We write the type [nat] in brackets to indicate that that method argument is %\emph{%#<i>#computationally irrelevant#</i>#%}%.  That is, [n] is a so-called "ghost state" argument, used only to help us prove the correctness of this method.  The compiled version of this program will not contain [n].  In the precondition of [free], we use the notation [n ~~ p], where [p] is an [hprop] that may mention spec variable [n].  Each spec variable that an assertion uses must be unpacked explicitly in this way.

     The type of the method for reading a counter's value introduces two more new assertion constructs. *)

  Parameter get : forall (c : t) (n : [nat]), STsep (n ~~ rep c n)
    (fun n' => n ~~ rep c n * [n' = n]).

  (** In the postcondition, we see a sub-assertion [[n' = n]].  This is a lifted pure proposition; the assertion is true whenever [n' = n] and the heap is empty.  We combine that pure assertion with [rep c n] using the %\emph{%#<i>#separating comjunction#</i>#%}% [*].  An assertion [p * q] is true for heap [h] whenever [h] can be split into two disjoint pieces [h1] and [h2], such that [h1] satisfies [p] and [h2] satisfies [q].

     Now the type of the counter increment method should be unsurprising. *)

  Parameter inc : forall (c : t) (n : [nat]), STsep (n ~~ rep c n)
    (fun _ : unit => n ~~ rep c (S n)).
End COUNTER.

(** We can implement a module ascribing to this signature.  Since the types of the methods include specifications, we know that any implementation is correct, up to the level of detail that we included in the signature. *)

Module Counter : COUNTER.
  Definition t := ptr.
  Definition rep (p : t) (n : nat) := p --> n.

  (** We represent a counter with the [ptr] type.  Unlike ML ref types, Ynot pointer types don't carry information on the types of data that they point to.  Rather, we rely on typed points-to facts within assertions.  We see an example in the definition of [rep]: a counter-pointer [p] represents a number [n] if [p] points to heap memory containing [n].

     Since our method types contain specifications, we will need to do some proving to define the methods.  We define a simple tactic [t] that is able to dispatch all of the proof obligations we will encounter. *)

  Ltac t := unfold rep; sep fail idtac.

  (** We replace uses of [rep] by unfolding its definition, and we call the [sep] tactic from the Ynot library.  [sep] is intended as a separation logic version of Coq's [intuition] tactic, which simplifies formulas of constructive propositional logic.  We have no theoretical completeness guarantees for [sep], but usage patterns are roughly the same.  Just as [intuition] takes an optional argument giving a tactic to apply in solving leaves of its proof search, [sep] takes two domain-specific tactics as arguments.  In later examples, we will see more interesting choices for those tactics.

     Before we begin programming, we open another scope, this time to let us write ML-like syntax for Ynot programs. *)

  Open Scope stsepi_scope.

  (** We implement the [new] method by %\emph{%#<i>#declaring it as a proof search goal#</i>#%}%, so that we can use tactics to discharge the obligations that we will generate. *)

  Definition new : STsep __ (fun c => rep c 0).
    refine {{New 0}}; t.
  Qed.

  (** The [refine] tactic is the foundation of our implementation.  In general, [refine] takes a term with holes in it, solving the current goal and adding the types of the holes as subgoals.  There are holes in the term we pass to [refine] in defining [new], but they are hidden by the Ynot syntax extensions.  We write double braces around a Ynot program to indicate simultaneous strengthening of the precondition and weakening of the postcondition.  We chain our tactic [t] onto the [refine], so that [t] is applied to discharge every subgoal.

     It is instructive to see exactly which subgoals are being proved for us. *)

  Definition new' : STsep __ (fun c => rep c 0).
    refine {{New 0}}.
    (** [[

2 subgoals
  
  ============================
   __ ==> ?504 * __
        ]] *)

    (** [[
subgoal 2 is:
 forall v : ptr, ?504 * v --> 0 ==> rep v 0
        ]]

        The first subgoal corresponds to strengthening the precondition; we see an implication between our stated precondition and the precondition that Coq inferred.  We are trying to write a function with precondition [__], while Coq has figured out that our implementation could actually be given any precondition.  That fact shows up in the form of the second assertion, which is a unification variable conjoined with the empty heap, which is logically equivalent to that unification variable alone.

        The same unification appears to the left of an implication in the second subgoal, which comes from weakening the postcondition.  Where [v] is the method return value, we must show that any heap with some unknown part and some part containing just a mapping of [v] to [0] can be described by the appropriate instance of [rep].  In our automated script above, the unification variable had already been determined to be [__] by this point, so that this goal can be proved by reflexivity of implication.

        For the rest of this and the other examples, we won't show the obligations that are generated.  You will no doubt need to inspect such obligations in writing your own Ynot programs, so it may be useful to play with the proof scripts in this tutorial, to see which obligations are generated and experiment with manual means of discharging them. *)

  Abort.

  (** The remaining method definitions are (perhaps surprisingly) quite straightforward.  We use ML-style operators for working with pointers, writing prefix [!] for reading and infix [::=] for writing.  We use Haskell-style [<-] notation for the monad "bind" operator. *)

  Definition free : forall c n, STsep (n ~~ rep c n) (fun _ : unit => __).
    intros; refine {{Free c}}; t.
  Qed.

  Definition get : forall c n, STsep (n ~~ rep c n) (fun n' => n ~~ rep c n * [n' = n]).
    intros; refine {{!c}}; t.
  Qed.
  
  Definition inc : forall c n, STsep (n ~~ rep c n) (fun _ : unit => n ~~ rep c (S n)).
    intros; refine (
      n' <- !c;
      {{c ::= S n'}}
    ); t.
  Qed.
End Counter.
