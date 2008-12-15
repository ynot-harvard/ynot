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

Module Counter : COUNTER.
  Definition t := ptr.
  Definition rep (p : t) (n : nat) := (p --> n)%hprop.

  Ltac t := unfold rep; sep fail idtac.

  Open Scope stsepi_scope.

  Definition new : STsep __ (fun c => rep c 0).
    refine {{New 0}}; t.
  Qed.

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
