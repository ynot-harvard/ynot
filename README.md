ynot
====

The Ynot Project source code. (http://ynot.cs.harvard.edu/)

Ynot is a library for the Coq proof assistant which turns it into a full-fledged environment for writing and verifying
imperative programs. In the tradition of the Haskell IO monad, Ynot axiomatizes a parameterized monad of imperative
computations, where the type of a computation tells you not only what type of data it returns, but also what
Hoare-logic-style precondition and postcondition it satisfies. On top of the simple axiomatic base, the library defines
a separation logic. Specialized automation tactics are able to discharge automatically most proof goals about
separation-style formulas that describe heaps, meaning that building a certified Ynot program is often not much harder
than writing that program in Haskell.

Ynot makes it easy to enhance its automation with support for new predicates describing new data structures, and, since
all such enhancements must be proved from first principles, extensibility does not require users to trust more code. All
of Coq's traditional theorem-proving tools are available by default as well. Thus, Ynot enables effective proof-based
software engineering, from simple memory safety of low-level imperative programs to deep correctness theorems about
programs like compilers that may use imperative data structures for efficiency.

The Ynot project is supported in part by NSF Grant 0702345, entitled Collaborative Research: Integrating Types and
Verification, by NSF Grant 0910660, entitled Combining Foundational and Lightweight Formal Methods to Build Certifiably
Dependable Software, and by a gift from Microsoft Research.

Disclaimer
----------

Ynot is no longer actively supported by the developers. The last release we made got it running on Coq 8.3pl2 with the
relational database from the POPL'10 paper.

Other's have already contributed to the project and we welcome patches.

If you are actively using the codebase and/or are interested in contributing to it, please email gmalecha@gmail.com and
we can see if we can give you commit permissions.
