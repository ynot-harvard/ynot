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
