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
