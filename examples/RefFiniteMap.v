(*******************************************************************)
(* A trivial implementation of the FINITE_MAP interface where we   *)
(* use a ref to an association list.                               *)
(*******************************************************************)

Require Import Ynot.
Require Import Examples.FiniteMap.
Set Implicit Arguments.

Module RefAssocList(Assoc:ASSOCIATION) : FINITE_MAP with Module A := Assoc.
  Open Local Scope hprop_scope.

  Module AT <: FINITE_MAP_AT with Module A:=Assoc.
    Module A := Assoc.
    Module AL := AssocList(Assoc). Import AL.
    Definition fmap_t := ptr.
    Definition rep(x:fmap_t)(y:alist_t) := Exists y' :@ alist_t, (x --> y') * [distinct y] * [Permutation y y'].
  End AT.

  Module T:=FINITE_MAP_T(Assoc)(AT).
  Module A := T.A.
  Module AL := T.AL.

  Import AT AL.
  Open Local Scope stsepi_scope.

  Ltac s := T.unfm_t; intros.

Ltac sep' tac :=
  let s := repeat progress (simpler; tac; try search_prem premer) in
    let concer := apply himp_empty_conc
      || apply himp_ex_conc_trivial
        || (apply himp_ex_conc; econstructor)
          || (eapply himp_unpack_conc; [eassumption || reflexivity |])
            || (apply himp_inj_conc; [s; fail | idtac]) in
              (intros; equater || specFinder; tac;
                repeat match goal with
                         | [ x : inhabited _ |- _ ] => dependent inversion x; clear x
                       end;
                intros; s;
                  repeat ((
                    search_prem ltac:(idtac;
                      search_conc ltac:(apply himp_frame || (apply himp_frame_cell; trivial))) || search_conc concer);
                  s);
                  try finisher).
  Ltac t := unfold rep; sep' ltac:(subst; eauto).

  Definition new : T.new. s;
    refine ({{New nil_al}})
  ; t. Defined.

  Definition free : T.free. s;
    refine ({{Free x}})
  ; t. Defined.

  Definition lookup : T.lookup. s;
    refine (z <- ! x ; 
            {{Return (lookup k z)}}) ; t. rewrite (lookup_dis_perm k H1); t.
  Defined.

  Definition insert :  T.insert. s;
    refine (z <- ! x ;
            {{x ::= ((k,, v):: (remove k z))}})
  ; t. Defined.

  Definition remove : T.remove. s;
    refine (z <- ! x ;
            {{x ::= (remove k z)}})
  ; t. Defined.

  Lemma perm : T.perm. s; t. Qed.
  Lemma distinct : T.distinct. s; t. Qed.

End RefAssocList.
