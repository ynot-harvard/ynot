Require Import List.
Require Import Sumbool.

Set Implicit Arguments.

(** General character sets **)

Record Charset : Type := mkCharset {
  char : Set;
  char_eq : forall (c1 c2 : char), {c1 = c2} + {c1 <> c2};

  (** Character classes generalize the literal class to make some things easier, e.g.
     [a-z] or [0-9]
   **)
  CharClassTerminal : Set;
  DenoteTerminal : CharClassTerminal -> char -> Prop ;
  in_dec : forall (cl : CharClassTerminal) (c : char), {DenoteTerminal cl c} + {~DenoteTerminal cl c}
}.

Inductive CharClass (cs : Charset) : Set :=
| All   : CharClass cs
| Empty : CharClass cs
| Singleton : (char cs) -> CharClass cs
| Group : list (char cs) -> CharClass cs
| Terminal : (CharClassTerminal cs) -> CharClass cs
| Complement : CharClass cs -> CharClass cs
| Union : CharClass cs -> CharClass cs -> CharClass cs
| Intersection : CharClass cs -> CharClass cs -> CharClass cs.

Fixpoint DenoteClass (cs: Charset) (cl: CharClass cs) (c: char cs) {struct cl} : Prop :=
  match cl with
    | All => True
    | Empty => False
    | Singleton c' => c' = c
    | Group grp => In c grp
    | Terminal term => DenoteTerminal cs term c
    | Complement cl' => ~DenoteClass cl' c
    | Union c1 c2 => DenoteClass c1 c \/ DenoteClass c2 c
    | Intersection c1 c2 => DenoteClass c1 c /\ DenoteClass c2 c
  end.

Definition In_CharClass_dec (cs : Charset) : forall (cl : CharClass cs) (c : (char cs)), {DenoteClass cl c} + {~DenoteClass cl c}.
  refine (fix In_CharClass_dec (cl : CharClass cs) (c : char cs) : {DenoteClass cl c} + {~DenoteClass cl c} :=
    match cl as cl return {DenoteClass cl c} + {~DenoteClass cl c} with
      | All => left _ _
      | Empty => right _ _
      | Singleton c' => if char_eq cs c c' then left _ _ else right _ _
      | Group lc' => if In_dec (char_eq cs) c lc' then left _ _ else right _ _
      | Terminal t => if @in_dec cs t c then left _ _ else right _ _
      | Complement cl => if In_CharClass_dec cl c then right _ _ else left _ _
      | Union c1 c2 => 
        if In_CharClass_dec c1 c then left _ _ else if In_CharClass_dec c2 c then left _ _ else right _ _
      | Intersection c1 c2 =>
        if In_CharClass_dec c1 c then if In_CharClass_dec c2 c then left _ _ else right _ _ else right _ _
    end); simpl; auto; try tauto.
Qed.

(** Ascii Character Set **)
Require Import String Ascii.
Require Import Compare_dec Omega.
Inductive AsciiTerminal : Set :=
| ARange : ascii -> ascii -> AsciiTerminal.

Definition AsciiDenoteTerminal (t: AsciiTerminal) (c:ascii) : Prop :=
  match t with
    | ARange a b => (nat_of_ascii a) <= (nat_of_ascii c) /\ (nat_of_ascii c) <= (nat_of_ascii b)
  end.

Definition AsciiTerminalIn_dec : forall (t : AsciiTerminal) (c : ascii), {AsciiDenoteTerminal t c} + {~AsciiDenoteTerminal t c}.
  refine (fun t c =>
  match t as t return {AsciiDenoteTerminal t c} + {~AsciiDenoteTerminal t c} with
    | ARange a b =>
      if le_lt_dec (nat_of_ascii a) (nat_of_ascii c) then
        if le_lt_dec (nat_of_ascii c) (nat_of_ascii b)
          then left _ _
          else right _ _ 
        else right _ _
  end); simpl; omega.
Qed.

Definition AsciiCharset : Charset :=
  @mkCharset ascii ascii_dec AsciiTerminal AsciiDenoteTerminal AsciiTerminalIn_dec.