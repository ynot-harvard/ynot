Require Import Ynot.
Require Import Ascii.
Require Import Stream.
Require Import Charset Parsec.
Require Import Arith.
Require Import String List.

Set Implicit Arguments.

Module Combinators.
  Import ParsecNotation.
  Import Parsec.

  (** whitespace **)
  Definition ws_class : CharClass AsciiCharset :=
    @Group AsciiCharset (" " :: "009" :: "011" :: "010" :: "012" :: "013" :: nil)%char.
  Definition tab : ascii := ascii_of_nat 9.
  Definition cr : ascii := ascii_of_nat 13.
  Definition lf : ascii := ascii_of_nat 10.

  Definition ws := 
    grec (fun V ws =>
              GTry ((gclass ws_class) _ ^ !!!!ws) @ (fun _ => tt)
          ||| (gclass ws_class) _                 @ (fun _ => tt))%grammar.

  Definition ws_p : parser_t ws.
    refine (gfix (fun (ws_p:parser_t ws) => 
                try ((class ws_class) ^ ws_p) @ (fun _ => tt)
            ||| (class ws_class)              @ (fun _ => tt)))%parser.
    gtac; apply (@SSatisfy AsciiCharset empvar unit).
  Qed.

  (** numbers **)
  (* A grammar for digits *)  
  Definition digit_class : CharClass AsciiCharset :=
    @Terminal AsciiCharset (ARange "0" "9")%char.

  Definition digit : Term AsciiCharset ascii  := gclass digit_class.

  (* A parser for digits *)
  Definition digit_p : parser_t digit := class digit_class.

  (* A grammar for numbers:  note that this computes the value of the number *)
  Definition digit_value (d : ascii) : nat := (nat_of_ascii d) - (nat_of_ascii "0"%char).

  Definition digits : Term AsciiCharset (list nat) :=
    grec (fun var digits =>
              GTry (digit _ ^ !!!!digits) @ (fun x => (digit_value (fst x)) :: snd x)
          ||| digit _                     @ (fun x => (digit_value x) :: nil))%grammar.
  Definition digits_p : parser_t digits.
    refine (
    gfix (fun nd : parser_t digits =>
               try (digit_p ^ nd) @ (fun x => (digit_value (fst x)) :: snd x)
           ||| digit_p            @ (fun x => (digit_value x) :: nil)))%parser.
    unfold digit,gsatisfy; gtac; apply (@SSatisfy AsciiCharset empvar (list nat) (lower AsciiCharset (DenoteClass digit_class)
           (In_CharClass_dec digit_class))). 
  Qed.

  Definition number : Term AsciiCharset nat :=
    fun var => @GMap _ var _ _ (fun x => fold_left (fun a x => 10 * a + x) x 0) (digits _).
  Definition number_p : parser_t number :=
    map (fun x => fold_left (fun a x => 10 * a + x) x 0) digits_p.

  (** strings **)
  Definition alpha_class : CharClass AsciiCharset :=
    @Terminal AsciiCharset (ARange "a" "z")%char.

  Definition Alpha_class : CharClass AsciiCharset :=
    @Terminal AsciiCharset (ARange "A" "Z")%char.

  Definition letter_class : CharClass AsciiCharset :=
    Union alpha_class Alpha_class.

  Definition letter : Term AsciiCharset ascii := gclass letter_class.
  Definition letter_p : parser_t letter := class letter_class.

  Definition str : Term AsciiCharset string :=
    grec (fun var str =>
              GTry (((letter _ ||| digit _) ^ !!!!str) @ (fun x => String (fst x) (snd x)))
          ||| (letter _ ||| digit _)                   @ (fun x => String x EmptyString))%grammar.

  Definition str_p : parser_t str.
    refine (gfix (fun p : parser_t str =>
          try (((letter_p ||| digit_p) ^ p) @ (fun x => String (fst x) (snd x)))
      ||| (letter_p ||| digit_p)            @ (fun x => String x EmptyString)))%parser.
    unfold letter, digit, unroll, grec, gsatisfy ; gtac ; apply (@SSatisfy AsciiCharset empvar string).
  Qed.

  (** combinators **)
(** TODO: I don't think this is possible to do b/c of the definition of unroll.
  Print GEpsilon.
  Definition many (T:Set) (cs: Charset) (t: Term cs T) : Term cs (list T) :=
    grec (fun var many =>
                GTry (t _ ^ !!!!many) @ (fun x => (fst x) :: (snd x))
            ||| (@GEpsilon _ _ _ nil))%grammar.
  Axiom p :forall (T:Set) (cs: Charset) (tg:Term cs T) (t:parser_t tg), parser_t (many tg).
  Definition many_p (T:Set) (cs: Charset) (tg:Term cs T) (t:parser_t tg) : parser_t (many tg).
    intros. Set Printing All.
    Eval compute in (@unroll cs (list T)
       (fun (var : Set -> Type) (many : var (list T)) =>
        @GAlt cs var (list T)
          (@GMap cs var (prod T (list T)) (list T)
             (fun x : prod T (list T) =>
              @cons T (@fst T (list T) x) (@snd T (list T) x))
             (@GTry cs var (prod T (list T))
                (@GCat cs var T (list T) (tg var) (GVar cs var (list T) many))))
          (@GEpsilon cs var (list T) (@nil T)))).


    pose   (gfix (fun p : parser_t (many tg) =>
                try (t ^ p) @ (fun x => (fst x) :: (snd x))
            ||| (% (@nil T))   @ (fun x => nil)))%parser.
**)

End Combinators.

Module Expressions.
  Import Combinators.
  Import ParsecNotation.
  
  (* A grammar for expressions that computes the result of evaluating the expression: 
     expr := number | expr + expr | expr - expr *)
(*
  Definition expr := 
    grec (fun V expr => 
               ws _ ^ number _ ^ ws _     @ (fun t => fst (snd t)) 
           ||| !!!!expr ^ #"+" ^ !!!!expr @ (fun t => fst t + (snd (snd t)))
           ||| !!!!expr ^ #"-" ^ !!!!expr @ (fun t => fst t - (snd (snd t))))%grammar.

  (* A parser for expressions *)
  Definition expr_p : parser_t expr.
    refine (gfix (fun (expr_p:parser_t expr) =>
                ws_p ^ number_p ^ ws_p @ (fun t => fst (snd t))
            ||| expr_p ^ #"+" ^ expr_p @ (fun t => fst t + (snd (snd t)))
            ||| expr_p ^ #"-" ^ expr_p @ (fun t => fst t - (snd (snd t))))%parser).
    repeat (unfold number, digits, digit, ws, gsatisfy ; gtac).
  Qed.
*)
  Definition prefix := 
    grec (fun V expr => 
              ws _ ^ number _ ^ ws _      @ (fun t => fst (snd t)) 
           ||| #"+" ^ !!!!expr ^ !!!!expr @ (fun t => fst (snd t) + (snd (snd t)))
           ||| #"-" ^ !!!!expr ^ !!!!expr @ (fun t => fst (snd t) - (snd (snd t))))%grammar.

  (* A parser for expressions *)
  Definition prefix_p : parser_t prefix.
    refine (gfix (fun (expr_p:parser_t prefix) =>
               ws_p ^ number_p ^ ws_p  @ (fun t => fst (snd t))
            ||| #"+" ^ expr_p ^ expr_p @ (fun t => fst (snd t) + (snd (snd t)))
            ||| #"-" ^ expr_p ^ expr_p @ (fun t => fst (snd t) - (snd (snd t))))%parser).
    repeat (progress (unfold number, digits, digit, ws, gsatisfy ; gtac)); apply (@SSatisfy AsciiCharset empvar nat). 
  Qed.
End Expressions.