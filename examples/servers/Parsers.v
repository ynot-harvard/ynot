Require Import Ynot.
Require Import Ascii.
Require Import Stream.
Require Import Charset Parsec ParsecCombinators.
Require Import Arith.
Require Import String List.

Module Expressions.
  Import Combinators.
  Import ParsecNotation.
  
  (* A grammar for expressions that computes the result of evaluating the expression: 
     expr := number | expr + expr | expr - expr *)
  Definition expr := 
    grec (fun V expr => 
              ws _ ^ number _ ^ ws _   @ (fun t => fst (snd t)) 
           ||| !!!!expr ^ #"+" ^ !!!!expr     @ (fun t => fst t + (snd (snd t)))
           ||| !!!!expr ^ #"-" ^ !!!!expr     @ (fun t => fst t - (snd (snd t))))%grammar.

  (* A parser for expressions *)
  Definition expr_p : parser_t expr.
    refine (gfix (fun (expr_p:parser_t expr) =>
                ws_p ^ number_p ^ ws_p @ (fun t => fst (snd t))
            ||| expr_p ^ #"+" ^ expr_p @ (fun t => fst t + (snd (snd t)))
            ||| expr_p ^ #"-" ^ expr_p @ (fun t => fst t - (snd (snd t))))%parser).
    repeat (unfold number, digits, digit, ws, gsatisfy ; gtac).
  Qed.

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
    repeat (unfold number, digits, digit, ws, gsatisfy ; gtac).
  Qed.
End Expressions.