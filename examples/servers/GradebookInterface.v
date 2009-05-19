Require Import Ynot Basis.
Require Import Ascii String Stream.
Require Import Parsec Charset.
Require Import Arith.
Require Import GradebookApp.
Require Import Parsers.

Set Implicit Arguments.

Module GradebookParser.
  Import ParsecCombinators.Combinators.
  Import ParsecNotation.

(**
  (* A grammar for digits *)  
  Definition is_digit(c:ascii):bool := 
    if le_lt_dec (nat_of_ascii "0"%char) (nat_of_ascii c) then
      (if le_lt_dec (nat_of_ascii c) (nat_of_ascii "9"%char) then true else false)
    else false.

  Definition digit : Term ascii  := gsatisfy is_digit.

  (* A parser for digits *)
  Definition digit_p : parser_t digit := satisfy is_digit.

  (** grammar for letters **)
  Definition is_alpha(c:ascii) : bool :=
    if le_lt_dec (nat_of_ascii "a"%char) (nat_of_ascii c) then 
      (if le_lt_dec (nat_of_ascii c) (nat_of_ascii "z"%char) then true else false)
    else false.

  Definition is_Alpha(c:ascii) : bool :=
    if le_lt_dec (nat_of_ascii "A"%char) (nat_of_ascii c) then 
      (if le_lt_dec (nat_of_ascii c) (nat_of_ascii "Z"%char) then true else false)
    else false.

  Definition is_letter(c:ascii) : bool := if (is_alpha c) then true else (is_Alpha c).

  Definition letter : Term ascii := gsatisfy is_letter.
  Definition letter_p : parser_t letter := satisfy is_letter.


  Definition tab : ascii := ascii_of_nat 9.
  Definition cr : ascii := ascii_of_nat 13.
  Definition lf : ascii := ascii_of_nat 10.

  Definition crlf : Term unit :=
    fun _ => (# cr ^ #lf @ (fun _ => tt))%grammar.
  
  Definition crlf_p : parser_t crlf.
    refine ((# cr ^ #lf @ (fun _ => tt)))%parser.
  Qed.    
**)

  Export GradebookModel.

  Definition id : Term AsciiCharset string := str.
  Definition id_p : parser_t id := str_p.

  Definition pass : Term AsciiCharset string := str.
  Definition pass_p : parser_t pass := str_p.

  Definition assign : Term AsciiCharset string := str.
  Definition assign_p : parser_t assign := str_p.

  Definition grade : Term AsciiCharset Grade := number.
  Definition grade_p : parser_t grade := number_p.

  Definition section : Term AsciiCharset Section :=
    fun var => (digit _ @ (fun v => nat_of_ascii v - nat_of_ascii "0"%char))%grammar.
  Definition section_p : parser_t section :=
    (digit_p @ (fun v => nat_of_ascii v - nat_of_ascii "0"%char))%parser.

  Definition id_pass : Term AsciiCharset (string * string) :=
    fun var => 
      (#"[" ^ id _ ^ ws _ ^ pass _ ^ #"]" @ (fun x => (fst (snd x), fst (snd (snd (snd x))))))%grammar.
  Definition id_pass_p : parser_t id_pass :=
    (#"[" ^ id_p ^ ws_p ^ pass_p ^ #"]" @ (fun x => (fst (snd x), fst (snd (snd (snd x))))))%parser.


  Definition CommandGrammar : Term AsciiCharset ParseCommand := 
    fun var =>
      (    #"G" ^ #"E" ^ #"T" ^ ws _ ^ id_pass _ ^ ws _ ^ id _ ^ ws _ ^ assign _ @ 
             (fun x => 
               let up := (fst (snd (snd (snd (snd x))))) in
               let id := (fst (snd (snd (snd (snd (snd (snd x))))))) in
               let assign := (snd (snd (snd (snd (snd (snd (snd (snd x)))))))) in
               GetGrade' (fst up) (snd up) id assign)
       ||| #"S" ^ #"E" ^ #"T" ^ ws _ ^ id_pass _ ^ ws _ ^ id _ ^ ws _ ^ assign _ ^ ws _ ^ grade _ @ 
             (fun x => 
               let up := (fst (snd (snd (snd (snd x))))) in
               let id := (fst (snd (snd (snd (snd (snd (snd x))))))) in
               let assign := (fst (snd (snd (snd (snd (snd (snd (snd (snd x))))))))) in
               let gr := snd (snd (snd (snd (snd (snd (snd (snd (snd (snd x))))))))) in
               SetGrade' (fst up) (snd up) id assign gr)
       ||| #"A" ^ #"V" ^ #"G" ^ ws _ ^ id_pass _ ^ ws _ ^ assign _ @ 
             (fun x => 
               let up := (fst (snd (snd (snd (snd x))))) in
               let assign := (snd (snd (snd (snd (snd (snd x)))))) in
               Average' (fst up) (snd up) assign))%grammar.

  Definition CommandParser : parser_t CommandGrammar :=
      (    #"G" ^ #"E" ^ #"T" ^ ws_p ^ id_pass_p ^ ws_p ^ id_p ^ ws_p ^ assign_p @ 
             (fun x => 
               let up := (fst (snd (snd (snd (snd x))))) in
               let id := (fst (snd (snd (snd (snd (snd (snd x))))))) in
               let assign := (snd (snd (snd (snd (snd (snd (snd (snd x)))))))) in
               GetGrade' (fst up) (snd up) id assign)
       ||| #"S" ^ #"E" ^ #"T" ^ ws_p ^ id_pass_p ^ ws_p ^ id_p ^ ws_p ^ assign_p ^ ws_p ^ grade_p @ 
             (fun x => 
               let up := (fst (snd (snd (snd (snd x))))) in
               let id := (fst (snd (snd (snd (snd (snd (snd x))))))) in
               let assign := (fst (snd (snd (snd (snd (snd (snd (snd (snd x))))))))) in
               let gr := snd (snd (snd (snd (snd (snd (snd (snd (snd (snd x))))))))) in
               SetGrade' (fst up) (snd up) id assign gr)
       ||| #"A" ^ #"V" ^ #"G" ^ ws_p ^ id_pass_p ^ ws_p ^ assign_p @ 
             (fun x => 
               let up := (fst (snd (snd (snd (snd x))))) in
               let assign := (snd (snd (snd (snd (snd (snd x)))))) in
               Average' (fst up) (snd up) assign))%parser.

End GradebookParser.


Module HttpGradebookInterface (AP : GradebookType) : AppInterface with Module A := AP.
  Module A := AP.

  Definition grammar := GradebookParser.CommandGrammar.
  Definition parser  := GradebookParser.CommandParser.

  Open Local Scope string_scope.
  Export Basis.

  Definition header : list ascii := str2la (
(*    "<?xml version=""1.0""?>" ++  *)
    "<!DOCTYPE HTML PUBLIC ""-//W3C//DTD HTML 4.01//EN"" ""http://www.w3.org/TR/html4/strict.dtd"">" ++
    "<html>" ++
    " <head>" ++
    "  <title>Course Grade Server</title>" ++
    " </head>" ++
    " <body>" ++
    "  <form action=""http://127.0.0.1:8081"" method=""GET"" target=""_self"">" ++
    "   Query <input type=""text"" name=""q"" size=""25"" maxlength=""40"" /> <input type=""submit"" />" ++
    "  </form>" ++
    "  <br />"). 

  Definition footer : list ascii := str2la (
    " </body>" ++
    "</html>").

  Definition printer (res : Status) : list ascii :=
    List.app header
    (List.app
      match res with
        | ERR_NOTPRIVATE => str2la "<b color=""red"">Error:</b> Not Private"
        | ERR_BADGRADE => str2la "<b color=""red"">Error:</b> Bad Grade"
        | ERR_NOINV => str2la "<b color=""red"">Error:</b> No Invariant"
        | OK => str2la "<b color=""green"">Success!</b>"
        | RET x => List.app (str2la "<b color=""green"">Result:</b> ") (ntos 3 x nil)
      end
      footer).
  
  Definition err (_ : consumed_t) := 
    List.app header (List.app (str2la "<b color=""red"">Error:</b> Malformed query") footer).

End HttpGradebookInterface.