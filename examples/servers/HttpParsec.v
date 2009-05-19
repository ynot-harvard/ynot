Require Import Ynot.
Require Import Ascii.
Require Import Stream.
Require Import Parsec Charset ParsecCombinators.
Require Import Arith.
Require Import String.

Set Implicit Arguments.

Module Http.
  Import Combinators.
  Import ParsecNotation.

  Definition crlf : Term AsciiCharset unit :=
    fun _ => (# cr ^ #lf @ (fun _ => tt))%grammar.
  
  Definition crlf_p : parser_t crlf.
    refine ((# cr ^ #lf @ (fun _ => tt)))%parser.
  Qed.    

  Definition HTTP : Term AsciiCharset string := 
    fun var => 
    (#"G" ^ #"E" ^ #"T" ^ ws _ ^ str _ ^ ws _ ^ #"H" ^ #"T" ^ #"T" ^ #"P" ^ #"/" ^ # "1" ^ #"." ^ digit _ ^ crlf _ ^ crlf _ @ (fun x => fst (snd (snd (snd (snd x))))))%grammar.

  Definition HTTP_p : parser_t HTTP :=
    (#"G" ^ #"E" ^ #"T" ^ ws_p ^ str_p ^ ws_p ^ #"H" ^ #"T" ^ #"T" ^ #"P" ^ #"/" ^ # "1" ^ #"." ^ digit_p ^ crlf_p ^ crlf_p @ (fun x => fst (snd (snd (snd (snd x))))))%parser.

End Http.

Open Local Scope stsepi_scope.
Require Import Basis.

Require Import GradebookInterface.

Definition parse_test : forall (input : string),
  STsep (__) 
        (fun _ : option string (*nat * ((method * string * (nat * nat)) * (list (string * string)) * string)*) => __)%hprop.
  intros; refine (
     printStringLn' (str2la input) ;;
     is <- STRING_INSTREAM.instream_of_list_ascii (str2la input) ;
     (* parse <- http_parse is (inhabits 0) ; *)
     parse <- GradebookInterface.GradebookParser.CommandParser is (inhabits 0) ;
     INSTREAM.close is ;;
     {{Return (match parse with 
                 | ERROR _ _ => None
                 | OKAY _ _ q => Some "good"%string
               end)}}).
  sep fail auto.
  sep fail auto.
  sep fail auto.
  sep fail auto.
  sep fail auto.
  sep fail auto.
  unfold ans_str_correct, okaystr,errorstr,okay,error; destruct parse; sep fail auto.
  sep fail auto.
  sep fail auto.
  sep fail auto.
Qed.
