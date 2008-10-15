(*
   Joust: a Java lexer, parser, and pretty-printer written in OCaml
   Copyright (C) 2001  Eric C. Cooper <ecc@cmu.edu>
   Released under the GNU General Public License *)

(* ocamllex lexer for Java

   Attempts to conform to:

   The Java Language Specification
   Second Edition

   James Gosling, Bill Joy, Guy Steele, Gilad Bracha *)

{
open Source
open Parser

(** Generated Joust lexer. *)

let identifier buf =
  let s = Lexing.lexeme buf in
  match Reserved.lookup s with
  | Some t -> t
  | None -> IDENTIFIER (Syntax.ident s (Source.lexeme_pos buf))

let literal buf =
  LITERAL (Lexing.lexeme buf)

let assign_op buf =
  OPERATOR_EQ (Lexing.lexeme buf)

let crop (left:int) (right:int) (str:string) =
  let len = String.length str in
  if len > left + right then
    String.sub str left (len - left - right)
  else ""

let annotation buf =
  ANNOTATION (crop 3 2 (Lexing.lexeme buf))

let short_annotation buf =
  ANNOTATION (crop 3 1 (Lexing.lexeme buf))

exception Unterminated_comment
}

(* CHAPTER 3: Lexical Structure *)

(* 3.4 Line Terminators *)

let LF = '\n'  (* newline *)
let CR = '\r'  (* return *)

let LineTerminator = LF | CR | CR LF
let InputCharacter = [^ '\r' '\n']

(* 3.5 Input Elements and Tokens *)

let SUB = '\026' (* control-Z *) (* decimal *)

(* 3.6 White Space *)

let SP = ' '     (* space *)
let HT = '\t'    (* horizontal tab *)
let FF = '\012'  (* form feed *) (* decimal *)

let WhiteSpace = SP | HT | FF (* | LineTerminator -- handled separately *)

(* 3.7 Comments *)

(* let TraditionalComment = "/*" ([^ '*'] | '*' [^ '/'])* "*/" *)
let EndOfLineComment = "//" InputCharacter* LineTerminator
(* let Comment = TraditionalComment | EndOfLineComment *)

(* beginvk *)
let Annotation = "/*:" ([^ '*'] | '*' [^ '/'])* "*/"
let ShortAnnotation = "//:" InputCharacter* LineTerminator
(* endvk *)

(* 3.8 Identifiers *)

let Letter = ['A'-'Z' 'a'-'z' '_' '$']
let Digit = ['0'-'9']
let Identifier = Letter (Letter | Digit)*

(* 3.10.1 Integer Literals *)

let IntegerTypeSuffix = ['l' 'L']

let DecimalIntegerLiteral = ('0' | ['1'-'9'] Digit*) IntegerTypeSuffix?

let HexDigit = ['0'-'9' 'a'-'f' 'A'-'F']
let HexIntegerLiteral = '0' ['x' 'X'] HexDigit+ IntegerTypeSuffix?

let OctalDigit = ['0'-'7']
let OctalIntegerLiteral = '0' OctalDigit+ IntegerTypeSuffix?

let IntegerLiteral =
  DecimalIntegerLiteral
| HexIntegerLiteral
| OctalIntegerLiteral

(* 3.10.2 Floating-Point Literals *)

let ExponentPart = ['e' 'E'] ['+' '-']? Digit+

let FloatTypeSuffix = ['f' 'F' 'd' 'D']

let FloatingPointLiteral =
  (Digit+ '.' Digit* | '.' Digit+) ExponentPart? FloatTypeSuffix?
| Digit+ (ExponentPart FloatTypeSuffix? | ExponentPart? FloatTypeSuffix)

(* 3.10.3 Boolean Literals *)

let BooleanLiteral = "true" | "false"

(* 3.10.6 Escape Sequences for Character and String Literals *)

let OctalEscape = '\\' ['0'-'3']? OctalDigit? OctalDigit

(* Not in spec -- added because we don't handle Unicode elsewhere. *)

let UnicodeEscape = "\\u" HexDigit HexDigit HexDigit HexDigit

let EscapeSequence =
  '\\' ['b' 't' 'n' 'f' 'r' '"' '\'' '\\']
| OctalEscape
| UnicodeEscape

(* 3.10.4 Character Literals *)

let SingleCharacter = [^ '\'' '\\' '\n' '\r']
let CharacterLiteral = '\'' (SingleCharacter | EscapeSequence) '\''

(* 3.10.5 String Literals *)

let StringCharacter = [^ '"' '\\' '\n' '\r']
let StringLiteral = '"' (StringCharacter | EscapeSequence)* '"'

(* 3.10.7 The Null Literal *)

let NullLiteral = "null"

(* 3.10 Literals *)

let Literal =
  IntegerLiteral
| FloatingPointLiteral
| BooleanLiteral
| CharacterLiteral
| StringLiteral
| NullLiteral

(* Assignment operators, except '=', from section 3.12 *)

let AssignmentOperator =
  ('+' | '-' | '*' | '/' | '&' | '|' | '^' | '%' | "<<" | ">>" | ">>>") '='

rule token = parse
| Annotation (* vk *)
    { annotation lexbuf }
| ShortAnnotation
    { short_annotation lexbuf }
| WhiteSpace
    { token lexbuf }
| LineTerminator
    { next_line lexbuf; token lexbuf }
| "/*"
    { begin_comment lexbuf; comment lexbuf; token lexbuf }
| EndOfLineComment
    { eol_comment lexbuf; next_line lexbuf; token lexbuf }
| Identifier
    { identifier lexbuf }
| Literal
    { literal lexbuf }

(* 3.11 Separators *)
| '('  { LP }
| ')'  { RP }
| '{'  { LC }
| '}'  { RC }
| '['  { LB }
| ']'  { RB }
| ';'  { SM }
| ','  { CM }
| '.'  { DOT }

(* 3.12 Operators *)
| "="  { EQ }
| ">"  { GT }
| "<"  { LT }
| "!"  { NOT }
| "~"  { COMPL }
| "?"  { COND }
| ":"  { COLON }
| "=="  { EQ_EQ }
| "<="  { LE }
| ">="  { GE }
| "!="  { NOT_EQ }
| "&&"  { AND_AND }
| "||"  { OR_OR }
| "++"  { INCR }
| "--"  { DECR }
| "+"  { PLUS }
| "-"  { MINUS }
| "*"  { TIMES }
| "/"  { DIV }
| "&"  { AND }
| "|"  { OR }
| "^"  { XOR }
| "%"  { MOD }
| "<<"  { LS }
| ">>"  { SRS }
| ">>>"  { URS }
| AssignmentOperator  { assign_op lexbuf }

| SUB? eof { EOF }

and comment = parse
  "*/" { end_comment lexbuf }
| LineTerminator  { continue_comment lexbuf; next_line lexbuf; comment lexbuf }
| eof  { raise Unterminated_comment }
| _  { continue_comment lexbuf; comment lexbuf }
