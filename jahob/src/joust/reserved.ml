(** Java reserved words. *)

(* Joust: a Java lexer, parser, and pretty-printer written in OCaml
   Copyright (C) 2001  Eric C. Cooper <ecc@cmu.edu>
   Released under the GNU General Public License *)


open Parser

let hash_table list =
  let tbl = Hashtbl.create (List.length list)
  in
  List.iter (fun (s, t) -> Hashtbl.add tbl s t) list;
  tbl

let literal v = (v, LITERAL v)

let primitive_type t = (t, PRIMITIVE_TYPE t)

let words = hash_table [
  "abstract", ABSTRACT;
  "boolean", BOOLEAN;
  "break", BREAK;
  "byte", BYTE;
  "case", CASE;
  "catch", CATCH;
  "char", CHAR;
  "class", CLASS;
  "const", CONST;
  "continue", CONTINUE;
  "default", DEFAULT;
  "do", DO;
  "double", DOUBLE;
  "else", ELSE;
  "extends", EXTENDS;
  "final", FINAL;
  "finally", FINALLY;
  "float", FLOAT;
  "for", FOR;
  "goto", GOTO;
  "if", IF;
  "implements", IMPLEMENTS;
  "import", IMPORT;
  "instanceof", INSTANCEOF;
  "int", INT;
  "interface", INTERFACE;
  "long", LONG;
  "native", NATIVE;
  "new", NEW;
  "package", PACKAGE;
  "private", PRIVATE;
  "protected", PROTECTED;
  "public", PUBLIC;
  "return", RETURN;
  "short", SHORT;
  "static", STATIC;
  "strictfp", STRICTFP;
  "super", SUPER;
  "switch", SWITCH;
  "synchronized", SYNCHRONIZED;
  "this", THIS;
  "throw", THROW;
  "throws", THROWS;
  "transient", TRANSIENT;
  "try", TRY;
  "void", VOID;
  "volatile", VOLATILE;
  "while", WHILE;

  literal "true";
  literal "false";
  literal "null";

  primitive_type "byte";
  primitive_type "short";
  primitive_type "char";
  primitive_type "int";
  primitive_type "long";
  primitive_type "float";
  primitive_type "double";
  primitive_type "boolean";
]

let lookup name =
  try Some (Hashtbl.find words name) with Not_found -> None
