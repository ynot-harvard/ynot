%{
(** Parser for {!Specs} specifications, generated with ocamlyacc. *)
open Form
open FormUtil
open Specs

let parse_error = ParsingSpecAux.parse_error
%}

%token <string> STRING
%token <string> IDENT
%token <string> QIDENT
%token COMMA SEMICOLON COLON COLONCOLON
%token LPAREN RPAREN
%token COLONEQUAL EQUAL EOF
%token LEMMA 
%token PUBLIC 
%token INVARIANT REQUIRES MODIFIES ENSURES 
%token SPECFIELD SPECSTATIC SPECVAR
%token PUBLIC PRIVATE STATIC GHOST ENSURED
%token CONSTDEFS VARDEFS 
%token READONLY CLAIMEDBY
%token ASSERT NOTETHAT ASSUME SPLIT HAVOC
%token HIDDEN

%start main             /* the entry point */
%type <Specs.spec list> main
%%

main: spec_list EOF {$1};

spec_list:
| spec oSEMICOLON spec_list {$1 :: $3}
| spec oSEMICOLON {[$1]}
;

spec:
| lemma {$1}
| invariant  {$1}
| contract   {$1}
| specvar {$1}
| constdefs  {$1}
| vardefs    {$1}
| modifier   {$1}
| assert_cmd {$1}
| noteThat_cmd {$1}
| assume_cmd {$1}
| split_cmd {$1}
| havoc_cmd {$1}
| assign_cmd {$1}
| operation {$1}
;

lemma:
  LEMMA IDENT COLON qform
  {mk_lemma $2 $4};

assert_cmd:
  ASSERT qform 
  {Assert $2};

noteThat_cmd:
  NOTETHAT qform 
  {NoteThat $2};

assume_cmd:
  ASSUME qform 
  {Assume $2};

split_cmd:
  SPLIT qform
  {Split $2};

havoc_cmd:
  HAVOC qform_comma_list
  {Havoc $2};

assign_cmd:
  qitem COLONEQUAL qform
  {mk_aassign $1 $3};

operation:
  IDENT LPAREN qform_comma_list RPAREN
  {mk_aoperation $1 $3};

optional_name:
| { "" }
| LPAREN STRING RPAREN { $2 }

ensured:
| {false}
| ENSURED {true}
;

invariant:
  publicness ensured INVARIANT optional_name qform 
  { mk_invariant $1 $2 $4 $5 };

contract:
  requires modifies ensures
  { mk_contract $1 $2 $3 };

requires:
| { None }
| REQUIRES qform { Some $2 };

modifies:
| { None }
| MODIFIES qform_comma_list { Some $2 };

ensures:
  ENSURES qform 
  { Some $2 };

specvar:
  publicness staticness ghostness SPECVAR IDENT COLONCOLON qtitem optinit
    {mk_specvar $1 $2 $3 $5 $7 $8}

constdefs:
    publicness CONSTDEFS defs
    { mk_constdefs $1 $3 };

vardefs:
    publicness VARDEFS defs
    { mk_vardefs $1 $3 };

defs:
| def oSEMICOLON { [$1] }
| defs def oSEMICOLON { $1 @ [$2] };

def: qform { mk_def $1 };

modifier:
| READONLY {mk_modifier Readonly}
| CLAIMEDBY IDENT {mk_modifier (ClaimedBy $2)}
| HIDDEN { mk_modifier Hidden }
;

optinit:
| { None }
| EQUAL qitem { Some $2 };

qform_comma_list:
| qitem
    {[$1]}
| qform_comma_list COMMA qitem
    {$1 @ [$3]}
    ;
 
qitem:
| IDENT { mk_var $1 }
| qform { $1 };

qform:
    STRING { ParseForm.parse_formula $1 };

qident:
  IDENT  {$1}
| QIDENT {$1};

qtitem:
| IDENT  { ParseForm.parse_type $1 }
| STRING { ParseForm.parse_type $1 };

publicness:
| PUBLIC  {PubPublic}
| PRIVATE {PubPrivate}
| {PubDefault}
;

staticness:
| STATIC {StatStatic}
| {StatInstance}
;

ghostness:
| GHOST {GhostVar}
| {NonGhostVar}
;

oSEMICOLON:
| { () }
| SEMICOLON { () };
