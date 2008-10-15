%{
(** Parser for {!Form} formulas, generated with ocamlyacc. *)
open Form
open FormUtil

let parse_error = ParsingFormAux.parse_error
%}

%token <string> IDENT
%token <string> QIDENT
%token <string> TYPIDENT
%token <string> STRING
%token <int> NATLIT
%token ARRAYREAD ARRAYWRITE
%token FIELDWRITE FIELDREAD
%token AND OR NOT IMPL IFF NULL EMPTYSET ARROW IF THEN ELSE
%token METAIMPL
%token NCOLON COLON COLONCOLON SEMICOLON DOT CUP CAP
%token COMMA EQ EQQ NEQ 
%token LT GT LTEQ GTEQ 
%token PLUS SETMINUS MINUS TIMES DIVIDE DEREF
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token DOTLBRACKET DOLLARLBRACKET
%token ALBRACKET ARBRACKET
%token TRUE FALSE SET BOOL FORALL EXISTS LAMBDA LET IN
%token EOL EOF
%token APPLY DOLLAR
%token QUOTE
%token OBJ UNIT INT BOOL ARRAY SET LIST OLD OBJLOCS MOD RIMAGE ZF
%token COMMENT

%token SUBSETEQ SUBSET SETEQ SETMINUS
%token CARD RTRANCL

%left SEMICOLON
%left COLONCOLON
%nonassoc IFF
%nonassoc IF THEN ELSE
%right IMPL ARROW
%right METAIMPL
%left OR
%left AND
%right NOT DOT
%nonassoc EQ COLON NCOLON
%nonassoc LT GT LTEQ GTEQ NEQ
%nonassoc SUBSETEQ SUBSET SETEQ
%left CUP CAP
%left PLUS MINUS SETMINUS
%nonassoc FORALL EXISTS LAMBDA
%right TIMES DIVIDE MOD RIMAGE
%nonassoc CARD OLD RTRANCL ZF
%left APPLY DOLLAR
%left DEREF

%start main             /* the entry point */
%type <Form.typeOrForm> main
%%
main:
| COLON type_form    { AType $2 }
| form EOF           { AForm $1 }
;

factor:
| ARRAYREAD {Const ArrayRead}
| ARRAYWRITE {Const ArrayWrite}
| FIELDREAD {Const FieldRead}
| FIELDWRITE {Const FieldWrite}
| LPAREN form RPAREN
    {$2}
| LPAREN form COMMA form_comma_list RPAREN
    {mk_tuple ($2 :: $4)}
| ident {mk_var $1}
| ident DOLLARLBRACKET form_no_binder RBRACKET
    %prec DEREF
    {App (Var "elemImage", [Var $1;$3])}
| NULL
    {Const NullConst}
| TRUE
    {Const (BoolConst true)}
| FALSE
    {Const (BoolConst false)}
| NATLIT
    {Const (IntConst $1)}
| EMPTYSET
    {Const EmptysetConst}
| LBRACE IDENT DOT form RBRACE
    %prec DOT
    {Binder (Comprehension, [($2, TypeUniverse)], $4)}
| LBRACE LPAREN IDENT COMMA IDENT RPAREN RBRACE
    %prec DOT
    {mk_singleton_relation $3 $5}
| LBRACE LPAREN IDENT COMMA IDENT RPAREN DOT form RBRACE
    %prec DOT
    {mk_relation_comprehension ($3, TypeUniverse) ($5, TypeUniverse) $8}
| LBRACE form_comma_list RBRACE
    {mk_finite_set $2}
| LBRACKET form_comma_list RBRACKET { mk_list $2 }
| ALBRACKET form_semicol_list ARBRACKET
    %prec SEMICOLON
    {mk_metaand $2}
  ;

form_no_binder:
| factor {$1}
| form_no_binder DEREF ident {mk_fieldRead (mk_var $3) $1}
| form_no_binder DOTLBRACKET form_no_binder RBRACKET
    %prec DEREF
    {mk_arrayRead1 $1 $3}
| NOT form_no_binder
    {App (Const Not, [$2])}
| form_no_binder AND form_no_binder
    {smk_and [$1;$3]}
| form_no_binder OR form_no_binder
    {App (Const Or, [$1;$3])}
| form_no_binder IMPL form_no_binder
    {App (Const Impl, [$1;$3])}
| form_no_binder METAIMPL form_no_binder
    {App (Const MetaImpl, [$1;$3])}
| form_no_binder IFF form_no_binder
    {App (Const Iff, [$1;$3])}
| form_no_binder EQ form_no_binder
    {App (Const Eq, [$1;$3])}
| form_no_binder EQQ form_no_binder
    {App (Const MetaEq, [$1;$3])}
| form_no_binder NEQ form_no_binder
    {App (Const Not, [App ((Const Eq), [$1;$3])])}
| form_no_binder LT form_no_binder
    {App (Const Lt, [$1;$3])}
| form_no_binder LTEQ form_no_binder
    {App (Const LtEq, [$1;$3])}
| form_no_binder GT form_no_binder
    {App (Const Gt, [$1;$3])}
| form_no_binder GTEQ form_no_binder
    {App (Const GtEq, [$1;$3])}
| form_no_binder COLON form_no_binder
    {mk_elem($1,$3)}
| form_no_binder NCOLON form_no_binder
    {mk_notelem($1,$3)}
| form_no_binder CUP form_no_binder
    {App (Const Cup, [$1;$3])}
| form_no_binder CAP form_no_binder
    {App (Const Cap, [$1;$3])}
| form_no_binder PLUS form_no_binder
    {App (Const Plus, [$1;$3])}
| form_no_binder MINUS form_no_binder
    {App (Const Minus, [$1;$3])}
| form_no_binder DOLLAR form_no_binder
    {App (Var "elemImage", [$1;$3])}
| form_no_binder TIMES form_no_binder
    {App (Const Mult, [$1;$3])}
| form_no_binder DIVIDE form_no_binder
    {App (Const Div, [$1;$3])}
| form_no_binder MOD form_no_binder
    {App (Const Mod, [$1;$3])}
| form_no_binder RIMAGE form_no_binder
    {App (Const Rimage, [$1;$3])}
| form_no_binder COLONCOLON type_form
    {mk_typedform($1,$3)}
| form_no_binder SUBSET form_no_binder 
    {App (Const Subset, [$1; $3])}
| IF form_no_binder THEN form_no_binder ELSE form_no_binder
    {App (Const Ite, [$2;$4;$6])}
| form_no_binder SUBSETEQ form_no_binder 
    {App (Const Subseteq, [$1; $3])}
| form_no_binder SETEQ form_no_binder
    {App (Const Seteq, [$1; $3])}
| form_no_binder SETMINUS form_no_binder
    {App (Const Diff, [$1; $3])}
| CARD factor
    {App (Const Card, [$2])}
| OLD factor
    {App (Const Old, [$2])}
| OBJLOCS factor
    {App (Const ObjLocs, [$2])}
| RTRANCL factor
    {App (Const Rtrancl, [$2])}
| COMMENT STRING factor
    {mk_comment $2 $3}
| factor factor_list
    %prec APPLY
    {parse_mk_app $1 $2}
  ;

form:
| form_no_binder
    {$1}
| FORALL tid_list DOT form 
    %prec DOT
    {Binder (Forall,$2,$4)}
| EXISTS tid_list DOT form 
    %prec DOT
    {Binder (Exists,$2,$4)}
| LAMBDA tid_list DOT form
    %prec DOT
    {Binder (Lambda,$2,$4)}
| LET tid EQ form_no_binder IN form_no_binder
    %prec DOT
    {mk_let $4 $2 $6}
;

tid_list:
| tid {[$1]}
| tid_list tid
    {$1 @ [$2]}
  ;

/*
tuple_list:
| LPAREN form_comma_list RPAREN { [mk_tuple $2] }
| tuple_list COMMA LPAREN form_comma_list RPAREN {$1 @ [mk_tuple $4]}
;
*/

tid_comma_list:
| tid {[$1]}
| tid_list COMMA tid
    {$1 @ [$3]}
  ;

tid:
| IDENT 
  {($1, TypeUniverse)}
| LPAREN IDENT COLONCOLON type_form RPAREN
  {($2, $4)}

factor_list:
| factor
    {[$1]}
| factor_list factor 
    %prec APPLY
    {$1 @ [$2]}
    ;

form_semicol_list:
| form_no_binder
    {[$1]}
| form_semicol_list SEMICOLON form_no_binder
    {$1 @ [$3]}
    ;

form_comma_list:
| form_no_binder
    {[$1]}
| form_comma_list COMMA form_no_binder
    {$1 @ [$3]}
    ;

ident:
| QIDENT {$1}
| IDENT {$1};

type_form: 
| tfactor                     { $1 }
| tfactor_list tsimple        { TypeApp($2,$1) }
| type_form TIMES type_form   { TypeProd[$1;$3] }
| type_form ARROW type_form   { TypeFun([$1],$3) };

tfactor_list:
| tfactor              { [$1] }
| tfactor_list tfactor { $1 @ [$2] };

tfactor:
| TYPIDENT { mk_typevar $1}
| tsimple                 { TypeApp($1,[]) }
| LPAREN type_form RPAREN { $2 }
| IDENT { mk_type_from_ident $1 }
;

tsimple:
| UNIT  { TypeUnit }
| INT   { TypeInt }
| BOOL  { TypeBool }
| ARRAY { TypeArray }
| SET   { TypeSet }
| LIST  { TypeList }
| OBJ   { TypeObject }
;

