{
 (** Lexical analyzer for {!Form} formulas
     generated with ocamllex. 
  *)
 open YaccForm

 let safe_print_char ch = 
   if ' ' <= ch then Printf.sprintf "%c" ch 
   else Printf.sprintf "ASCII %d" (int_of_char ch)

 let string_lit s =
   let len = String.length s in
     String.sub s 2 (len-4)
}
 let digitchar = ['0'-'9']
 let natlit = '-'? digitchar digitchar*
 let identchar = ['a'-'z''A'-'Z''_']
 let ident = identchar (identchar | digitchar)*
 let qualident = ident ('.' ident)*
 let typident = ''' ident
 let xident = '\\' '<' identchar* '>'
 let non_quote = [^ ''' '"']
 let string = ''' ''' non_quote* ''' '''
 let nonblank_char = [^ ' ''\n''\t''\r']

 let Comment = "(*" ([^ '*'] | '*' [^ ')'])* "*)"

  rule token = parse
  [' ' '\t''\n''\r']     {token lexbuf}     (* skip blanks *)
| Comment        {token lexbuf}     (* skip blanks *)
| eof            {EOF}
| natlit as n    {NATLIT(int_of_string n)}
| string as s    {STRING (string_lit s)}
  (* constants *)
| "True"         {TRUE}
| "False"        {FALSE}
| "null"         {NULL}
| "{}"           {EMPTYSET}
| "\\<emptyset>" {EMPTYSET}
| "\\<forall>"    {FORALL}
| "ALL"          {FORALL}
| "\\<exists>"    {EXISTS}
| "EX"           {EXISTS}
| "\\<lambda>"   {LAMBDA}
| "%"            {LAMBDA}
| "let"          {LET}
| "in"           {IN}
| "%"            {LAMBDA}
| "Un"           {CUP}
| "\\<union>"     {CUP}
| "Int"          {CAP}
| "\\<inter>"     {CAP}
| "~="           {NEQ}
| "!="           {NEQ}
| "\\<noteq>"     {NEQ}
| '='            {EQ}
| "=="           {EQQ}
| "==="          {SETEQ}
| '|'            {OR}
| "\\<or>"        {OR}
| '&'            {AND}
| "\\<and>"       {AND}
| '~'            {NOT}
| "\\<not>"       {NOT}
| "=>"           {ARROW}
| "-->"          {IMPL}
| "\\<longrightarrow>" {IMPL}
| "==>"          {METAIMPL}
| "<->"          {IFF}
| '>'            {GT}
| '<'            {LT}
| ">="           {GTEQ}
| "<="           {LTEQ}
| "\\<le>"       {LTEQ}
| "[|"           {ALBRACKET}
| "|]"           {ARBRACKET}
| '['            {LBRACKET}
| ".["           {DOTLBRACKET}
| "$["           {DOLLARLBRACKET}
| ']'            {RBRACKET}
| '{'            {LBRACE}
| '}'            {RBRACE}
| ','            {COMMA}
| ".."           {DEREF}
| "``"           {RIMAGE}
| "$"            {DOLLAR}
| '.'            {DOT}
| '('            {LPAREN}
| ')'            {RPAREN}
| '+'            {PLUS}
| '-'            {MINUS}
| '*'            {TIMES}
| "div"          {DIVIDE}
| "::"           {COLONCOLON}
| ':'            {COLON}
| "\\<in>"       {COLON}
| "~:"           {NCOLON}
| "\\<notin>"    {NCOLON}
| '@'            {APPLY}
| ';'            {SEMICOLON}
| "arrayRead"    {ARRAYREAD}
| "arrayWrite"   {ARRAYWRITE}
| "fieldWrite"   {FIELDWRITE}
| "fieldRead"    {FIELDREAD}
| "comment"      {COMMENT}

| "unit"         {UNIT}
| "int"          {INT}
| "bool"         {BOOL}
| "array"        {ARRAY}
| "set"          {SET}
| "list"         {LIST}
| "obj"          {OBJ}

| "\\<subseteq>" {SUBSETEQ}
| "<==" {SUBSETEQ}
| "\\<setminus>" {SETMINUS}
| "\\<subset>"   {SUBSET}
| "card"         {CARD}
| "Card"         {CARD}

| "zf"           {ZF}

| "mod"          {MOD}
| "old"          {OLD}
| "objlocs"      {OBJLOCS}
| "rtrancl"      {RTRANCL}

| "if"           {IF}
| "then"         {THEN}
| "else"         {ELSE}

| ident as s     {IDENT s}
| typident as s  {TYPIDENT s}
| qualident as s {QIDENT s}
| xident as s    {failwith ("unknown x-symbol token '" ^ s ^ "'")}
| nonblank_char as c {failwith ("Unrecognized token '" ^ safe_print_char c ^ "' while parsing formula or type.")}
