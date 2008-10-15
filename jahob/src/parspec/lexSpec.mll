{
 open YaccSpec

let trim_quotes s = 
  let trim_last s' = if String.get s' ((String.length s')-1) = '"' then
    String.sub s' 0 ((String.length s')-1) else s' in
  if String.get s 0 = '"' then 
    (trim_last (String.sub s 1 ((String.length s) - 1)))
  else
    trim_last s

 let safe_print_char ch = 
   if ' ' <= ch then Printf.sprintf "%c" ch 
   else Printf.sprintf "ASCII %d" (int_of_char ch)

}

 let StringCharacter = [^ '"']
 let StringLiteral = '"' StringCharacter* '"'
 let nonblank_char = [^ ' ''\n''\t']

 let LineTerminator = '\r' | '\n' | '\r' '\n'
 let CommentCharacter = [^ '\r' '\n']
 let EndOfLineComment = "//" CommentCharacter* LineTerminator?

 let digitchar = ['0'-'9']
 let identchar = ['a'-'z''A'-'Z''_'''']
 let ident = identchar (identchar | digitchar)*
 let qualident = identchar (identchar | digitchar | '.')* identchar
 let xident = '\\' '<' identchar* '>'
 let nonblank = nonblank_char nonblank_char*

 rule token = parse
 [' ' '\t''\n''\r'] {token lexbuf}     (* skip blanks *)
| EndOfLineComment  {token lexbuf}     (* skip comments *)
| eof            {EOF}  
| '('            {LPAREN}
| ')'            {RPAREN}
| ';'            {SEMICOLON}
| ','            {COMMA}
| ':'            {COLON}
| "::"           {COLONCOLON}
| ":="           {COLONEQUAL}
| '='            {EQUAL}
| "lemma"        {LEMMA}
| "public"       {PUBLIC}
| "private"      {PRIVATE}
| "static"       {STATIC}
| "ghost"        {GHOST}
| "invariant"    {INVARIANT}
| "ensured"      {ENSURED}
| "inv"          {INVARIANT}
| "requires"     {REQUIRES}
| "modifies"     {MODIFIES}
| "ensures"      {ENSURES}
| "specfield"    {SPECFIELD}
| "specstatic"   {SPECSTATIC}
| "specvar"      {SPECVAR}
| "vardefs"      {VARDEFS}
| "constdefs"    {CONSTDEFS}
| "readonly"     {READONLY}
| "claimedby"    {CLAIMEDBY}
| "assert"       {ASSERT}
| "noteThat"     {NOTETHAT}
| "assume"       {ASSUME}
| "split"        {SPLIT}
| "havoc"        {HAVOC}
| "hidden"       {HIDDEN}
| StringLiteral as s {STRING (trim_quotes s)}
| ident as s {IDENT s}
| qualident as s {QIDENT s}
| xident as s {IDENT s}
| nonblank_char as c {failwith ("Unrecognized token '" ^ safe_print_char c ^ "' while parsing spec.")}

