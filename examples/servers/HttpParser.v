Require Import Ynot.
Require Import Charset Packrat.
Require Import List Ascii String.

Set Implicit Arguments.

(**
       URI            = ( absoluteURI | relativeURI ) [ "#" fragment ]

       absoluteURI    = scheme ":" *( uchar | reserved )

       relativeURI    = net_path | abs_path | rel_path

       net_path       = "//" net_loc [ abs_path ]
       abs_path       = "/" rel_path
       rel_path       = [ path ] [ ";" params ] [ "?" query ]

       path           = fsegment *( "/" segment )
       fsegment       = 1*pchar
       segment        = *pchar

       params         = param *( ";" param )
       param          = *( pchar | "/" )

       scheme         = 1*( ALPHA | DIGIT | "+" | "-" | "." )
       net_loc        = *( pchar | ";" | "?" )
       query|fragment = *( uchar | reserved )

       pchar          = uchar | ":" | "@" | "&" | "=" | "+"
       uchar          = unreserved | escape
       unreserved     = ALPHA | DIGIT | safe | extra | national

       escape         = "%" HEX HEX
       reserved       = ";" | "/" | "?" | ":" | "@" | "&" | "=" | "+"
       extra          = "!" | "*" | "'" | "(" | ")" | ","
       safe           = "$" | "-" | "_" | "."
       unsafe         = CTL | SP | <""> | "#" | "%" | "<" | ">"
       national       = <any OCTET excluding ALPHA, DIGIT,
                        reserved, extra, safe, and unsafe>
**)
Import Packrat.


Definition alpha := Terminal AsciiCharset (ARange "a" "z").
Definition Alpha := Terminal AsciiCharset (ARange "A" "Z").
Definition digit := Terminal AsciiCharset (ARange "0" "9").

Section Combinators.
  Variable base_ty : Set.
  Variable base_ty_denote : base_ty -> Set.
  Definition ty := @ty base_ty.
  Definition tyDenote : ty -> Set := @tyDenote ascii base_ty base_ty_denote.
  Definition term := @term ascii.

  Definition many ctx (T S : ty) (t: tyDenote T) (f : tyDenote S -> tyDenote T -> tyDenote T)
    (prin : term _ ctx S) (rec : term _ ctx T) : term _ ctx T :=
    (Alt (Map _ (fun a : tyDenote (Prod S T) => f (fst a) (snd a)) (Seq prin rec))
         (Map _ (fun _ => t) (@Epsilon ascii base_ty base_ty_denote ctx))).

  Definition many1 ctx (T S : ty) (t: tyDenote S -> tyDenote T) 
    (f : tyDenote S -> tyDenote T -> tyDenote T)
    (prin : term _ ctx S) (rec : term _ ctx T) : term _ ctx T :=
    (Alt (Map _ (fun a:tyDenote (Prod S T) => f (fst a) (snd a)) (Seq prin rec))
         (Map _ (t) (prin))).
End Combinators.

Set Printing All.
Definition manyStr ctx : term (fun _:unit => string) ctx (Char unit) -> term (fun _:unit => string) ctx (Base tt) -> term (fun _:unit => string) ctx (Base tt) :=
  @many unit (fun _:unit => string) ctx (Base tt) (Char unit) EmptyString String.

Definition many1Str ctx : term (fun _:unit => string) ctx (Char unit) -> term (fun _:unit => string) ctx (Base tt) -> term (fun _:unit => string) ctx (Base tt) :=
  @many1 unit (fun _:unit => string) ctx (Base tt) (Char unit) (fun a:tyDenote (fun _:unit => string) (Char unit) => String a EmptyString) String.

Definition cat ctx (c : ascii) (s : term ctx string) : term ctx string :=
  Map _ (fun a => String (fst a) (snd a)) (Seq (Lit ctx c) s).

Definition optional ctx (T : Set) (t : T) (c : term ctx T) : term ctx T :=
  Alt c (Map (fun _ => t) (Epsilon _)).

Fixpoint litString ctx (T : Set) (t : T) (s : string) : term ctx T :=
  match s with
    | EmptyString => (Map (fun _ => t) (Epsilon ctx))
    | String a r => (Map (fun _ => t) (Seq (Lit _ a) (litString ctx t r)))
  end.

(* Notation "# c" := (AsciiParser.Lit _ c%char) (at level 1) : grammar_scope. *)
Notation "## c" := (AsciiParser.LitClass _ c%char) (at level 1) : grammar_scope.
Notation "e1 ^^ e2" := (AsciiParser.Seq e1 e2) (right associativity, at level 30) : grammar_scope.
Notation "e @@ f" := (AsciiParser.Map f e) (left associativity, at level 78) : grammar_scope.
Notation "e1 || e2" := (AsciiParser.Alt e1 e2) (right associativity, at level 79) : grammar_scope.

Open Local Scope grammar_scope.

Fixpoint enum ctx (T : Set) (t':T) (t : list (string * T)) : term ctx T :=
  match t with
    | nil => ## (Group nil) @@ (fun _ => t') (** This is essentially the error production **)
    | (str,v) :: r => (litString _ v str) || enum ctx t' r
  end.

Definition crlf ctx : term ctx unit := (Lit _ (ascii_of_nat 13)) ^^ (Lit _ (ascii_of_nat 10)) @@ (fun _ => tt).
Definition sp ctx : term ctx unit := (Lit _ " "%char) @@ (fun _ => tt
Inductive method : Set :=
| GET : method | POST : method | HEAD : method.

Definition HTTP_ctx := 
       (nat ::
        ascii :: ascii :: ascii :: ascii ::
        ascii :: ascii :: ascii ::
        string ::
        string :: string ::
        string :: string :: string ::
        string :: string :: string ::
        method :: (nat * nat) :: (method * string * (nat * nat)) ::
        string :: string :: (string * string) :: list (string * string) ::
        string :: 
        string :: ((method * string * (nat * nat)) * (list (string * string)) * string) :: nil)%type.

Definition HTTP_env :=
  gfix HTTP_ctx
  (fun number
       unsafe safe extra reserved
       unreserved uchar pchar
       fragment
       param params
       segment fsegment path
       rel_path abs_path request_uri
       method http_ver request_line
       header_seg header_value header headers
       body
       simple_req request =>
    (* 0 *)
    (## digit @@ (fun t => nat_of_ascii t - nat_of_ascii "0"%char),

    (* 1 *)
    (## (Group ("?" :: " " :: """" :: "#" :: "%" :: "<" :: ">" :: nil)),
    (## (Group ("$" :: "-" :: "_" :: "." :: nil)),
    (## (Group ("!" :: "*" :: "'" :: "(" :: ")" :: "," :: nil)),
    (## (Group (";" :: "/" :: "?" :: ":" :: "@" :: "&" :: "=" :: "+" :: nil)),

    (* 5 *)
    ((## (Union (Union alpha Alpha) digit)) || safe || extra,
    (unreserved || reserved,
    (uchar || (## (Group (":" :: "@" :: "&" :: "=" :: "+" :: nil))),

    (* 8 *)
    (manyStr (uchar || reserved || (Lit _ "%"%char)) fragment,

    (* 9 *)
    (manyStr (pchar || (Lit _ "/"%char)) param,
    (Map (fun a => String.append (fst a) (snd a))
         (param ^^ (many EmptyString (String.append) (cat ";" param) params)),

    (* 11 *)
    (manyStr pchar segment,
    (many1Str pchar fsegment,
    (Map (fun a => append (fst a) (snd a)) (fsegment ^^ (cat "/" segment)),

    (* 14 *)
    (Map (fun a => append (fst a) (append (fst (snd a)) (snd (snd a))))
         ((optional EmptyString  path) ^^
           ((optional EmptyString (cat ";" params)) ^^
             (optional EmptyString (cat "?" fragment)))), 
(*    (segment, *)
    (cat "/" rel_path,
    (abs_path,

    (* 17 *)
    (enum _ GET (("GET", GET) :: ("POST", POST) :: ("HEAD", HEAD) :: nil)%string,
    ((litString _ tt "HTTP/") ^^ number ^^ (Lit _ "."%char) ^^ number @@ (fun t => (fst (snd t), snd (snd (snd t)))),
    (method ^^ (Lit _ " "%char) ^^ request_uri ^^ (Lit _ " "%char) ^^ http_ver ^^ crlf _ @@ (fun t => (fst t, fst (snd (snd t)), fst (snd (snd (snd (snd t)))))),

    (* 20 *)
    (many1Str (unreserved) header_seg,
    (many1Str (unreserved || extra || reserved || unsafe || (Lit _ " "%char)) header_value,
    (header_seg ^^ (litString _ tt ": ") ^^ header_value ^^ crlf _ @@ (fun t => (fst t, fst (snd (snd t)))),
    (many nil (fun a b => a :: b) header headers,

    (* 24 *)
    (manyStr (## All) body,

    (* 25 *)
    ((litString _ (EmptyString) "GET") ^^ (Lit _ " "%char) ^^ rel_path ^^ crlf _ @@ (fun t => fst (snd (snd t))),
    (request_line ^^ headers ^^ crlf _ ^^ body @@ (fun t => (fst t, fst (snd t), snd (snd (snd t)))),

      tt)))))))))))))))))))))))))))
  ).

Open Local Scope hprop_scope.

Definition HTTP_simple_correct
    (ins : Stream.INSTREAM.instream_t char) (n : [nat]) (a : option (nat * string)) :=
  ans_correct HTTP_env ins n (Var HTTP_ctx 25) a.

Definition simple_http_parse' :=
  AsciiParser.mkparser (HTTP_env) (AsciiParser.Var _ 25).

Definition simple_http_parse : forall (ins : Stream.INSTREAM.instream_t char) (n : [nat]),
  STsep (n ~~ Stream.INSTREAM.rep ins n)
        (fun a : option (nat * string) =>
          HTTP_simple_correct ins n a * rep_ans ins n a) :=
  simple_http_parse'.

Definition HTTP_correct
    (ins : Stream.INSTREAM.instream_t char) (n : [nat]) 
    (a : option (nat * ((method * string * (nat * nat)) * list (string * string) * string))) := 
  ans_correct HTTP_env ins n (Var HTTP_ctx 26) a.

Definition http_parse' := AsciiParser.mkparser (HTTP_env) (AsciiParser.Var _ 26).

Definition http_parse : forall (ins : Stream.INSTREAM.instream_t char) (n : [nat]),
  STsep (n ~~ Stream.INSTREAM.rep ins n)
        (fun a : option (nat * ((method * string * (nat * nat)) * (list (string * string)) * string)) =>
          HTTP_correct ins n a * rep_ans ins n a) :=
  http_parse'.