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

Inductive method : Set :=
| GET : method | POST : method | HEAD : method.

Definition alpha := Terminal AsciiCharset (ARange "a" "z").
Definition Alpha := Terminal AsciiCharset (ARange "A" "Z").
Definition digit := Terminal AsciiCharset (ARange "0" "9").

Section Combinators.
  Variable base_ty : Set.
  Variable base_ty_denote : base_ty -> Set.
  Definition ty := @ty base_ty.
  Definition tyDenote : ty -> Set := @tyDenote AsciiCharset base_ty base_ty_denote.
  Definition term := @term AsciiCharset.

  Definition many ctx (T S : ty) (t: tyDenote T) (f : tyDenote S -> tyDenote T -> tyDenote T)
    (prin : term _ ctx S) (rec : term _ ctx T) : term _ ctx T :=
    (Alt (Map _ (fun a : tyDenote (Prod S T) => f (fst a) (snd a)) (Seq prin rec))
         (Map _ (fun _ => t) (@Epsilon AsciiCharset base_ty base_ty_denote ctx))).

  Definition many1 ctx (T S : ty) (t: tyDenote S -> tyDenote T) 
    (f : tyDenote S -> tyDenote T -> tyDenote T)
    (prin : term _ ctx S) (rec : term _ ctx T) : term _ ctx T :=
    (Alt (Map _ (fun a:tyDenote (Prod S T) => f (fst a) (snd a)) (Seq prin rec))
         (Map _ (t) (prin))).

  Definition optional ctx (T : ty) (t : tyDenote T) (c : term base_ty_denote  ctx T) : term base_ty_denote ctx T :=
    Alt c (Map _ (fun _ => t) (@Epsilon AsciiCharset base_ty base_ty_denote ctx)).

End Combinators.

Inductive TyIndex : Set :=
| TyString : TyIndex
| TyNat    : TyIndex
| TyMethod : TyIndex
| TyList   : ty TyIndex -> TyIndex.

Fixpoint IndexDenote (ty : TyIndex) : Set :=
  match ty with
    | TyString => string
    | TyNat    => nat
    | TyMethod => method
    | TyList t => list (tyDenote IndexDenote t)
  end.

Definition term' := @term TyIndex IndexDenote.

Definition manyStr ctx : term' ctx (Char TyIndex) -> term' ctx (Base TyString) -> term' ctx (Base TyString) :=
  @many _ _ ctx (Base TyString) (Char TyIndex) EmptyString String.

Definition many1Str ctx : term' ctx (Char TyIndex) -> term' ctx (Base TyString) -> term' ctx (Base TyString) :=
  @many1 _ _ ctx (Base TyString) (Char TyIndex) (fun a => String a EmptyString) String.

Definition cat ctx (c : ascii) (s : term' ctx (Base TyString)) : term' ctx (Base TyString) :=
  @Map AsciiCharset TyIndex IndexDenote ctx (Prod (Char TyIndex) (Base TyString)) (Base TyString)
    (fun a:tyDenote IndexDenote (Prod (Char TyIndex) (Base TyString)) => 
           String (fst a) (snd a)) (Seq (Lit AsciiCharset IndexDenote ctx c) s).

Fixpoint litString ctx {T : ty TyIndex} (t : tyDenote _ T) (s : string) : term' ctx T :=
  match s with
    | EmptyString => (Map _ (fun _ => t) (@Epsilon AsciiCharset TyIndex IndexDenote ctx))
    | String a r => (Map _ (fun _ => t) (Seq (Lit AsciiCharset IndexDenote ctx a) (litString ctx t r)))
  end.

(* Notation "# c" := (AsciiParser.Lit _ c%char) (at level 1) : grammar_scope. *)
Notation "## c" := (@LitClass AsciiCharset TyIndex IndexDenote _ c%char) (at level 1) : grammar_scope.
Notation "e1 ^^ e2" := (@Seq AsciiCharset TyIndex IndexDenote _ _ _ e1 e2) (right associativity, at level 30) : grammar_scope.
Notation "e @@ f" := (@Map AsciiCharset TyIndex IndexDenote _ _ _ f e) (left associativity, at level 78) : grammar_scope.
Notation "e1 ||| e2" := (Alt e1 e2) (right associativity, at level 79) : grammar_scope.

Definition Lit := @Lit AsciiCharset TyIndex IndexDenote.
Definition Map := @Map AsciiCharset TyIndex IndexDenote.
Definition Seq := @Seq AsciiCharset TyIndex IndexDenote.

Open Local Scope grammar_scope.

Fixpoint enum ctx {T : ty TyIndex} (t' : tyDenote _ T) (t : list (string * tyDenote _ T)) : term' ctx T :=
  match t with
    | nil => ## (Group AsciiCharset nil) @@ (fun _ => t') (** This is essentially the error production **)
    | (str,v) :: r => (litString _ v str) ||| enum ctx t' r
  end.

Definition crlf ctx : term' ctx (Unit TyIndex) := 
  @Map ctx (Prod (Char TyIndex) (Char TyIndex)) (Unit TyIndex) (fun _ => tt)
    ((Lit ctx (ascii_of_nat 13)) ^^ (Lit ctx (ascii_of_nat 10))).

Definition sp ctx : term' ctx (Unit TyIndex) := 
  @Map ctx (Char TyIndex) (Unit TyIndex) (fun _ => tt)
    (Lit ctx " "%char).

Definition verTy := Prod (Base TyNat) (Base TyNat).
Definition reqLineTy := Prod (Prod (Base TyMethod) (Base TyString)) verTy.
Definition headerTy := Prod (Base TyString) (Base TyString).
Definition headersTy := Base (TyList headerTy).


Definition HTTP_ctx : Ctxt TyIndex := 
       ((Base TyNat) ::
        (Char TyIndex) :: (Char TyIndex) :: (Char TyIndex) :: (Char TyIndex) ::
        (Char TyIndex) :: (Char TyIndex) :: (Char TyIndex) ::
        (Base TyString) ::
        (Base TyString) :: (Base TyString) ::
        (Base TyString) :: (Base TyString) :: (Base TyString) ::
        (Base TyString) :: (Base TyString) :: (Base TyString) ::
        (Base TyMethod) :: (Prod (Base TyNat) (Base TyNat)) :: reqLineTy ::
        (Base TyString) :: (Base TyString) :: headerTy :: headersTy ::
        (Base TyString) :: 
        (Base TyString) :: Prod (Prod reqLineTy headersTy) (Base TyString):: nil)%type.

Definition many' := @many TyIndex IndexDenote HTTP_ctx.
Definition optional' := @optional TyIndex IndexDenote HTTP_ctx.
Definition HTTP_env :=
  gfix AsciiCharset IndexDenote HTTP_ctx
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
    (@Map HTTP_ctx _ (Base TyNat) 
      (fun t:tyDenote _ (Char TyIndex) => nat_of_ascii t - nat_of_ascii "0"%char) (## digit),

    (* 1 *)
    (## (Group AsciiCharset ("?" :: " " :: """" :: "#" :: "%" :: "<" :: ">" :: nil)),
    (## (Group AsciiCharset ("$" :: "-" :: "_" :: "." :: nil)),
    (## (Group AsciiCharset ("!" :: "*" :: "'" :: "(" :: ")" :: "," :: nil)),
    (## (Group AsciiCharset (";" :: "/" :: "?" :: ":" :: "@" :: "&" :: "=" :: "+" :: nil)),

    (* 5 *)
    ((## (Union (Union alpha Alpha) digit)) ||| safe ||| extra,
    (unreserved ||| reserved,
    (uchar ||| (## (Group AsciiCharset (":" :: "@" :: "&" :: "=" :: "+" :: nil))),

    (* 8 *)
    (manyStr (uchar ||| reserved ||| (Lit _ "%"%char)) fragment,

    (* 9 *)
    (manyStr (pchar ||| (Lit _ "/"%char)) param,
    (@Map HTTP_ctx (Prod (Base TyString) (Base TyString)) (Base TyString) (fun a => String.append (fst a) (snd a))
         (param ^^ (@many' (Base TyString) (Base TyString) EmptyString (String.append) (cat ";" param) params)),

    (* 11 *)
    (manyStr pchar segment,
    (many1Str pchar fsegment,
    (@Map HTTP_ctx (Prod (Base TyString) (Base TyString)) (Base TyString)
          (fun a => append (fst a) (snd a)) (fsegment ^^ (cat "/" segment)),

    (* 14 *)
    (@Map HTTP_ctx (Prod (Base TyString) (Prod (Base TyString) (Base TyString))) (Base TyString)
         (fun a => append (fst a) (append (fst (snd a)) (snd (snd a))))
         ((@optional' (Base TyString) EmptyString  path) ^^
           ((@optional' (Base TyString) EmptyString (cat ";" params)) ^^
             (@optional' (Base TyString) EmptyString (cat "?" fragment)))), 
(*    (segment, *)
    (cat "/" rel_path,
    (abs_path,

    (* 17 *)
    (@enum HTTP_ctx (Base TyMethod) GET (("GET", GET) :: ("POST", POST) :: ("HEAD", HEAD) :: nil)%string,
    (@Map HTTP_ctx (Prod (Unit TyIndex) (Prod (Base TyNat) (Prod (Char TyIndex) (Base TyNat)))) (Prod (Base TyNat) (Base TyNat))
          (fun t => (fst (snd t), snd (snd (snd t))))
          ((@litString HTTP_ctx (Unit TyIndex) tt "HTTP/") ^^ number ^^ (Lit _ "."%char) ^^ number),
    (@Map HTTP_ctx (Prod (Base TyMethod) (Prod (Char TyIndex) (Prod (Base TyString) (Prod (Char TyIndex) (Prod (Prod (Base TyNat) (Base TyNat)) (Unit TyIndex))))))
                   reqLineTy
          (fun t => (fst t, fst (snd (snd t)), fst (snd (snd (snd (snd t))))))
          (method ^^ (Lit _ " "%char) ^^ request_uri ^^ (Lit _ " "%char) ^^ http_ver ^^ crlf _),

    (* 20 *)
    (many1Str (unreserved) header_seg,
    (many1Str (unreserved ||| extra ||| reserved ||| unsafe ||| (Lit _ " "%char)) header_value,
    (@Map HTTP_ctx (Prod (Base TyString) (Prod (Unit TyIndex) (Prod (Base TyString) (Unit TyIndex))))
                   headerTy
          (fun t => (fst t, fst (snd (snd t))))
          (header_seg ^^ (@litString HTTP_ctx (Unit TyIndex) tt ": ") ^^ header_value ^^ crlf _),
    (@many' headersTy headerTy
            nil (fun a b => a :: b)
            header headers,

    (* 24 *)
    (manyStr (## (All AsciiCharset)) body,

    (* 25 *)
    (@Map HTTP_ctx (Prod (Unit TyIndex) (Prod (Char TyIndex) (Prod (Base TyString) (Unit TyIndex))))
                   (Base TyString)
          (fun t => fst (snd (snd t)))
          ((@litString HTTP_ctx (Unit TyIndex) tt "GET") ^^ (Lit _ " "%char) ^^ rel_path ^^ crlf _),
    (@Map HTTP_ctx (Prod reqLineTy (Prod headersTy (Prod (Unit TyIndex) (Base TyString))))
                   (Prod (Prod reqLineTy headersTy) (Base TyString))
          (fun t => (fst t, fst (snd t), snd (snd (snd t))))
          (request_line ^^ headers ^^ crlf _ ^^ body),

      tt)))))))))))))))))))))))))))
 ).

Open Local Scope hprop_scope.

Definition HTTP_simple_correct
    (ins : Stream.INSTREAM.instream_t ascii) (n : nat) (a : option (nat * string)) :=
  ans_correct HTTP_env ins n [Var AsciiCharset IndexDenote HTTP_ctx 25]%inhabited a.

Definition simple_http_parse' :=
  mkparser (HTTP_env) (Var AsciiCharset IndexDenote HTTP_ctx 25).

Definition simple_http_parse : forall (ins : Stream.INSTREAM.instream_t ascii) (n : nat),
  STsep (Stream.INSTREAM.rep ins n)
        (fun a : option (nat * string) =>
          HTTP_simple_correct ins n a * rep_ans AsciiCharset ins n a) :=
  simple_http_parse'.

Eval compute in tyDenote IndexDenote (Prod (Base TyMethod) (Prod (Base TyString) (Prod (Base TyNat) (Base TyNat)))).

Definition HTTP_correct
    (ins : Stream.INSTREAM.instream_t ascii) (n : nat) 
    (a : option (nat * ((method * string * (nat * nat)) * list (string * string) * string))) := 
  ans_correct HTTP_env ins n [Var AsciiCharset IndexDenote HTTP_ctx 26]%inhabited a.

Definition http_parse' := mkparser (HTTP_env) (Var AsciiCharset IndexDenote HTTP_ctx 26).

Definition http_parse : forall (ins : Stream.INSTREAM.instream_t ascii) (n : nat),
  STsep (Stream.INSTREAM.rep ins n)
        (fun a : option (nat * ((method * string * (nat * nat)) * (list (string * string)) * string)) =>
          HTTP_correct ins n a * rep_ans AsciiCharset ins n a) :=
  http_parse'.