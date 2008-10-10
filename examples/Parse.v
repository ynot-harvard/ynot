(* This file provides a simple set of parsing combinators, which in Haskell
 * style, take an input stream s, and return a list of parse results.  
 * The input streams are (imperative) ADTs that conceptually represent an
 * offset in some input string, but they can also be implemented e.g., using
 * Unix-style character I/O.  
 * 
 * The parse results are a list of pairs of the form (n,v) where n is 
 * the length of the string that was parsed, and v is the semantic
 * value computed as part of the parse.  
 *
 * A parser p's type is indexed by a grammar term e, which is itself
 * indexed by a set T.  The grammar term denotes a relation between strings 
 * and values of type T, and the guarantee is that p will only return results
 * (n,v) with the property that there exists some string s, such that 
 * the input stream starting at its original offset, has s as a substring
 * of n characters, and (s,v) is in the relation denoted by e.
 *
 * The terms are represented in the style of Adam's lambda-tamer, though
 * the situation here is considerably simpler since we define the semantics
 * of the terms using an inductive type family.  (Nevertheless, there is
 * one theorem that I would like to be able to prove, but have been unable
 * to do so...  As a result, when constructing recursive grammars, one must
 * build a proof that a certain substituton property holds, but I provide
 * a simple tactic to do this automatically, once you unfold definitions.)
 * 
 * I give an example stream implementation, in terms of a string and
 * a ref to hold the current offset, and some example grammars and parsers
 * at the bottom.  Note that the grammars and parsers are parameterized
 * by an arbitrary character set, so it should be possible to first build
 * a lexer that takes the input stream from a list of characters to a
 * list of tokens, and then parse the list of tokens into e.g., an 
 * abstract syntax tree (or other semantic value).
 *
 * TODO:
 *  1. We should probably turn the parsing stuff into a functor.
 * 
 *  2. As noted above, when you use recursion to build a parser, there is 
 *     a proof obligation (regarding unwinding) that must be discharged.
 *     The tactic gtac takes care of this, as long as you unwind all of
 *     the definitions used in the grammar.  But it would be great if the
 *     user didn't have to write this.  
 *
 *  3. It would really be slick if we could analyze the grammar to produce
 *     better combinators.  For example, the alternation combinator could
 *     try to compute first sets of the two parsers it is given, based on
 *     the terms that index those grammars.  If the first sets don't overlap,
 *     then we can peek at the first character in the stream and commit to
 *     one of the parsers or the other.  More generally, we might try
 *     to transform a grammar into LL1 form and then avoid the overhead
 *     of the backtracking all together where possible.  Ultimately, we
 *     should try to do something like packrat parsing where we cut off and
 *     memoize things.
 *
 *  4. It would really be nice to leverage the grammars as indices for pretty-
 *     printing combinators.  The theorem we ought to get out is that if 
 *     PS and PP are a parser and pretty printer for grammar e, then we should
 *     be guaranteed that for any semantic value v, PS(PP v) will succeed and
 *     return v as one of the parse results.  
 *)    

Require Import List.
Require Import Ynot.
Require Import Ascii.
Require Import Omega.
Require Import Eqdep.
Require Import Stream.
Set Implicit Arguments.

(* This section defines grammars and parsers -- should be turned into a
 * functor over the char and char_eq variables. 
 *)
Section Parse.
  Variable char : Set.
  Variable char_eq : forall (c1 c2:char), {c1 = c2} + {c1 <> c2}.

  (* We describe the syntax of grammars using Adam's approach from ltamer *)
  Section vars.
    Variable var : Set -> Type.

    Inductive term : Set -> Type := 
    | GVar : forall t:Set, var t -> term t
    | GVoid : forall t:Set, term t
    | GEpsilon : term unit
    | GLit : char -> term char
    | GCat : forall (t1 t2:Set), term t1 -> term t2 -> term (t1 * t2)
    | GAlt : forall t, term t -> term t -> term t
    | GMap : forall (t1 t2:Set), (t1 -> t2) -> term t1 -> term t2
    | GRec : forall t:Set, (var t -> term t) -> term t.
  End vars.

  Definition Term t := forall V, term V t.

  Definition gvoid := fun t V => GVoid V t.
  Definition gepsilon := fun V => GEpsilon V.
  Definition glit c := fun V => GLit V c.
  Definition gcat t1 t2 (e1 : Term t1) (e2 : Term t2) :=
    fun V => GCat (e1 V) (e2 V).
  Definition galt t (e1 e2 : Term t) := 
    fun V => GAlt (e1 V) (e2 V).
  Definition gmap (t1 t2:Set) (f:t1 -> t2) (e:Term t1) := 
    fun V => GMap f (e V).
  Definition grec (t:Set) (f : forall V:Set->Type, V t -> term V t) : Term t := 
    fun V => GRec (f V).

  Implicit Arguments GVar [var t].
  Implicit Arguments GVoid [var].
  Implicit Arguments GEpsilon [var].
  Implicit Arguments GLit [var].
  Implicit Arguments GCat [var t1 t2].
  Implicit Arguments GAlt [var t].
  Implicit Arguments GRec [var t].
  Implicit Arguments GMap [var t1 t2].

  (* A relational definition of substitution for terms -- used in the definition
   * of the semantics below, in particular for the rec case *)
  Inductive Subst(Var:Set->Type) : 
    forall (t1 t2:Set), (Var t1->term Var t2)->(term Var t1)->(term Var t2)->Type := 
  | SVoid : forall t1 t2 (e:term Var t1), Subst (fun _ => GVoid t2) e (GVoid t2)
  | SEpsilon : forall t1 (e:term Var t1), Subst (fun _ => GEpsilon) e GEpsilon
  | SLit : forall t1 c (e:term Var t1), Subst (fun _ => GLit c) e (GLit c)
  | SCat : 
      forall t1 t2 t3 (f1:Var t1 -> term Var t2) (f2:Var t1 -> term Var t3) (e:term Var t1)
        (e1:term Var t2)(e2:term Var t3),
        Subst f1 e e1 -> Subst f2 e e2 -> 
        Subst (fun v => GCat (f1 v) (f2 v)) e (GCat e1 e2)
  | SAlt : 
      forall t1 t2 (f1 f2:Var t1 -> term Var t2) (e:term Var t1)(e1 e2:term Var t2),
        Subst f1 e e1 -> Subst f2 e e2 -> 
        Subst (fun v => GAlt (f1 v) (f2 v)) e (GAlt e1 e2)
  | SMap : 
       forall (t1 t2 t3:Set) 
         (f:Var t1 -> term Var t2) (e:term Var t1) (g:t2->t3) (e1:term Var t2),
         Subst f e e1 -> 
         Subst (fun v => GMap g (f v)) e (GMap g e1)
  | SVarEq : 
       forall t (e:term Var t), Subst (GVar(var:=Var)(t:=t)) e e
  | SVarNeq : 
       forall t1 t2 (v:Var t2) (e:term Var t1), Subst (fun _ => GVar v) e (GVar v)
  | SRec : 
       forall t1 t2 (f1:Var t1->Var t2->term Var t2) (f2:Var t2->term Var t2)(e:term Var t1), 
         (forall v', Subst (fun v => f1 v v') e (f2 v')) -> 
         Subst (fun v => GRec (f1 v)) e (GRec f2).

  (* Conceptually, a term denotes a predicate on strings and values *)
  Definition denote(t:Set) := list char -> t -> Prop.

  (* Here we give a straightforward semantics for terms as an inductive definition.
     Note that in the rec case, we simply unroll the term via substitution. *)
  Inductive parses : forall (t:Set), term denote t -> list char -> t -> Prop := 
    | parses_epsilon : parses GEpsilon nil tt
    | parses_lit : forall c, parses (GLit c) (c::nil) c
    | parses_cat : forall t1 t2 (e1:term denote t1)(e2:term denote t2) s1 s2 (v1:t1) (v2:t2),
        parses e1 s1 v1 -> parses e2 s2 v2 -> parses (GCat e1 e2) (s1 ++ s2) (v1,v2)
    | parses_alt_left : forall t (e1 e2:term denote t) s (v:t), 
        parses e1 s v -> parses (GAlt e1 e2) s v
    | parses_alt_right : forall t (e1 e2:term denote t) s (v:t), 
        parses e2 s v -> parses (GAlt e1 e2) s v
    | parses_map : forall (t1 t2:Set) (f:t1->t2) (e:term denote t1) s v,
        parses e s v -> parses (GMap f e) s (f v)
    | parses_fix : forall (t:Set) (f:denote t -> term denote t) e s v,
        Subst f (GRec f) e -> parses e s v -> parses (GRec f) s v
    | parses_var : forall (t:Set) (x:denote t) s v, x s v -> parses (GVar x) s v.

  Definition parse_result(t:Set) := (nat * t)%type.
  Definition parse_results t := list (parse_result t).

  Fixpoint list_all(A:Type)(P:A->Prop)(x:list A) {struct x} : Prop := 
    match x with
    | nil => True
    | h::t => (P h) /\ (list_all P t)
    end.

  (* operations for computing a substring *)
  Fixpoint substr_chop(A:Type)(cs:list A)(len:nat) {struct len} : list A := 
    match (len,cs) with
    | (S n,c::cs1) => c :: (substr_chop cs1 n)
    | (_,_) => nil
    end.

  Fixpoint substr(A:Type)(cs:list A)(start:nat)(len:nat) {struct start} : list A := 
    match (start,cs) with
    | (0,cs) => substr_chop cs len
    | (S n,c::cs) => substr cs n len
    | (S n,nil) => nil
    end.

  (* the parse result (m,v) is a possible parse of grammar e with input string ins, 
   * starting at offset n. *)
  Definition possible_parse(t:Set)(e:Term t)(n:nat)(ins:list char)(p:parse_result t) := 
    parses (e denote) (substr ins n (fst p)) (snd p).

  (* all of the parse results in ps are possible parses of grammar e with input
   * stream instream starting at offset n. *)
  Definition possible_parses(t:Set)(e:Term t)(instream:instream_t char)(n:[nat])
                            (ps:parse_results t) := 
    (n ~~ (hprop_unpack (stream_elts instream) 
            (fun ins => [list_all (possible_parse e n ins) ps])))%hprop.

  (* A parser for grammar e, takes an input stream instream and (irrelevant) starting
   * offset n.  It returns the stream in a state where we don't necessarily know what
   * the current offset is, and a list of possible_parses for the grammar e. *)
  Definition parser(instream:instream_t char)(t:Set)(e:Term t)(n:[nat]) := 
    STsep (n ~~ rep instream n)
          (fun ans => 
            ((Exists m :@nat, rep instream m) * (possible_parses e instream n ans))%hprop).

  Definition Parser(t:Set)(e:Term t) := 
    forall (instream:instream_t char)(n:[nat]),parser instream e n.

  Open Local Scope stsep_scope. 

  (* Some simple tactics to help automate the proofs below. *)

  (* For some reason, I have to feed this to sep to get it to simplify *)
  Lemma EmpImpP(P:Prop) : P -> (__ ==> [P]).
  Proof.
    sep red.
  Qed.
    
  Ltac simplr := 
    match goal with
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => 
        generalize (inj_pairT2 _ _ _ _ _ H) ; clear H ; intro ; subst
    | [ |- (__ ==> [?P])%hprop ] => eapply EmpImpP ; simplr
    | [ |- context[char_eq ?e1 ?e2] ] => 
        destruct (char_eq e1 e2) ; subst ; simplr 
    | [ |- _ /\ _ ] => split ; [ simplr | simplr ]
    | [ H:exists x, _ |- _ ] => destruct H ; simplr
    | [ H:_ /\ _ |- _ ] => destruct H ; simplr
    | [ a:(_ * _)%type |- _ ] => destruct a ; simplr
    | [ v:option _ |- _] => destruct v ; [simplr | simplr]
    | [ |- parses (GAlt _ _) _ _ ] => fail 1
    | [ |- parses _ _ _ ] => try econstructor
    | [ H : instream_t char |- _ ] => 
        let stream_elts := fresh "stream_elts" in
        let rep := fresh "rep" in
        let peek := fresh "peek" in
        let next := fresh "next" in
        let pos := fresh "pos" in
        let seek := fresh "seek" in
        let close := fresh "close" in
        destruct H as [stream_elts rep peek next pos seek close] ; simpl ;
          clear peek next pos seek close ; simplr
    | _ => simpl ; eauto
    end.

  Ltac t := 
    unfold Exc, glit, gepsilon, gvoid, galt, gcat, gmap, grec, 
      parse_result, possible_parses, possible_parse in *; 
      sep auto ; repeat (progress simplr).

  Lemma NthErrorSubstr(l:list char)(n:nat)(c:char) : 
       (Some c = nth_error l n) -> substr l n 1 = c::nil.
  Proof.
    induction l ; induction n ; simpl ; unfold error ; intros ; try congruence.
    inversion H. subst. auto. auto.
  Qed.

  (* the literal parser for a character c *)
  Definition lit(c:char) : Parser (glit c).
    intros c instream n. 
    refine (copt <- next instream n ;
            Return (match copt with
                    | None => nil
                    | Some c2 => if char_eq c c2 then (1,c)::nil else nil
                    end) <@> 
                    hprop_unpack (stream_elts instream) 
                      (fun elts => (n ~~ rep instream (1 + n) * 
                                   [copt = nth_error elts n])%hprop) @> _) ; 
    t. t. rewrite (NthErrorSubstr l n0 H). constructor. t. t.
  Defined.

  Lemma SubstrZeroNil(l:list char)(n:nat) : substr l n 0 = nil.
    induction l ; induction n ; simpl ; auto.
  Qed.

  (* the parser for the empty string *)
  Definition epsilon : Parser gepsilon.
    intros instream n.
    refine ({{Return ((0,tt)::nil) <@> (n ~~ rep instream n)}}) ; t. t.
    rewrite (SubstrZeroNil l n0). constructor.
  Defined.

  (* the parser that matches no string *)
  Definition void(t:Set) : Parser (gvoid t).
    intros t instream n.
    refine ({{Return nil <@> (n ~~ rep instream n)}}) ; t. t.
  Defined.

  Lemma AltApp(t:Set)(e1 e2:Term t)(n:nat)(ins:list char)(p1 p2:parse_results t) : 
    list_all (possible_parse e1 n ins) p1 -> 
    list_all (possible_parse e2 n ins) p2 -> 
    list_all (possible_parse (galt e1 e2) n ins) (p1 ++ p2).
  Proof.
    induction p1. simpl. induction p2. auto. simpl. t. apply parses_alt_right. auto.
    simpl. t. apply parses_alt_left. auto.
  Defined.

  (* the parser for (e1 || e2) built from parsers p1 and p2 for e1 and e2 respectively.
   *   Note that seek does not require that we pass in [n] where n is the current
   *   offset in the stream -- and for good reason.  All we know after running the
   *   1st parser is that there exists some offset, but we can't compute it. *)
  Definition alt(t:Set)(e1 e2:Term t)
                (p1:Parser e1)(p2:Parser e2) : Parser (galt e1 e2).
    intros t e1 e2 p1 p2 instream n.
    refine (m <- position instream n @>
              (fun m => n ~~ rep instream n * [m=n])%hprop ;
            r1 <- p1 instream n <@> (n ~~ [m=n])%hprop @> 
              (fun r1 => ((Exists v :@ nat, rep instream v) * 
                          (possible_parses e1 instream n r1) * 
                          (n ~~ [m=n]))%hprop) ;
            seek instream m <@> 
                ((possible_parses e1 instream n r1) * (n ~~ [n=m]))%hprop ;;
            r2 <- p2 instream (inhabits m) <@> 
                ((possible_parses e1 instream n r1 * (n ~~ [n=m]))%hprop) ;
            Return (r1 ++ r2) <@> 
              (((Exists v :@ nat, rep instream v) * 
                (possible_parses e1 instream n r1) * 
                (possible_parses e2 instream n r2) * (n ~~ [n=m]))%hprop)
             @> _) ;
    t. t. apply (AltApp e1 e2 m l r1 r2 H H0).
  Defined.

  Lemma MapParses(t1 t2:Set)(f:t1->t2)(e:Term t1)(n:nat)(s:list char)(r:parse_results t1) : 
    list_all (possible_parse e n s) r -> 
    list_all (possible_parse (gmap f e) n s) (List.map (fun p => (fst p, f (snd p))) r).
  Proof.
    unfold possible_parse. induction r ; auto ; simpl. t. auto.
  Qed.

  (* the parser for (gmap f e) given f and a parser p for e *)
  Definition map(t1 t2:Set)(f:t1->t2)(e:Term t1)(p:Parser e) : Parser (gmap f e).
    unfold Parser. intros t1 t2 f e p instream n.
    refine (r <- p instream n @> 
              (fun r => ((Exists m :@nat, rep instream m) * 
                         (possible_parses e instream n r))%hprop) ;
            Return (List.map (fun p => (fst p, f (snd p))) r)
              <@> ((Exists m :@nat, rep instream m) * (possible_parses e instream n r))%hprop
            @> _); 
    t. t. apply (MapParses f e n0 l r H).
  Defined.

  Lemma SubstrApp(l:list char)(b n m:nat) : 
    (substr l b (n+m)) = (substr l b n) ++ (substr l (n+b) m).
  Proof.
    intros l b n m. assert (n + b = b + n). omega. rewrite H. clear H.
    generalize b n m. clear b n m.
    induction l. induction b ; simpl ; auto ; induction n ; simpl ; auto.
    induction b ; simpl ; auto. induction n ; simpl ; auto. 
    intro. pose (IHl 0 n m). simpl in e. rewrite e. auto.
  Defined.

  (* the following loop iterates over a list of parse results from grammar e1,
   * taking each such (m1,v1), and applies the parser p2 for grammar e2 to the
   * input stream starting at offset n+m1, which yields a new list of parse results
   * matching the grammar e2.  It then maps (fun (m1,v2) => (n+m1),(v1,v2))
   * over these new results to get the compound results, and returns the
   * concatenation of all of the results. *)
  Definition cat_loop(t1 t2:Set)(e1:Term t1)(e2:Term t2)(instream:instream_t char)
                     (n:nat)(p2:Parser e2)
                     (r1 : parse_results t1) : 
      STsep ((Exists m :@ nat,rep instream m) * 
             possible_parses e1 instream (inhabits n) r1)%hprop
            (fun r2 => 
              (Exists m:@ nat, rep instream m) * 
               (possible_parses e1 instream (inhabits n) r1) *
               possible_parses (gcat e1 e2) instream (inhabits n) r2)%hprop.
   intros.
   refine ((fix loop(r1:parse_results t1) {struct r1} : 
            STsep ((Exists m :@nat,rep instream m) * 
                   possible_parses e1 instream (inhabits n) r1)%hprop
                  (fun r2 => 
                    (Exists m:@ nat, rep instream m) * 
                    (possible_parses e1 instream (inhabits n) r1) *
                    possible_parses (gcat e1 e2) instream (inhabits n) r2)%hprop :=
               match r1 as r1' return
                 STsep ((Exists m :@nat,rep instream m) * 
                         possible_parses e1 instream (inhabits n) r1')%hprop
                       (fun r2 => 
                         (Exists m:@ nat, rep instream m) * 
                         (possible_parses e1 instream (inhabits n) r1') *
                         possible_parses (gcat e1 e2) instream (inhabits n) r2)%hprop
               with
               | nil => {{Return nil <@> ((Exists m:@ nat, rep instream m) * 
                                          (possible_parses e1 instream (inhabits n) nil))}}
               | a::tail => 
                  seek instream (fst a + n) 
                    <@> (possible_parses e1 instream (inhabits n) (a::tail)) ;;
                  res1 <- p2 instream (inhabits (fst a + n)) 
                    <@> (possible_parses e1 instream (inhabits n) (a::tail)) 
                    @> (fun res1 => 
                          ((Exists m :@ nat, rep instream m) * 
                           (possible_parses e1 instream (inhabits n) (a::nil)) * 
                           (possible_parses e1 instream (inhabits n) tail) * 
                           (possible_parses e2 instream (inhabits (fst a + n)) res1))%hprop) ;
                  res2 <- loop tail 
                    <@> ((possible_parses e2 instream (inhabits (fst a + n)) res1) * 
                         (possible_parses e1 instream (inhabits n) (a::nil))) ;
                  Return ((List.map (fun pair => (fst a + fst pair, (snd a,snd pair))) res1)
                            ++ res2) 
                    <@> (((Exists m :@ nat, rep instream m) *
                         (possible_parses e1 instream (inhabits n) (a::nil)) *
                         (possible_parses e1 instream (inhabits n) tail) *
                         (possible_parses e2 instream (inhabits (fst a + n)) res1) *
                         (possible_parses (gcat e1 e2) instream (inhabits n) res2))%hprop) @> _
               end) r1) ; 
       clear loop ; t. t. t. t.
       induction res1 ; t. t. rewrite (SubstrApp l n a0 n0). apply (parses_cat H0 H4).
    Defined.

  (* builds a concatenation parser for e1 followed by e2, given appropriate parsers 
   * p1 and p2 *)
  Definition cat(t1 t2:Set)(e1:Term t1)(e2:Term t2)(p1:Parser e1)(p2:Parser e2) : 
                   Parser (gcat e1 e2).
    intros t1 t2 e1 e2 p1 p2 instream n.
    refine (m <- position instream n ;
            r1 <- p1 instream n <@> (n ~~ [n = m])%hprop ;
            cat_loop e1 instream m p2 r1 <@> (n ~~ [n = m])%hprop @> _) ;
    t. t.
  Defined.

  Definition coerce_fix(t:Set)(f:forall V, V t -> term V t)(e:Term t)
                       (H:Subst (f denote) (GRec (f denote)) (e denote))
                       (F:Parser (grec f) -> Parser e)
                       (p:Parser (grec f)) : Parser (grec f).
    intros t f e H F p instream n.
    refine ((F p instream n) @> _) ; t. t. induction v ; auto ; t. t.
  Defined.
                         
  Fixpoint flatten(V:Set->Type)(t:Set)(e: term (term V) t) {struct e} : term V t := 
    match e in (term _ t) return (term V t) with
    | GVar _ v => v
    | GVoid t => GVoid t
    | GEpsilon => GEpsilon
    | GLit c => GLit c
    | GCat t1 t2 e1 e2 => GCat (flatten e1) (flatten e2)
    | GAlt t e1 e2 => GAlt (flatten e1) (flatten e2)
    | GMap t1 t2 f e => GMap f (flatten e)
    | GRec t f => GRec (fun (v:V t) => flatten (f (GVar v)))
    end.

  Definition unroll(t:Set)(f:forall V, V t -> term V t) : Term t := 
    fun V => flatten (f (term V) (GRec (f V))).

  (* Fundamentally, I'm just using SepFix to build a fixed-point.  But I want the
     interface to the user to be:  Given a Parser (grec f), you give me a 
     Parser (unroll f).  So I need to coerce the Parser (unroll f) into a 
     Parser (grec f) so we can compute the fixed-point.  But this coercion
     demands an argument that (grec f) and (unroll f) have the same denotion.
     Alas, I haven't been able to do this directly in spite of the fact that
     for any f:forall V, V t -> term V t, it should be the case that 
     (f denote) (GRec (f denote)) = unroll f denote.  So I'm forced to have
     the user pass in a proof that this property holds -- turns out this is
     trivial to do for any concrete grammar, but it's still annoying.  On the other hand,
     I'd be happy if I could convince Coq to (a) unroll grammar definitions automatically,
     and (b) invoke my gtac tactic below when I'm using Russell or refine.  Then I don't 
     have to rely on any axioms.  
   *)
  Definition Gfix(t:Set)(f:forall V, V t -> term V t)
                  (F:Parser (grec f) -> Parser (unroll f))
                  (Pf:Subst (f denote) (GRec (f denote)) (unroll f denote)) : 
                  Parser (grec f) := 
    (* coerce F so that its result is re-rolled *)
    let Fc : Parser (grec f) -> Parser (grec f) := coerce_fix Pf F in
    (* Grrr. To call SepFix, I have to uncurry Fc *)
    let Fu : (forall arg, parser (fst arg) (grec f) (snd arg)) -> 
             (forall arg, parser (fst arg) (grec f) (snd arg)) := 
       fun f arg => Fc (fun ins n => f (ins,n)) (fst arg) (snd arg) in
    fun instream n => (SepFix _ _ _ Fu) (instream,n).
  Implicit Arguments Gfix [t f instream].

End Parse.


Section Examples.
  Require Import String.
  Delimit Scope grammar_scope with grammar.

  Notation "! v" := (GVar _ _ _ v) (at level 1) : grammar_scope.
  Notation "0" := (GVoid ascii _): grammar_scope.
  Notation "# c" := (GLit(char:=ascii) _ (c%char)) (at level 1) : grammar_scope.
  Notation "e1 ^ e2" := (GCat e1 e2) 
     (right associativity, at level 30) : grammar_scope.
  Notation "e @ f" := (GMap f e)
     (left associativity, at level 78) : grammar_scope.
  Notation "e1 '||' e2" := (GAlt e1 e2)
    (right associativity, at level 79) : grammar_scope.
  Notation "1" := (GEpsilon ascii _) : grammar_scope.

  Delimit Scope parser_scope with parser.

  Notation "e1 ^ e2" := (cat e1 e2) 
     (right associativity, at level 30) : parser_scope.
  Notation "e @ f" := (map f e)
     (left associativity, at level 78) : parser_scope.
  Notation "e1 '||' e2" := (alt e1 e2)
    (right associativity, at level 79) : parser_scope.
  Notation "# c" := (lit ascii_dec (c%char)) (at level 1) : parser_scope.
  Notation "1" := (epsilon(char:=ascii)) : parser_scope.
  Notation "0" := (void _ ascii) : parser_scope.
  Notation "'gfix' e" := (Gfix e _) (at level 70).

  Ltac gtac := unfold unroll, grec ; simpl ; repeat constructor.

  (* Example grammar :  N -> a | b N b *)                
  Definition g : Term ascii unit := 
    grec (fun var N => #"a"             @ (fun _ => tt)  
                    || #"b" ^ !N ^ #"b" @ (fun _ => tt))%grammar.

  (* Example parser for grammar g *)
  Definition g_parser : Parser g.
      refine (gfix (fun (p:Parser g) => 
                      #"a"            @ (fun _ => tt) 
                   || #"b" ^ p ^ #"b" @ (fun _ => tt))%parser) ;
      gtac.
  Defined.

  (* A grammar for digits *)  
  Definition digit := fun V => 
     ((#"0" || #"1" || #"2" || #"3" || #"4" || #"5" || #"6" || #"7" || #"8" || #"9") 
       :term ascii V ascii)%grammar.

  (* A parser for digits *)
  Definition digit_p : Parser digit := 
    (#"0" || #"1" || #"2" || #"3" || #"4" || #"5" || #"6" || #"7" || #"8" || #"9")%parser.

  (* A grammar for numbers:  note that this computes the value of the number *)
  Definition number :=
    grec (fun V number => 
              digit _           @ nat_of_ascii  
           || !number ^ digit _ @ (fun p => 10 * fst p + nat_of_ascii (snd p)))%grammar.

  (* A parser for numbers:  number := digit | number digit *)
  Definition number_p : Parser number.
    refine (gfix (fun (number:Parser number) => 
                digit_p          @ nat_of_ascii
             || number ^ digit_p @ (fun p => 10 * fst p + nat_of_ascii (snd p)))%parser).
    unfold digit. gtac.
  Defined.

  Definition tab : ascii := ascii_of_nat 9.
  Definition cr : ascii := ascii_of_nat 10.

  (* whitespace *)
  Definition ws := 
    grec (fun V ws => 
              1 
          ||  (#" " ^ !ws || #tab ^ !ws || #cr ^ !ws) @ (fun _ => tt))%grammar.

  Definition ws_p : Parser ws.
    refine (gfix (fun (ws_p:Parser ws) => 
                 1 
              || (#" " ^ ws_p || #tab ^ ws_p || #cr ^ ws_p) @ (fun _ => tt))%parser).
    gtac.
  Defined.
      
  (* A grammar for expressions that computes the result of evaluating the expression: 
     expr := number | expr + expr | expr - expr *)
  Definition expr := 
    grec (fun V expr => 
              ws _ ^ number _ ^ ws _   @ (fun t => fst (snd t)) 
           || !expr ^ #"+" ^ !expr     @ (fun t => fst t + (snd (snd t)))
           || !expr ^ #"-" ^ !expr     @ (fun t => fst t - (snd (snd t))))%grammar.

  (* A parser for expressions *)
  Definition expr_p : Parser expr.
    refine (gfix (fun (expr_p:Parser expr) =>
               ws_p ^ number_p ^ ws_p    @ (fun t => fst (snd t))
            || expr_p ^ #"+" ^ expr_p    @ (fun t => fst t + (snd (snd t)))
            || expr_p ^ #"-" ^ expr_p    @ (fun t => fst t - (snd (snd t))))%parser).
    unfold number, digit, ws ; gtac.
  Defined.

  Open Local Scope stsep_scope.

  Lemma StringLen(s:string) : (length s) = (List.length (string_to_list s)).
    induction s ; auto ; simpl. rewrite IHs. auto.
  Qed.

  Lemma SubstrChop(A:Set)(x:list A) : substr_chop x (List.length x) = x.
  Proof.
    induction x ; auto. simpl. rewrite IHx. auto.
  Defined.

  (* The following computation takes a string and returns all of the values from 
   * expressions it can parse from the entire string. *)
  Definition expr_string(s:string) : 
    STsep __ (fun ans => [list_all 
                          (parses (expr (denote ascii)) (string_to_list s)) ans]%hprop).
    intros.
    refine ((* create a stream out of the string *)
            instream <- instream_of_string s ;
            (* run the parser on the stream *)
            res <- expr_p instream (inhabits 0) <@>
              (hprop_unpack (stream_elts instream) 
                (fun elts => [elts = (string_to_list s)]))%hprop ;
            (* destroy the stream *)
            close instream <@> 
              (hprop_unpack (stream_elts instream) 
                (fun elts => [list_all (possible_parse expr 0 elts) res] * 
                             [elts = (string_to_list s)]))%hprop ;;
            (* filter all results that don't consume the whole string *)
            Return (List.map (fun p:nat*nat => snd p)
                     (filter (fun p => if eq_nat_dec (fst p) (String.length s) then true
                                       else false) res))
              <@>
              (hprop_unpack (stream_elts instream) 
                (fun elts => [list_all (possible_parse expr 0 elts) res] * 
                             [elts = (string_to_list s)]))%hprop @> _) ; 
    unfold possible_parses, possible_parse ; sep auto ; destruct instream ; simpl;
      clear peek next position seek close ; sep auto. clear rep. 
    eapply EmpImpP. induction res ; auto ; simpl. destruct a. simpl in *.
    destruct (eq_nat_dec n (length s)). simpl. split. destruct H. subst.
    rewrite (StringLen s) in *. rewrite (SubstrChop (string_to_list s)) in H. auto. 
    sep auto. sep auto.
  Defined.
    
End Examples.
