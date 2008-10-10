Require Import String.
Require Import List. 
Require Import Ascii.
Require Import Omega.
Require Import Eqdep.
Require Import Examples.Stream.

Set Implicit Arguments.

(* This section defines grammars and parsers -- should be turned into a
 * functor over the char and char_eq variables. 
 *)
Section PARSE.
  Variable char : Set.
  Variable char_eq : forall (c1 c2:char), {c1 = c2} + {c1 <> c2}.

  Section GRAMMAR.
  (* We describe the syntax of grammars using Adam's approach from ltamer *)
  Section VARS.
    Variable var : Set -> Type.

    Inductive term: Set -> Type := 
    | GVar     : forall t:Set, var t -> term t
    | GEpsilon : forall t:Set, t -> term t
    | GSatisfy : (char -> bool) -> term char
    | GCat     : forall (t1 t2:Set), term t1 -> term t2 -> term (t1 * t2)
    | GAlt     : forall t, term t -> term t -> term t
    | GTry     : forall t, term t -> term t
    | GRec     : forall t:Set, (var t -> term t) -> term t
    | GMap     : forall (t1 t2:Set), (t1 -> t2) -> term t1 -> term t2.
  End VARS.

  Definition Term t := forall V, term V t.

  Implicit Arguments GVar     [var t].
  Implicit Arguments GEpsilon [var t].
  Implicit Arguments GSatisfy [var].
  Implicit Arguments GCat     [var t1 t2].
  Implicit Arguments GAlt     [var t].
  Implicit Arguments GTry     [var t].
  Implicit Arguments GRec     [var t].
  Implicit Arguments GMap     [var t1 t2].

  (* A relational definition of substitution for terms -- used in the definition
   * of the semantics below, in particular for the rec case *)
  Inductive Subst(Var:Set->Type) : 
    forall (t1 t2:Set), (Var t1->term Var t2)->(term Var t1)->(term Var t2)->Type := 
  | SEpsilon : forall (t1 t2:Set) (v:t2) (e:term Var t1), 
      Subst (fun _ => GEpsilon v) e (GEpsilon v)
  | SSatisfy : forall t1 (f:char->bool) (e:term Var t1), 
       Subst (fun _ => GSatisfy f) e (GSatisfy f)
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
  | STry : 
      forall t1 t2 (f1:Var t1 -> term Var t2) (e : term Var t1) (e1:term Var t2), 
        Subst f1 e e1 -> Subst (fun v => GTry (f1 v)) e (GTry e1)
  | SVarEq : 
       forall t (e:term Var t), Subst (@GVar Var t) e e
  | SVarNeq : 
       forall t1 t2 (v:Var t2) (e:term Var t1), Subst (fun _ => GVar v) e (GVar v)
  | SRec : 
       forall t1 t2 (f1:Var t1->Var t2->term Var t2) (f2:Var t2->term Var t2)(e:term Var t1), 
         (forall v', Subst (fun v => f1 v v') e (f2 v')) -> 
         Subst (fun v => GRec (f1 v)) e (GRec f2).

  Inductive consumed_t : Set := Consumed | NotConsumed.

  Inductive reply_t(a:Set) : Set := 
  | Okay : consumed_t -> a -> list char -> reply_t a
  | Error : consumed_t -> reply_t a.

  Implicit Arguments Error [a].

  Definition join_cons (nc1 nc2 : consumed_t) : consumed_t := 
    match (nc1, nc2) with
    | (Consumed, _) => Consumed
    | (_, Consumed) => Consumed
    | (_, _) => NotConsumed
    end.

  (* We give meaning to grammars here, following the style of Parsec combinators. 
   * In particular, note that we only try the second grammar of an alternation when
   * the first one does not consume input.  The presentation here is slightly different
   * from Parsec in that (a) we don't worry about space leaks since this is intended
   * for specification only, and (b) instead of representing concatenation with a
   * bind-like construct, we simply return a pair of the results.  We have a separate 
   * operation GMap that allows us to transform a t1 grammar to a t2 grammar.  The
   * intention here is that grammars should use a minimum of meta-level stuff in
   * revealing their structure, so that we can potentially analyze and transform them.
   *)
  Section PARSES.
    Variable var : Set -> Type.

    Inductive parses : forall (t:Set), term var t -> list char -> reply_t t -> Prop := 
    | pRec : forall (t:Set) (f:var t -> term var t) e s r, 
                Subst f (GRec f) e -> parses e s r -> parses (GRec f) s r
    | pEpsilon : forall (t:Set) (v:t) s, parses (GEpsilon v) s (Okay NotConsumed v s)
    | pSatisfy : forall (f:char->bool) s r, 
                   r = match s with 
                       | c::cs => if (f c) then Okay Consumed c cs else Error NotConsumed
                       | nil => Error NotConsumed
                       end -> parses (GSatisfy f) s r
    | pMap : forall (t1 t2:Set) (f:t1->t2) e1 r1 r s, 
               parses e1 s r1 -> r = match r1 with 
                                     | Okay nc v s2 => Okay nc (f v) s2
                                     | Error nc => Error nc
                                     end -> parses (GMap f e1) s r
    | pAltR : forall t (e1 e2:term var t) r s, 
              parses e1 s (Error NotConsumed) -> parses e2 s r -> parses (GAlt e1 e2) s r
    | pAltLNC : forall t (e1 e2:term var t) v s2 r2 r s, 
                parses e1 s (Okay NotConsumed v s2) -> 
                parses e2 s r2 -> 
                r = match r2 with
                    | Error NotConsumed => Okay NotConsumed v s2
                    | Okay NotConsumed _ _ => Okay NotConsumed v s2
                    | r2 => r2
                    end -> parses (GAlt e1 e2) s r
    | pAltLCE : forall t (e1 e2:term var t) s, 
                parses e1 s (Error Consumed) -> parses (GAlt e1 e2) s (Error Consumed)
    | pAltLCOK : forall t (e1 e2:term var t) s s2 v, 
                parses e1 s (Okay Consumed v s2) -> parses (GAlt e1 e2) s (Okay Consumed v s2)
    | pTry : forall t (e1:term var t) r1 r s, 
             parses e1 s r1 -> 
             r = match r1 with
                 | Error Consumed => Error NotConsumed
                 | Okay Consumed v s2 => Okay NotConsumed v s2
                 | _ => r1
                 end -> parses (GTry e1) s r
    | pCatE : forall t1 t2 (e1:term var t1) (e2:term var t2) nc s, 
                parses e1 s (Error nc) -> parses (GCat e1 e2) s (Error nc)
    | pCatOK : forall t1 t2 (e1:term var t1) (e2:term var t2) nc1 v1 s1 r2 r s, 
                parses e1 s (Okay nc1 v1 s1) -> 
                parses e2 s1 r2 -> 
                r = match r2 with
                    | Error nc2 => Error (join_cons nc1 nc2)
                    | Okay nc2 v2 s2 => Okay (join_cons nc1 nc2) (v1,v2) s2
                    end -> parses (GCat e1 e2) s r.
  End PARSES.
  End GRAMMAR.

  Require Import Ynot.

  Inductive parse_reply_t(t:Set) : Set := 
  | OKAY : consumed_t -> nat -> t -> parse_reply_t t
  | ERROR : consumed_t -> string -> parse_reply_t t.

  Fixpoint nthtail(A:Type)(cs:list A)(n:nat) {struct n} : list A := 
    match (n,cs) with
    | (0,cs) => cs
    | (S n, c::cs) => nthtail cs n
    | (S n, nil) => nil
    end.

  Definition P(t:Set) := list char -> reply_t t.

  Definition okay(t:Set)(n:[nat])(i:instream_t char)(e:Term t)(c:consumed_t)(m:nat)(v:t) :=
    (n ~~ let elts := stream_elts i in
          elts ~~ [parses (e P) (nthtail elts n) (Okay c v (nthtail elts (m+n)))])%hprop.

  Definition okaystr(t:Set)(n:[nat])(i:instream_t char)(e:Term t)(c:consumed_t)(m:nat)(v:t) :=
    (okay n i e c m v * (n ~~ rep i (m+n)))%hprop.

  Definition error(t:Set)(n:[nat])(i:instream_t char)(e:Term t)(c:consumed_t) := 
    (n ~~ let elts := stream_elts i in
          elts ~~ [parses (e P) (nthtail elts n) (Error t c)])%hprop.

  Definition errorstr(t:Set)(n:[nat])(i:instream_t char)(e:Term t)(c:consumed_t) := 
    (error n i e c * (Exists m :@ nat, rep i m))%hprop.

  Definition ans_correct(t:Set)(n:[nat])(i:instream_t char)(e:Term t)(ans:parse_reply_t t) :=
    match ans with 
    | OKAY c m v => okay n i e c m v
    | ERROR c _ => error n i e c
    end.

  Definition ans_str_correct(t:Set)(n:[nat])(i:instream_t char)(e:Term t)(ans:parse_reply_t t) :=
    match ans with 
    | OKAY c m v => okaystr n i e c m v
    | ERROR c _ => errorstr n i e c
    end.

  Definition parser_t(t:Set)(e:Term t) := 
    forall (ins:instream_t char)(n:[nat]), STsep (n ~~ rep ins n) (ans_str_correct n ins e).
  Implicit Arguments parser_t [t].

  Open Local Scope stsep_scope. 

  Lemma EmpImpInj(P:Prop) : 
    P -> __ ==> [P].
  Proof.
    intros. sep auto.
  Qed.

  Lemma NthErrorNoneNthTail(A:Type)(i:nat)(vs:list A) : 
   nth_error vs i = None -> nthtail vs i = nil.
  Proof.
    induction i ; destruct vs ; auto ; simpl ; intros. unfold value in H. congruence.
    apply IHi. auto.
  Qed.

  Lemma NthErrorSomeNthTail(A:Type)(i:nat)(vs:list A)(v:A) : 
    nth_error vs i = Some v -> 
      exists vs1, exists vs2, vs = vs1 ++ v::vs2 /\ nthtail vs i = v::vs2.
  Proof.
    induction i ; destruct vs ; auto ; simpl ; intros. unfold Specif.error in H. congruence.
    unfold value in H. inversion H. subst. exists (nil(A:=A)). simpl. eauto.
    unfold Specif.error in H. congruence. pose (IHi _ _ H). destruct e as [vs1 [vs2 [H1 H2]]].
    exists (a::vs1). exists vs2. split. rewrite H1. simpl. auto. auto.
  Qed.

  Lemma NthTailSucc(A:Type)(i:nat)(vs vs2:list A)(v:A) : 
    nthtail vs i = v::vs2 -> nthtail vs (S i) = vs2.
  Proof.
    induction i ; simpl ; intros. rewrite H. auto. destruct vs. congruence. 
    pose (IHi _ _ _ H). apply e.
  Qed.

  Ltac mysep := 
    match goal with
    | [ |- (__ ==> [ _ ])%hprop ] => apply EmpImpInj
    | [ H : parses ?e1 ?s (Error _ _) |- parses (GCat ?e1 _) ?s _ ] => 
      eapply pCatE ; eauto
    | [ H : parses ?e1 ?s (Okay _ _ _) |- parses (GCat ?e1 _) ?s _ ] => 
      eapply pCatOK ; eauto
    | [ H : parses ?e1 ?s (Error _ NotConsumed) |- parses (GAlt ?e1 _) ?s _ ] => 
      eapply pAltR ; eauto
    | [ H : parses ?e1 ?s (Okay NotConsumed _ _) |- parses (GAlt ?e1 _) ?s _] => 
      eapply pAltLNC ; eauto
    | [ H : parses ?e1 ?s (Error _ Consumed) |- parses (GAlt ?e1 _) ?s _] => 
      eapply pAltLCE ; eauto
    | [ H : parses ?e1 ?s (Okay Consumed _ _) |- parses (GAlt ?e1 _) ?s _] => 
      eapply pAltLCOK ; eauto
    | [ |- parses _ _ _ ] => econstructor ; eauto
    | [ |- context[hprop_unpack (stream_elts ?ins) _]] => 
      destruct ins as [stream_elts rep peek next position seek close] ; 
        simpl in *; clear peek next position seek close
    | [ |- context[if (?f ?c) then _ else _] ] => 
      let H := fresh "H" in
      assert (H: f c = true \/ f c = false) ; [ destruct (f c) ; tauto | 
              destruct H ; [ rewrite H ; simpl | rewrite H ; simpl ]]
    | _ => auto
    end.

  Definition gsatisfy(f:char -> bool) vars := GSatisfy vars f.
  Definition gepsilon(t:Set)(v:t) vars := GEpsilon vars v.
  Definition galt(t:Set)(e1 e2:Term t) vars := GAlt (e1 vars) (e2 vars).
  Definition gmap(t1 t2:Set)(f:t1 -> t2)(e:Term t1) vars := GMap f (e vars).
  Definition gcat(t1 t2:Set)(e1:Term t1)(e2:Term t2) vars := GCat (e1 vars) (e2 vars).
  Definition gtry(t:Set)(e:Term t) vars := GTry (e vars).
  Definition grec(t:Set)(f:forall (var:Set->Type), var t -> term var t)(var:Set -> Type) :=
    GRec (f var).

  Ltac myunfold := unfold ans_str_correct, ans_correct, okaystr, okay, errorstr, error, 
    gsatisfy, gepsilon, galt, gmap, gcat, gtry, grec.

  Ltac psimp := repeat (progress (myunfold ; sep auto ; mysep ; simpl ; eauto)).

  (* the parser for a single character *)
  Definition satisfy(f:char -> bool) : parser_t (gsatisfy f).
    intros f instream n.
    refine (copt <- next instream n ; 
            Return (match copt with
                    | None => ERROR char NotConsumed "bad character"
                    | Some c => if f c then OKAY Consumed 1 c
                                else ERROR char NotConsumed "bad character"
                    end) <@>
              match copt with 
              | None => errorstr n instream (gsatisfy f) NotConsumed
              | Some c => if f c then okaystr n instream (gsatisfy f) Consumed 1 c
                          else errorstr n instream (gsatisfy f) NotConsumed 
              end @> _) ; psimp. destruct copt ; psimp.
   assert (nth_error l n0 = None \/ (exists c, nth_error l n0 = Some c)).
   destruct (nth_error l n0). right. eauto. left. auto. destruct H. rewrite H ; psimp. 
   rewrite (NthErrorNoneNthTail _ _ H). auto. destruct H. 
   destruct (NthErrorSomeNthTail _ _ H) as [vs1 [vs2 [H1 H2]]]. rewrite H. psimp. rewrite H2. 
   pose (NthTailSucc _ _ H2). simpl in e. rewrite e. rewrite H0. auto. rewrite H2.  
   rewrite H0. auto.
 Defined.
            
  (* the parser for the empty string *)
  Definition epsilon(t:Set)(v:t) : parser_t (gepsilon v).
    intros t v instream n.
    refine ({{Return (OKAY NotConsumed 0 v) <@> (n ~~ rep instream n)}}) ; 
    psimp. 
  Defined.
    
  (* left-biased alternation -- need to fix error message propagation here *)
  Definition alt(t:Set)(e1 e2:Term t)(p1:parser_t e1)(p2:parser_t e2) : parser_t (galt e1 e2).
    intros t e1 e2 p1 p2 instream n.
    unfold galt.
    refine (n0 <- position instream n @> (fun n0 => n ~~ rep instream n * [n0=n])%hprop ; 
            ans1 <- p1 instream n <@> (n ~~ [n0=n])%hprop @> 
               (fun ans1 => ans_str_correct n instream e1 ans1 * (n ~~ [n0=n]))%hprop ;
            let frame := fun ans => ((n ~~ [n0=n]) * ans_correct n instream e1 ans)%hprop in
            match ans1 as ans1' 
              return STsep (ans_str_correct n instream e1 ans1' * (n ~~ [n0=n]))%hprop
                           (ans_str_correct n instream (galt e1 e2))
            with
            | ERROR NotConsumed msg1 => 
                seek instream n0 <@> frame (ERROR t NotConsumed msg1) ;; 
                p2 instream n <@> frame  (ERROR t NotConsumed msg1) @> _
            | OKAY NotConsumed m1 v1 => 
                seek instream n0 <@> frame (OKAY NotConsumed m1 v1) ;; 
                ans2 <- p2 instream n <@> frame (OKAY NotConsumed m1 v1) ;
                match ans2 as ans2' 
                  return STsep (frame (OKAY NotConsumed m1 v1) * 
                                   ans_str_correct n instream e2 ans2')
                               (ans_str_correct n instream (galt e1 e2))
                with
                | ERROR NotConsumed msg2 => 
                    (* interestingly, I forgot to do the seek here and in the next
                       case and then got stuck doing the proof! *)
                    seek instream (m1 + n0) <@> 
                        frame (OKAY NotConsumed m1 v1) *
                        ans_correct n instream e2 (ERROR t NotConsumed msg2) ;;
                    Return OKAY NotConsumed m1 v1 <@> 
                        frame (OKAY NotConsumed m1 v1) * 
                        rep instream (m1 + n0) * 
                        ans_correct n instream e2 (ERROR t NotConsumed msg2) @> _
                | OKAY NotConsumed m2 v2 => 
                    seek instream (m1 + n0) <@> 
                        frame (OKAY NotConsumed m1 v1) *
                        ans_correct n instream e2 (OKAY NotConsumed m2 v2) ;;
                    Return OKAY NotConsumed m1 v1 <@> 
                        frame (OKAY NotConsumed m1 v1) * 
                        rep instream (m1 + n0) * 
                        ans_correct n instream e2 (OKAY NotConsumed m2 v2) @> _
                | ans => 
                    {{Return ans <@> 
                        frame (OKAY NotConsumed m1 v1) * ans_str_correct n instream e2 ans}}
                end
          | ans => 
              {{Return ans <@> 
                 ((n ~~ [n0=n]) * ans_str_correct n instream e1 ans)%hprop}}
          end).
    (* Most of the cases can be discharged with psimp, but in a few cases, this
     * fails because sep generates a constraint variable for an existential goal
     * before introducing certain terms (usually for an hprop_unpack).  So I have
     * to break out those cases and handle them manually. *)
    psimp. psimp. psimp. psimp. unfold ans. psimp. myunfold. sep auto. dependent inversion n.
    psimp. unfold frame. dependent inversion n. psimp. psimp. psimp. 
    unfold frame. psimp. myunfold. dependent inversion n. psimp. 
    unfold frame. psimp. psimp. psimp. psimp. unfold frame, ans ; clear frame ans.
    psimp. psimp. psimp. unfold frame, ans, ans0 ; clear frame ans ans0. psimp. 
    psimp. psimp. unfold frame. dependent inversion n. psimp. psimp. psimp.
    psimp. unfold frame ; clear frame. psimp. destruct v. psimp. psimp.
    unfold frame, ans. dependent inversion n. psimp. psimp. psimp.
  Defined.

  (* the parser for (gmap f e) given f and a parser p for e *)
  Definition map(t1 t2:Set)(f:t1->t2)(e:Term t1)(p:parser_t e) : parser_t (gmap f e).
    intros t1 t2 f e p instream n.
    refine (ans <- p instream n;
            Return (match ans with 
                    | OKAY c m v => OKAY c m (f v)
                    | ERROR c msg => ERROR t2 c msg 
                    end) <@> ans_str_correct n instream e ans @> _) ; psimp.
    destruct ans ; psimp. 
  Defined.

  (* parser for concatenation *)
  Definition cat(t1 t2:Set)(e1:Term t1)(e2:Term t2)(p1:parser_t e1)(p2:parser_t e2) : 
    parser_t (gcat e1 e2).
    intros t1 t2 e1 e2 p1 p2 instream n.
    refine (n0 <- position instream n ;
            ans1 <- p1 instream n <@> (n ~~ [n0 = n])%hprop ; 
            match ans1 as ans1' return 
              STsep (ans_str_correct n instream e1 ans1' * (n ~~ [n0 = n])%hprop)
                    (ans_str_correct n instream (gcat e1 e2))
            with 
            | OKAY c1 m1 v1 => 
                ans2 <- p2 instream (inhabits (m1+n0))<@> 
                   (ans_correct n instream e1 (OKAY c1 m1 v1) * (n ~~ [n0=n]))%hprop; 
                Return match ans2 with
                       | OKAY c2 m2 v2 => OKAY (join_cons c1 c2) (m2 + m1) (v1,v2)
                       | ERROR c2 msg => ERROR (t1*t2)%type (join_cons c1 c2) msg
                       end <@>
                  (ans_correct n instream e1 (OKAY c1 m1 v1) * (n ~~ [n0=n]) *
                   ans_str_correct (inhabits (m1+n0)) instream e2 ans2)%hprop @> _
            | ERROR c1 msg => 
                {{Return ERROR (t1*t2) c1 msg <@> 
                  (ans_str_correct n instream e1 (ERROR t1 c1 msg) * (n ~~ [n0 = n]))%hprop}}
            end) ; psimp.
    destruct ans2 ; psimp. assert (n + (m1 + n1) = n + m1 + n1). omega. rewrite H1.
    psimp. rewrite H1. psimp. 
  Defined.

  (* try combinator *)
  Definition try(t:Set)(e:Term t)(p:parser_t e) : parser_t (gtry e).
    intros t e p instream n.
    refine (ans <- p instream n ; 
            Return match ans with
                   | ERROR Consumed msg => ERROR t NotConsumed msg
                   | OKAY Consumed m v => OKAY NotConsumed m v
                   | ans => ans
                   end <@> ans_str_correct n instream e ans @> _) ; psimp.
    destruct ans ; destruct c ; psimp. 
  Defined.

  (* used in construction of fixed-point *)
  Definition coerce_parse_fn(t:Set)(f:forall var, var t -> term var t)(e:Term t)
                            (H:Subst (f P) (GRec (f P)) (e P))
                            (F:parser_t (grec f) -> parser_t e) : 
                       parser_t (grec f) -> parser_t (grec f).
    intros t f e H1 F p instream n.
    refine ((F p instream n) @> _). destruct v ; psimp.
  Qed. 

  Fixpoint flatten(V:Set->Type)(t:Set)(e: term (term V) t) {struct e} : term V t := 
    match e in (term _ t) return (term V t) with
    | GVar _ v => v
    | GEpsilon t v => GEpsilon V v
    | GSatisfy f => GSatisfy V f
    | GCat t1 t2 e1 e2 => GCat (flatten e1) (flatten e2)
    | GAlt t e1 e2 => GAlt (flatten e1) (flatten e2)
    | GMap t1 t2 f e => GMap f (flatten e)
    | GTry t e => GTry (flatten e)
    | GRec t f => GRec (fun (v:V t) => flatten (f (GVar V t v)))
    end.

  Definition unroll(t:Set)(f:forall V, V t -> term V t) : Term t := 
    fun V => flatten (f (term V) (GRec (f V))).

  Definition parser_t'(t:Set)(e:Term t)(p:(instream_t char * [nat])) := 
    let ins := fst p in
    let n := snd p in
      STsep (n ~~ rep ins n) (ans_str_correct n ins e).

  (* Alas, note that we need H here -- can't easily prove this once and for all *)
  Definition Gfix(t:Set)(f:forall V, V t -> term V t)
                  (F:parser_t (grec f) -> parser_t (unroll f))
                  (H: Subst (f P) (GRec (f P)) (unroll f P)) : 
                  parser_t (grec f) := 
    (* coerce F so that its result is re-rolled *)
    let Fc : parser_t (grec f) -> parser_t (grec f) := coerce_parse_fn H F in
    (* Grrr. To call SepFix, I have to uncurry Fc *)
    let Fu : (forall p, parser_t' (grec f) p) -> (forall p, parser_t' (grec f) p) := 
       fun f arg => Fc (fun ins n => f (ins,n)) (fst arg) (snd arg) in
    fun instream n => (SepFix _ _ _ Fu) (instream,n).
  Implicit Arguments Gfix [t f].
End PARSE.


Section Examples.
  Delimit Scope grammar_scope with grammar.

  Notation "!!!! v" := (GVar _ _ _ v) (at level 1) : grammar_scope.
  Notation "# c" := (GSatisfy(char:=ascii) _ 
                     (fun c2 => if ascii_dec (c%char) c2 then true else false)) 
  (at level 1) : grammar_scope.
  Notation "e1 ^ e2" := (GCat e1 e2) 
     (right associativity, at level 30) : grammar_scope.
  Notation "e @ f" := (GMap f e)
     (left associativity, at level 78) : grammar_scope.
  Notation "e1 '|||' e2" := (GAlt e1 e2)
    (right associativity, at level 79) : grammar_scope.
  Notation "% v" := (GEpsilon ascii _ v) (at level 1) : grammar_scope.

  Delimit Scope parser_scope with parser.

  Notation "e1 ^ e2" := (cat e1 e2) 
     (right associativity, at level 30) : parser_scope.
  Notation "e @ f" := (map f e)
     (left associativity, at level 78) : parser_scope.
  Notation "e1 '|||' e2" := (alt e1 e2)
    (right associativity, at level 79) : parser_scope.
  Notation "# c" := (satisfy (fun c2 => if ascii_dec (c%char) c2 then true else false)) 
    (at level 1) : parser_scope.
  Notation "% v" := (epsilon(char:=ascii) v) : parser_scope.
  Notation "'gfix' e" := (Gfix e _) (at level 70).

  Ltac gtac := unfold unroll, grec ; simpl ; repeat (progress constructor).

  (* Example grammar :  N -> a | b N b *)                
  Definition g : Term ascii unit := 
    grec (fun var N => #"a"             @ (fun _ => tt)  
                    ||| #"b" ^ !!!!N ^ #"b" @ (fun _ => tt))%grammar.

  (* Example parser for grammar g *)
  Definition g_parser : parser_t g.
      refine (gfix (fun (p:parser_t g) => 
                      #"a"            @ (fun _ => tt) 
                   ||| #"b" ^ p ^ #"b" @ (fun _ => tt))%parser) ;
      gtac.
  Defined.

  (* A grammar for digits *)  
  Definition is_digit(c:ascii):bool := 
    if le_lt_dec (nat_of_ascii "0"%char) (nat_of_ascii c) then
      (if le_lt_dec (nat_of_ascii c) (nat_of_ascii "9"%char) then true else false)
    else false.

  Definition digit : Term ascii ascii := gsatisfy is_digit.

  (* A parser for digits *)
  Definition digit_p : parser_t digit := satisfy is_digit.

  (* A grammar for numbers:  note that this computes the value of the number *)
  Definition number :=
    grec (fun V number => 
              digit _           @ nat_of_ascii  
           ||| !!!!number ^ digit _ @ (fun p => 10 * fst p + nat_of_ascii (snd p)))%grammar.

  (* A parser for numbers:  number := digit | number digit *)
  Definition number_p : parser_t number.
    refine (gfix (fun (number:parser_t number) => 
                digit_p          @ nat_of_ascii
             ||| number ^ digit_p @ (fun p => 10 * fst p + nat_of_ascii (snd p)))%parser).
    unfold digit, gsatisfy. gtac. 
  Defined.

  Definition tab : ascii := ascii_of_nat 9.
  Definition cr : ascii := ascii_of_nat 10.

  (* whitespace *)
  Definition ws := 
    grec (fun V ws => 
              % tt
          |||  (#" " ^ !!!!ws ||| #tab ^ !!!!ws ||| #cr ^ !!!!ws) @ (fun _ => tt))%grammar.

  Definition ws_p : parser_t ws.
    refine (gfix (fun (ws_p:parser_t ws) => 
                 % tt 
              ||| (#" " ^ ws_p ||| #tab ^ ws_p ||| #cr ^ ws_p) @ (fun _ => tt))%parser).
    gtac.
  Defined.
      
  (* A grammar for expressions that computes the result of evaluating the expression: 
     expr := number | expr + expr | expr - expr *)
  Definition expr := 
    grec (fun V expr => 
              ws _ ^ number _ ^ ws _   @ (fun t => fst (snd t)) 
           ||| !!!!expr ^ #"+" ^ !!!!expr     @ (fun t => fst t + (snd (snd t)))
           ||| !!!!expr ^ #"-" ^ !!!!expr     @ (fun t => fst t - (snd (snd t))))%grammar.

  (* A parser for expressions *)
  Definition expr_p : parser_t expr.
    refine (gfix (fun (expr_p:parser_t expr) =>
               ws_p ^ number_p ^ ws_p    @ (fun t => fst (snd t))
            ||| expr_p ^ #"+" ^ expr_p    @ (fun t => fst t + (snd (snd t)))
            ||| expr_p ^ #"-" ^ expr_p    @ (fun t => fst t - (snd (snd t))))%parser).
    unfold number, digit, ws, gsatisfy ; gtac.
  Defined.

End Examples.
