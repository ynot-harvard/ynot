Require Import List. 
Require Import Ascii.
Require Import Omega.
Require Import Stream.
Require Import Charset.
Import INSTREAM.

Set Implicit Arguments.

Section CHARSET.
  Variable charset : Charset.

  Definition char := char charset.

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

  (* A relational definition of substitution for terms -- used in the definition
   * of the semantics below, in particular for the rec case *)
  Inductive Subst :
    forall (t1 t2:Set), (var t1->term t2)->(term t1)->(term t2)->Type := 
  | SEpsilon : forall (t1 t2:Set) (v:t2) (e:term t1), 
    Subst (fun _ => GEpsilon v) e (GEpsilon v)
  | SSatisfy : forall t1 (f:char->bool) (e:term t1), 
    Subst (fun _ => GSatisfy f) e (GSatisfy f)
  | SCat : 
    forall t1 t2 t3 (f1:var t1 -> term t2) (f2:var t1 -> term t3) (e:term t1)
      (e1:term t2)(e2:term t3),
      Subst f1 e e1 -> Subst f2 e e2 -> 
      Subst (fun v => GCat (f1 v) (f2 v)) e (GCat e1 e2)
  | SAlt : 
    forall t1 t2 (f1 f2:var t1 -> term t2) (e:term t1)(e1 e2:term t2),
      Subst f1 e e1 -> Subst f2 e e2 -> 
      Subst (fun v => GAlt (f1 v) (f2 v)) e (GAlt e1 e2)
  | SMap :
    forall (t1 t2 t3:Set) 
      (f:var t1 -> term t2) (e:term t1) (g:t2->t3) (e1:term t2),
      Subst f e e1 -> 
      Subst (fun v => GMap g (f v)) e (GMap g e1)
  | STry : 
    forall t1 t2 (f1:var t1 -> term t2) (e : term t1) (e1:term t2), 
      Subst f1 e e1 -> Subst (fun v => GTry (f1 v)) e (GTry e1)
  | SVarEq : 
    forall t (e:term t), Subst (@GVar t) e e
  | SVarNeq : 
    forall t1 t2 (v:var t2) (e:term t1), Subst (fun _ => GVar v) e (GVar v)
  | SRec : 
    forall t1 t2 (f1:var t1->var t2->term t2) (f2:var t2->term t2)(e:term t1), 
      (forall v', Subst (fun v => f1 v v') e (f2 v')) -> 
      Subst (fun v => GRec (f1 v)) e (GRec f2).
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

Fixpoint flatten(V:Set->Type)(t:Set)(e: term (term V) t) {struct e} : term V t := 
  match e in (term _ t) return (term V t) with
    | GVar _ v => v
    | GEpsilon t v => GEpsilon v
    | GSatisfy f => GSatisfy f
    | GCat t1 t2 e1 e2 => GCat (flatten e1) (flatten e2)
    | GAlt t e1 e2 => GAlt (flatten e1) (flatten e2)
    | GMap t1 t2 f e => GMap f (flatten e)
    | GTry t e => GTry (flatten e)
    | GRec t f => GRec (fun (v:V t) => flatten (f (GVar v)))
  end.

Definition unroll(t:Set)(f:forall V, V t -> term V t) : Term t := 
  fun V => flatten (f (term V) (GRec (f V))).

Definition empvar := (fun _:Set => Empty_set).

(* It would be nice if we could prove the following axiom so that the definition
 * of Gfix was simpler: 
Axiom Unroll : forall (t:Set)(f:forall var, var t -> term var t), 
  Subst (f empvar) (GRec (f empvar)) (unroll f empvar).
 *)

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
 * the first one does not consume input.  The presentation here is slightly di fferent
 * from Parsec in that (a) we don't worry about space leaks since this is intended
 * for specification only, and (b) instead of representing concatenation with a
 * bind-like construct, we simply return a pair of the results.  We have a separate 
 * operation GMap that allows us to transform a t1 grammar to a t2 grammar.  The
 * intention here is that grammars should use a minimum of meta-level stuff in
 * revealing their structure, so that we can potentially analyze and transform them.
 *)

(* What I'm doing here is defining a denotational semantics that maps grammar terms
 * down to a simpler language with a monadic structure.  Then we give an operational
 * semantics to the monadic structure.  Note that I've instantiated the var in the
 * phoas so that it always yields an empty set.  This ensures that the term does not
 * have a free variable.  *)
Inductive M: Set -> Type := 
| MReturn : forall t, reply_t t -> M t
| MBind : forall t1 t2, M t1 -> (reply_t t1 -> M t2) -> M t2
| MFix : forall t (f:empvar t -> term empvar t), list char -> M t.

Notation "'Return' x" := (MReturn x) (at level 75) : gdenote_scope.
Notation "x <- c1 ; c2" := (MBind c1 (fun x => c2)) 
  (right associativity, at level 84, c1 at next level) : gdenote_scope.

Definition wfCoerce (t:Set)(v:empvar t) : M t := match v with end.

Open Local Scope gdenote_scope.

(* here we map a term e to a computation over lists of characters -- this is
 * essentially the same as with Parsec-style combinators, though I've chosen
 * slightly different combinators that are closer to arrows than the monadic
 * interpretation.  *)
Fixpoint denote(t:Set)(e:term empvar t)(s:list char) {struct e} : M t := 
  match e in term _ t return M t with
    | GVar _ v => wfCoerce v
    | GEpsilon _ x => Return Okay NotConsumed x s
    | GSatisfy test => 
      Return match s with
               | c :: cs => if (test c) then Okay Consumed c cs else 
                 Error NotConsumed
               | nil => Error NotConsumed
             end
    | GMap t1 t2 f e => 
      r <- denote e s ;
      Return match r with 
               | Okay nc v s2 => Okay nc (f v) s2
               | Error nc => Error nc
             end
    | GTry t e => 
      r <- denote e s ;
      Return match r with
               | Error Consumed => Error NotConsumed
               | Okay Consumed v s2 => Okay NotConsumed v s2
               | _ => r
             end
    | GCat t1 t2 e1 e2 => 
      r1 <- denote e1 s ;
      match r1 with 
        | Error nc => Return Error nc
        | Okay nc1 v1 s1 => 
          r2 <- denote e2 s1 ;
          Return match r2 with 
                   | Error nc2 => Error (join_cons nc1 nc2)
                   | Okay nc2 v2 s2 => Okay (join_cons nc1 nc2) (v1,v2) s2
                 end
      end
    | GAlt t e1 e2 => 
      r1 <- denote e1 s ; 
      match r1 with
        | Error Consumed => Return Error Consumed
        | Error NotConsumed => denote e2 s
        | Okay NotConsumed v s2 => 
          r2 <- denote e2 s ;
          Return match r2 with 
                   | Error NotConsumed => Okay NotConsumed v s2
                   | Okay NotConsumed _ _ => Okay NotConsumed v s2
                   | r2 => r2
                 end
        | Okay Consumed v s2 => Return Okay Consumed v s2
      end
    | GRec t f => MFix f s
  end.
  
(* We now give an operational semantics to the monadic terms generated by the
 * denotation function.  Note that in essence, we just delay unrolling the 
 * fix operator.  *)
Inductive evals : forall t, M t -> reply_t t -> Prop := 
| eMReturn : forall t (r:reply_t t), evals (MReturn r) r
| eMBind : forall t1 t2 (c:M t1) (r1:reply_t t1) (f:reply_t t1 -> M t2) r2, 
  evals c r1 -> evals (f r1) r2 -> evals (MBind c f) r2
| eMFix : 
  forall t (f:empvar t -> term empvar t) (s:list char) (e:term empvar t) (r:reply_t t), 
    Subst f (GRec f) e -> evals (denote e s) r -> evals (MFix f s) r.

(* Then we say that a term t parses string s yielding result r if the following
 * if evaluating the denotation of e, when applied to s yields r. *)
Definition parses(t:Set)(e:Term t)(s:list char)(r:reply_t t) := 
  evals (denote (e empvar) s) r.

Inductive parse_reply_t(t:Set) : Set :=
| OKAY  : consumed_t -> nat -> t -> parse_reply_t t
| ERROR : consumed_t -> list ascii -> parse_reply_t t.

Fixpoint nthtail(A:Type)(cs:list A)(n:nat) {struct n} : list A := 
  match (n,cs) with
    | (0,cs) => cs
    | (S n, c::cs) => nthtail cs n
    | (S n, nil) => nil
  end.

Require Import Ynot. 

Definition okay(t:Set)(n: [nat])(i:instream_t char)(e:Term t)(c:consumed_t)(m:nat)(v:t) :=
  (n ~~ let elts := stream_elts i in
        elts ~~ [parses e (nthtail elts n) (Okay c v (nthtail elts (m+n)))])%hprop.

Definition okaystr(t:Set)(n:[nat])(i:instream_t char)(e:Term t)(c:consumed_t)(m:nat)(v:t) :=
  (okay n i e c m v * (n ~~ rep i (m+n)))%hprop.

Definition error(t:Set)(n:[nat])(i:instream_t char)(e:Term t)(c:consumed_t) := 
  (n ~~ let elts := stream_elts i in
        elts ~~ [parses e (nthtail elts n) (Error c)])%hprop.

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
  intros. sep fail auto.
Qed.

Lemma NthErrorNoneNthTail(A:Type)(i:nat) : forall (vs:list A),
  nth_error vs i = None -> nthtail vs i = nil.
Proof.
  induction i ; destruct vs ; auto ; simpl ; intros. unfold value in H. congruence.
  apply IHi. auto.
Qed.

Lemma NthErrorSomeNthTail(A:Type)(i:nat) : forall (vs:list A)(v:A),
  nth_error vs i = Some v -> 
  exists vs1, exists vs2, vs = vs1 ++ v::vs2 /\ nthtail vs i = v::vs2.
Proof.
  induction i ; destruct vs ; auto ; simpl ; intros. unfold Specif.error in H. congruence.
  unfold value in H. inversion H. subst. exists (nil(A:=A)). simpl. eauto.
  unfold Specif.error in H. congruence. pose (IHi _ _ H). destruct e as [vs1 [vs2 [H1 H2]]].
  exists (a::vs1). exists vs2. split. rewrite H1. simpl. auto. auto.
Qed.

Lemma NthTailSucc(A:Type)(i:nat) : forall (vs vs2:list A)(v:A),
  nthtail vs i = v::vs2 -> nthtail vs (S i) = vs2.
Proof.
  induction i ; simpl ; intros. rewrite H. auto. destruct vs. congruence. 
  pose (IHi _ _ _ H). apply e.
Qed.

Lemma PlusAssoc(n m p:nat) : n + (m + p) = n + m + p. intros ; omega.
Qed.

Ltac mysep := 
  match goal with
    | [ |- (__ ==> [ _ ])%hprop ] => apply EmpImpInj
    | [ |- evals (MReturn ?r) ?r ] => constructor
    | [ |- evals (MBind _ _) _] => econstructor
    | [ |- context[?n + (?m + ?p)]] => rewrite (PlusAssoc n m p)
    | [ |- context[if (?f ?c) then _ else _] ] => 
      let H := fresh "H" in
      assert (H: f c = true \/ f c = false) ; [ destruct (f c) ; tauto | 
              destruct H ; [ rewrite H ; simpl | rewrite H ; simpl ]]
    | _ => auto
  end.

Definition lower (P : char -> Prop) (v : forall c : char, {P c} + {~P c}) : char -> bool := fun c => if v c then true else false.

Definition gsatisfy(f:char -> bool) vars := GSatisfy (var:=vars) f.
Definition gclass(cl:CharClass charset) vars := GSatisfy (var:=vars) (@lower (DenoteClass cl) (In_CharClass_dec cl)).
Definition gepsilon(t:Set)(v:t) vars := GEpsilon (var:=vars) v.
Definition galt(t:Set)(e1 e2:Term t) vars := GAlt (e1 vars) (e2 vars).
Definition gmap(t1 t2:Set)(f:t1 -> t2)(e:Term t1) vars := GMap f (e vars).
Definition gcat(t1 t2:Set)(e1:Term t1)(e2:Term t2) vars := GCat (e1 vars) (e2 vars).
Definition gtry(t:Set)(e:Term t) vars := GTry (e vars).
Definition grec(t:Set)(f:forall (var:Set->Type), var t -> term var t)(var:Set -> Type) := GRec (f var).

Ltac myunfold := unfold ans_str_correct, ans_correct, okaystr, okay, errorstr, error, 
  parses, gsatisfy, gepsilon, galt, gmap, gcat, gtry, grec.

Ltac psimp := (myunfold ; sep fail auto ; mysep ; simpl ; eauto).

Ltac rsimp := psimp ; 
  match goal with 
    | [ |- context[match ?a with | OKAY c m v => _ | ERROR c _ => _ end] ] => destruct a
    | [ |- context[match ?c with | Consumed => _ | NotConsumed => _ end] ] => destruct c
    | _ => idtac
  end.

Lemma NthError(x:list char)(n:nat) : 
  (nth_error x n = None \/ exists c, nth_error x n = Some c).
Proof.  intros. destruct (nth_error x n). right. eauto. left. eauto.
Qed.

Lemma EvalsMReturn(t:Set)(r1 r2:reply_t t) : r1 = r2 -> evals (MReturn r1) r2.
Proof. intros. rewrite <- H. constructor. Qed.

Open Scope char_scope.

Definition bad_character := "b"::"a"::"d"::" "::"c"::"h"::"a"::"r"::"a"::"c"::"t"::"e"::"r"::nil.

(* the parser for a single character *)
Definition satisfy(f:char -> bool) : parser_t (gsatisfy f).
  intros instream n.
  refine (copt <- next instream n ; 
          Return (match copt with
                    | None => ERROR char NotConsumed bad_character
                    | Some c => if f c then OKAY Consumed 1 c
                                else ERROR char NotConsumed bad_character
                  end) <@>
                    match copt with 
                      | None => errorstr n instream (gsatisfy f) NotConsumed
                      | Some c => if f c then okaystr n instream (gsatisfy f) Consumed 1 c
                                  else errorstr n instream (gsatisfy f) NotConsumed 
                    end @> _);
  psimp ; solve [ sep fail auto |
    match goal with 
      [ |- _ ==> match nth_error ?x ?n with | Some c => _ | None => _ end] => 
      let H := fresh in pose (H := NthError x n) ; destruct H ; [ rewrite H ; psimp ; 
        rewrite (NthErrorNoneNthTail _ _ H) ; psimp | destruct H ; rewrite H ; psimp ; psimp ;
          let H1 := fresh in let v1 := fresh in let v2 := fresh in 
            let H2 := fresh in let H3 := fresh in 
          pose (H1 := NthErrorSomeNthTail _ _ H) ; destruct H1 as [v1 [v2 [H1 H2]]] ; 
          rewrite H2 ; psimp ; pose (H3 := (NthTailSucc _ _ H2)) ; 
          simpl in H3 ; eapply EvalsMReturn ; congruence]
      | [ |- match ?copt with | Some c => _ | None => _ end ==> _] => destruct copt ;
        repeat psimp 
    end ].
Qed.

Definition class(cl:CharClass charset) : parser_t (gsatisfy (@lower (DenoteClass cl) (In_CharClass_dec cl))) := satisfy (@lower (DenoteClass cl) (In_CharClass_dec cl)).

(* the parser for the empty string *)
Definition epsilon(t:Set)(v:t) : parser_t (gepsilon v).
  intros instream n.
  refine ({{Return (OKAY NotConsumed 0 v) <@> (n ~~ rep instream n)}}) ; 
  repeat psimp. 
Qed.
    
(* left-biased alternation -- need to fix error message propagation here *)
Definition alt(t:Set)(e1 e2:Term t)(p1:parser_t e1)(p2:parser_t e2) : parser_t (galt e1 e2).
  intros instream n. unfold galt.
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
          end) ; 
  (try unfold frame) ; repeat rsimp.
Qed.

(* the parser for (gmap f e) given f and a parser p for e *)
Definition map(t1 t2:Set)(f:t1->t2)(e:Term t1)(p:parser_t e) : parser_t (gmap f e).
  intros instream n.
  refine (ans <- p instream n;
          Return (match ans with 
                    | OKAY c m v => OKAY c m (f v)
                    | ERROR c msg => ERROR t2 c msg 
                  end) <@> ans_str_correct n instream e ans @> _) ; psimp.
  destruct ans ; repeat psimp. 
Qed.

(* parser for concatenation *)
Definition cat(t1 t2:Set)(e1:Term t1)(e2:Term t2)(p1:parser_t e1)(p2:parser_t e2) : 
  parser_t (gcat e1 e2).
  intros instream n.
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
          end) ; repeat rsimp.
Qed.

(* try combinator *)
Definition try(t:Set)(e:Term t)(p:parser_t e) : parser_t (gtry e).
  intros instream n.
  refine (ans <- p instream n ; 
         Return match ans with
                   | ERROR Consumed msg => ERROR t NotConsumed msg
                   | OKAY Consumed m v => OKAY NotConsumed m v
                   | ans => ans
                end <@> ans_str_correct n instream e ans @> _) ; psimp.
  destruct ans ; destruct c ; repeat psimp.
Qed.

(* used in construction of fixed-point *)
Definition coerce_parse_fn(t:Set)(f:forall var, var t -> term var t)(e:Term t)
                            (H1:Subst (f empvar) (GRec (f empvar)) (e empvar))
                            (F:parser_t (grec f) -> parser_t e) : 
                       parser_t (grec f) -> parser_t (grec f).
  intros p instream n.
  refine ((F p instream n) @> _). sep fail auto.  sep fail auto. destruct v ; psimp ; econstructor ; eauto.
Qed. 

Definition parser_t'(t:Set)(e:Term t)(p:(instream_t char * [nat])) := 
  let ins := fst p in
  let n := snd p in
  STsep (n ~~ rep ins n) (ans_str_correct n ins e).

Open Local Scope stsepi_scope.

(* Alas, note that we need H here -- can't easily prove this once and for all *)
Definition Gfix(t:Set)(f:forall V, V t -> term V t)
               (F:parser_t (grec f) -> parser_t (unroll f))
               (H: Subst (f empvar) (GRec (f empvar)) (unroll f empvar)) : 
               parser_t (grec f) :=
  (* coerce F so that its result is re-rolled *)
  let Fc : parser_t (grec f) -> parser_t (grec f) := coerce_parse_fn H F in
  Fix2 _ _ Fc.

Implicit Arguments Gfix [t f].

End CHARSET.

Module ParsecNotation.

  Delimit Scope grammar_scope with grammar.

  Notation "!!!! v" := (@GVar _ _ _ v) (at level 1) : grammar_scope.
  Notation "# c" := (@GSatisfy AsciiCharset _
    (fun c2 => if ascii_dec (c)%char c2 then true else false)) (at level 1) : grammar_scope.
  Notation "e1 ^ e2" := (GCat e1 e2) 
    (right associativity, at level 30) : grammar_scope.
  Notation "e @ f" := (GMap f e)
    (left associativity, at level 78) : grammar_scope.
  Notation "e1 '|||' e2" := (GAlt e1 e2)
    (right associativity, at level 79) : grammar_scope.
  Notation "% v" := (@GEpsilon _ _ _ v) (at level 1) : grammar_scope.

  Delimit Scope parser_scope with parser.
  
  Notation "e1 ^ e2" := (cat e1 e2) 
    (right associativity, at level 30) : parser_scope.
  Notation "e @ f" := (map f e)
    (left associativity, at level 78) : parser_scope.
  Notation "e1 '|||' e2" := (alt e1 e2)
    (right associativity, at level 79) : parser_scope.
  Notation "# c" := (satisfy AsciiCharset (fun c2 => if ascii_dec (c%char) c2 then true else false)) 
    (at level 1) : parser_scope.
  Notation "% v" := (epsilon _ v) : parser_scope.
  Notation "'gfix' e" := (Gfix e _) (at level 70).

  Ltac gtac := unfold unroll, gclass, grec ; simpl ; repeat (progress constructor).

End ParsecNotation.
