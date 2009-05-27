(* Copyright (c) 2009, Harvard University
 * All rights reserved.
 *
 * Authors: Greg Morrisett, Adam Chlipala
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - The names of contributors may not be used to endorse or promote products
 *   derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

(* Specification and implementation of Packrat parsers -- this shows off the
 * use of a hash-table as well as stream-based IO. *)
Require Import List. 
Require Import Omega.
Require Import Eqdep.
Require Import Parse.Stream.
Require Import Charset.
Import INSTREAM.
Set Implicit Arguments.

Module Packrat.
Section Packrat.

  Variable cs : Charset.

  (* Parsers are parameterized by a character set *)
  Definition char := char cs.
  Definition char_eq := char_eq cs.

  Variable base_ty : Set.
  Variable base_ty_denote : base_ty -> Set.

  Inductive ty : Set :=
  | Base : base_ty -> ty
  | Unit : ty
  | Char : ty
  | Prod : ty -> ty -> ty.

  Fixpoint tyDenote (t : ty) : Set :=
    match t with
      | Base bt => base_ty_denote bt
      | Unit => unit
      | Char => char
      | Prod t1 t2 => tyDenote t1 * tyDenote t2
    end%type.

  (* This section defines syntax and semantics of grammars *)
  Section GRAMMAR.
    (* we use DeBruijn indices to represented typed non-terminals within grammars *)
    Definition Ctxt := list ty.

    Fixpoint get (c:Ctxt) (n:nat) {struct n} : ty := 
      match n, c with
      | 0, T::rest => T
      | S m, T::rest => get rest m
      | _, _ => Unit
      end.
    
    Fixpoint Env(f:ty -> Type)(G:Ctxt) {struct G} : Type := 
      match G with
        | nil => unit
        | T::rest => ((f T) * (Env f rest))%type
      end.

    Fixpoint lookup(f:ty->Type)(default:f Unit)(G:Ctxt) {struct G} : 
      forall n:nat, Env f G -> f (get G n) := 
        match G return forall n, Env f G -> f (get G n) with
          | nil => fun n => match n return Env f nil -> f (get nil n) with
                              | 0 => fun _ => default
                              | _ => fun _ => default
                            end
        | T::rest => fun n => match n return Env f (T::rest) -> f (get (T::rest) n) with
                                | 0 => fun env => fst env
                                | S n => fun env => lookup f default rest n (snd env)
                              end
        end.

    Variable G : Ctxt.

    (* A typed grammar term, following the ideas behind parsing expression grammars *)


    Inductive term : ty -> Type := 
    | Epsilon : term Unit
    | Void : forall t, term t
    | Lit : char -> term Char
    | LitClass : CharClass cs -> term Char
    | Var : forall n, term (get G n)
    | Seq : forall t1 t2, term t1 -> term t2 -> term (Prod t1 t2)
    | Alt : forall t, term t -> term t -> term t
    | FollowBy : forall t, term t -> term t
    | NotFollowBy : forall t, term t -> term Unit
    | Map : forall t1 t2, (tyDenote t1 -> tyDenote t2) -> term t1 -> term t2.

    Variable env : Env term G.

    Definition look n := lookup term Epsilon G n env.

    (* indicates whether or not characters were consumed while parsing *)
    Inductive consumed_t : Set := Consume | NoConsume.

    (* a parse either fails or succeeds, indicating whether or not it consumed any
     * characters, the list of characters still to be parsed, and the semantic value. *)
    Inductive ans_t(t:Set) : Set := 
    | Fail : ans_t t
    | Succeed : consumed_t -> list char -> t -> ans_t t.
 
    (* A monad for dealing with the recursive computations in grammars *)
    Inductive M : Set -> Type := 
    | MReturn : forall (t:Set), t -> M t
    | MBind : forall (t1 t2:Set), M t1 -> (t1 -> M t2) -> M t2
    | MUnroll : forall t, term t -> list char -> M (ans_t (tyDenote t)).
    
    Notation "'Return' x" := (MReturn x) (at level 75) : gdenote_scope.
    Notation "x <- c1 ; c2" := (MBind c1 (fun x => c2)) 
      (right associativity, at level 84, c1 at next level) : gdenote_scope.
    Open Local Scope gdenote_scope.

    Definition join_consume (c1 c2:consumed_t) : consumed_t := 
      match c1, c2 with 
        | NoConsume, NoConsume => NoConsume 
        | _, _ => Consume
      end.

    (* We first reduce the term and string to an M object and then provide an
     * operational interpretation of M's below.  It would be better to cut down
     * grammars so they don't have any left-recursion in them, and then give them
     * a functional semantics (using an order that argues either the grammar term
     * gets smaller or we consume characters.)  I did this in another development,
     * but it was very ugly compared to this. *)
    Fixpoint denote(t:ty)(e:term t)(s:list char) {struct e} : M (ans_t (tyDenote t)) := 
      match e in term t return M (ans_t (tyDenote t)) with 
        | Epsilon => Return Succeed NoConsume s tt
        | Void _ => Return Fail _
        | Lit c => match s with 
                     | nil => Return Fail _
                     | c'::s' => if char_eq c c' then Return Succeed Consume s' c
                       else Return Fail _
                   end
        | LitClass c => match s with 
                          | nil => Return Fail _
                          | c'::s' => if In_CharClass_dec c c' 
                            then Return Succeed Consume s' c'
                            else Return Fail _
                        end
        | Seq t1 t2 e1 e2 => 
          a1 <- denote e1 s ; 
          match a1 with 
            | Fail => Return Fail _
            | Succeed c1 s1 v1 => 
              a2 <- denote e2 s1 ; 
              match a2 with 
                | Fail => Return Fail _
                | Succeed c2 s2 v2 => Return Succeed (join_consume c1 c2) s2 (v1,v2)
              end
          end
        | Alt t e1 e2 => 
          a1 <- denote e1 s ; 
          match a1 with 
            | Fail => denote e2 s
            | a1 => Return a1
          end
        | FollowBy t e =>
          a <- denote e s ; 
          match a with 
            | Fail => Return Fail _
            | Succeed _ _ v => Return Succeed NoConsume s v
          end
        | NotFollowBy t e =>
          a <- denote e s ; 
          match a with 
            | Fail => Return Succeed NoConsume s tt
            | Succeed _ _ _ => Return Fail _
          end
        | Map t1 t2 f e =>
          a <- denote e s ; 
          match a with 
            | Fail => Return Fail _
            | Succeed c s' v => Return Succeed c s' (f v)
          end
        (* note that here we return the expression e that we look up in the environment
         * as an MUnroll object.  We can't ask for its denotation here because it's not
         * a sub-term of (Var n). *)
        | Var n => MUnroll (look n) s
      end.

    (* Finally, give an operational semantics to the monad M -- the only 
     * interesting step is for MUnroll which simply calls evals and denote
     * again. *)
    Inductive evals: forall t:Set, M t -> t -> Prop := 
    | evals_MReturn : forall (t:Set) (v:t), evals (MReturn v) v
    | evals_MBind : forall (t1 t2:Set) (c1:M t1) (v1:t1) (c2:t1 -> M t2) (v2:t2), 
      evals c1 v1 -> evals (c2 v1) v2 -> evals (MBind c1 c2) v2
    | evals_MUnroll : forall (t:ty) (e:term t) (s:list char) (v:ans_t (tyDenote t)), 
      evals (denote e s) v -> evals (MUnroll e s) v.

  End GRAMMAR.

  (* the following definitions make it easy to construct a grammar by using 
   * a simple form of HOAS. *)

  (* when G = t1::t2::...::tn::nil, then grammar_t G expands into 
   *    term (term G) T1 -> term (term G) T2 -> ... -> term (term G) Tn -> 
   *       (term (term G) T1 * term (term G) T2 * ... * term (term G) Tn * unit) 
   *)
  Fixpoint grammar_t'(G1 G2:Ctxt) {struct G1} : Type := 
    match G1 with 
      | nil => Env (term G2) G2
      | T::Ts => term G2 T -> grammar_t' Ts G2
    end.

  Definition grammar_t G := grammar_t' G G.

  (* when e : grammar_t G, then gfix e can be used to build a suitable
   * recursive grammar. *)
  Lemma getN(G:Ctxt)(n:nat)T : nth_error G n = Some T -> get G n = T.
   induction G ; destruct n ; simpl ; unfold error, value in *; intros ; try congruence.
    apply IHG ; auto.
  Defined.

  Definition genvar T (G G1 G2:Ctxt) : G = G1 ++ T::G2 -> term G T.
    intros.
    assert (get G (length G1) = T). apply (getN G (length G1)). rewrite H.
    clear H G ; induction G1 ; auto.
    pose (Var G (length G1)). clearbody t. rewrite H0 in t. apply t.
  Defined.

  Program Fixpoint gfix'(G G1 G2:Ctxt) {struct G2} : 
    (G = G1 ++ G2) -> grammar_t' G2 G -> Env (term G) G := 
    match G2 return (G = G1 ++ G2) -> grammar_t' G2 G -> Env (term G) G with
      | nil => fun _ env => env
      | T::rest => fun H f => @gfix' G (G1 ++ T::nil) rest _ (f (@genvar T G G1 rest H))
    end.
  Next Obligation. rewrite app_ass ; auto. Defined.

  Definition gfix(G:Ctxt)(f:grammar_t G) : Env (term G) G := 
    @gfix' G nil G (refl_equal G) f.

  (************************************************************)
  (* In this section, we define the basic parsing combinators *)
  (************************************************************)
  Require Import Ynot.
  Require Import FiniteMap2.
  Open Local Scope hprop_scope.
  Open Local Scope stsepi_scope.
  Section Parsing.
    (* we work relative to a typing context and environment for the non-terminals *)
    Variable G : Ctxt.
    Variable env : Env (term G) G.

    Fixpoint nthtail(A:Type)(cs:list A)(n:nat) {struct n} : list A := 
      match n, cs with 
        | 0, cs => cs 
        | S n, c::cs => nthtail cs n
        | S n, nil => nil
      end.

    (* We're going to use the finite map to memoize the results of parsing
     * each non-terminal at a given input position. *)
    Record key_t : Set := mkKey { key_non_terminal : nat ; key_pos : nat }.

    Definition key_eq(k1 k2:key_t) : {k1 = k2} + {k1 <> k2}.
      intros [k1nt k1pos] [k2nt k2pos].
      refine(
      match eq_nat_dec k1nt k2nt with
        | left H1 => match eq_nat_dec k1pos k2pos with 
                       | left H2 => left _ _ 
                       | right H2 => right _ _
                           end
        | right H1 => right _ _
      end) ; congruence.
    Defined.

    (* This is derivable from Eqdep_dec, but requires declaring a module, which alas,
     * I can't do inside this section.  So screw it...
     *)
    Axiom key_eq_irr : forall (k:key_t)(p:k = k), p = refl_equal k.

    (* Parsers return an option(nat * t) where None denotes parse failure and 
     * Some(n,v) denotes success, consuming n characters and returning semantic value v. 
     * This predicate connects answers to the specification above. *)
    Definition parses(s:list char)(pos:nat)(t:ty)(e:term G t)(vopt:option (nat * tyDenote t)) :Prop := 
      evals env (denote env e (nthtail s pos)) 
      match vopt with 
        | None => Fail _
        | Some (len,v) => 
          Succeed (if eq_nat_dec 0 len then NoConsume else Consume) 
                  (nthtail s (len + pos))
                  v
      end.

    Definition value_t(k:key_t) := option (nat * tyDenote (get G (key_non_terminal k))).

(*
    (* Our finite-map is going to capture correctness in the result type -- minor hack
     * in that I need to get at the stream elements but this requires using hprop_unpack
     * which yields an hprop, so I just apply the hprop to the empty heap to get it back
     * as a Prop. *)      
    Record value_t(ins:instream_t char)(k:key_t) : Set := mkValue
      { value_ans : option (nat * get id G (key_non_terminal k)) ; 
        value_pf  : 
        (let elts := stream_elts ins in 
          elts ~~ 
          [parses elts (key_pos k) (lookup (term G) (Epsilon G) G (key_non_terminal k) env)
            value_ans]) empty
      }.
*)

    Definition FM_t(ins:instream_t char) := 
      FiniteMapInterface.finite_map_t key_eq value_t.
    Definition table_t(ins:instream_t char)(FM:FM_t ins) := 
      FiniteMapInterface.fmap_t FM.
    Definition fmrep(ins:instream_t char)(FM:FM_t ins)(t:table_t FM) := 
      FiniteMapInterface.rep FM t.

    Definition valid_value(elts:list char)(k:key_t)(v:value_t k) := 
        parses elts (key_pos k) (lookup (term G) (Epsilon G) G (key_non_terminal k) env) v.

    Fixpoint valid_al(elts:list char)(al:FiniteMapInterface.alist_t value_t) 
      {struct al} : Prop := 
      match al with 
        | FiniteMapInterface.Nil_al => True
        | FiniteMapInterface.Cons_al k v al => valid_value elts v /\ valid_al elts al
      end.

    Lemma valid_al_remove: forall elts k (al:FiniteMapInterface.alist_t value_t), 
      valid_al elts al -> 
      valid_al elts (@FiniteMapInterface.remove_al key_t key_eq value_t k al).
      induction al ; auto. simpl. intros. destruct (key_eq k k0). apply IHal. tauto.
      simpl. intuition.
    Qed.
                            
    Definition fminv(ins:instream_t char)(FM:FM_t ins)(t:table_t FM) := 
      Exists l :@ _, fmrep FM t l * (elts :~~ stream_elts ins in [valid_al elts l]).
    Definition flookup_al := @FiniteMapInterface.lookup_al key_t key_eq value_t.

    Definition rep_ans(ins:instream_t char)(n:nat)(t:Set)(a:option (nat * t)) : hprop := 
      match a with 
        | Some (m,_) => rep ins (n+m) 
        | None => Exists m :@ nat, rep ins m
      end.

    Definition ans_correct(ins:instream_t char)(n:nat)(T:ty)
                          (e:[term G T])(a:option (nat * tyDenote T)) := 
      elts :~~ stream_elts ins in e ~~ [parses elts n e a]. 

    (* A basic parser for grammer e takes an input stream [ins], a 
     * variable [n] representing the current offset in the input stream, a finite
     * map interface [FM] and object [t] that maps non-terminals and positions to 
     * appropriate results, and returns an option(nat*T) that is correct with
     * respect to the specification above.  We also ensure that if the parse is
     * sucessful, then the input stream is advanced by the appropriate number of
     * characters, and that the finite map [t] is still valid. *)
    Definition basic_parser_t(T:ty)(e:[term G T]) :=
      forall (ins:instream_t char)(n:nat)(FM:FM_t ins)(t:table_t FM), 
        STsep (rep ins n * fminv FM t) 
              (fun a:option (nat * tyDenote T) => 
                ans_correct ins n e a * rep_ans ins n a * fminv FM t).

    (* The following defines an environment for the non-terminals, mapping each
     * one to an appropriate basic parser *)
    Fixpoint penv_t(G1:Ctxt) {struct G1} : Env (term G) G1 -> Type := 
      match G1 return Env (term G) G1 -> Type with 
        | nil => fun env => unit
        | T::G1' => fun env => (basic_parser_t (inhabits (fst env)) * penv_t G1' (snd env))%type
      end.

    (* Finally, a parser for e is a basic parser built relative to an environment
     * that provides a basic parser for all of the non-terminals.  The environment
     * itself is under a computation because we need to build it using a fixed-point.
     *)
    Definition parser_t(T:ty)(e:[term G T]) := 
      forall (penv : STsep __ (fun penv : penv_t G env => __)), basic_parser_t e.

    Lemma EmpImpInj(P:Prop) : P -> __ ==> [P].
    intros. sep fail auto. Qed.

    Ltac mysep := 
      try autorewrite with PackRat; 
      match goal with
        | [ |- (__ ==> [ _ ])%hprop ] => apply EmpImpInj
        | [ |- evals _ (MReturn _ ?r) ?r ] => econstructor
        | [ |- evals _ (MBind _ _) _] => econstructor ; eauto ; simpl
        | [ |- context[if (?f ?c) then _ else _] ] => 
          let H := fresh "H" in
            assert (H: f c = true \/ f c = false) ; [ destruct (f c) ; tauto | 
              destruct H ; [ rewrite H ; simpl | rewrite H ; simpl ]]
        | _ => auto
      end.

    Definition valid_al_val ins al k (vopt:option(value_t k)) := 
      elts :~~ stream_elts ins in [valid_al elts al] * [vopt = flookup_al k al].

    Lemma rep_ex : forall elt (ins : instream_t elt) n,
      rep ins n ==> (Exists m :@ nat, rep ins m).
      sep fail idtac.
    Qed.
    
    Ltac destruct_pairs := 
      repeat match goal with
               | [ x : (_ * _)%type |- _ ] => goal_meta_fail ; destruct x
             end.

    Ltac pre :=
      simpl_IfNull; destruct_pairs ;
      canceler;
      try simpl_cancel ltac:(idtac;
        match goal with
          | [ |- rep _ _ ==> Exists m :@ nat, rep _ m ] => 
            apply rep_ex
        end).

    Ltac unfp := unfold parser_t, basic_parser_t.
    Ltac unf := unfold ans_correct, rep_ans, parses; unfold_local.
    Ltac unf' := unfold fminv, fmrep, valid_al_val.
    Ltac t := unf ; sep fail mysep.
    Ltac t' := cbv zeta; simpl_IfNull; destruct_pairs;
      canceler; unf; sep pre mysep.

    (* the empty parser *)
    Definition epsilon : parser_t [Epsilon G].
      unfp ;
      refine (
        fun penv ins n FM t => 
        {{Return (Some (0,tt)) <@> (rep ins n * fminv FM t)}}
      );t. rewrite plus_comm ; t.
    Defined.

    (* the always failing parser *)
    Definition void(T:ty) : parser_t [Void G T].
      unfp ; 
      refine (
        fun T penv ins n FM t => 
          {{ Return None <@> (rep ins n * fminv FM t) }}
      ) ; t.
    Defined.

    (* Some lemmas on lists of characters to simplify proof below *)
    Lemma NthError(x:list char)(n:nat) : 
      (nth_error x n = None \/ exists c, nth_error x n = Some c).
    Proof.  intros. destruct (nth_error x n). right. eauto. left. eauto. Qed.

    Lemma NthErrorNoneNthTail(A:Type)(i:nat)(vs:list A) : 
      nth_error vs i = None -> nthtail vs i = nil.
    Proof.
      induction i ; destruct vs ; auto ; simpl ; intros ; 
      try (unfold value in * ; congruence) ; auto.
    Qed.

    Lemma NthErrorSomeNthTail(A:Type)(i:nat)(vs:list A)(v:A) : 
      nth_error vs i = Some v -> 
      exists vs1, exists vs2, vs = vs1 ++ v::vs2 /\ nthtail vs i = v::vs2.
    Proof.
      induction i ; destruct vs ; auto ; simpl ; unfold Specif.error, value in * ; 
      try congruence ; intros.
      match goal with [ H : Some _ = Some _ |- _ ] => 
        inversion H ; subst ; exists (@nil A) ; simpl ; eauto
      end.
      pose (IHi _ _ H) ; destruct e as [vs1 [vs2 [H1 H2]]] ; exists (a::vs1) ; exists vs2 ; 
        split ; subst ; auto.
    Qed.
    
    Implicit Arguments NthErrorSomeNthTail [A i vs v].

    Lemma NthTailSucc(A:Type)(i:nat)(vs vs2:list A)(v:A) : 
      nthtail vs i = v::vs2 -> nthtail vs (S i) = vs2.
    Proof.
      induction i ; simpl ; intros ; subst ; auto ; destruct vs ; try congruence. 
      apply (IHi _ _ _ H). 
    Qed.

    Hint Rewrite NthErrorNoneNthTail using solve [auto] : PackRat.

    Lemma rep_S : forall elt (ins : instream_t elt) n,
      rep ins (S n) ==> rep ins (n + 1).
      intros; rewrite plus_comm; t.
    Qed.

    Hint Resolve rep_S.

    Lemma NthTailPop : forall c' v2 n ls,
      nthtail ls n = c' :: v2
      -> match ls with
           | nil => nil (A:=char)
           | _ :: cs => nthtail cs n
         end = v2.
      induction n; destruct ls; simpl; intuition; congruence.
    Qed.

    Implicit Arguments NthTailPop [c' v2 n ls].

    Ltac exrewrite E :=
      let H := fresh "H" in
        generalize E; intro H;
          repeat (let T := type of H in
            match T with
              | _ = _ => progress rewrite H
              | _ /\ _ => let H' := fresh "H'" in
                destruct H as [H' H]
              | ex _ => let x := fresh "x" in
                destruct H as [x H]
            end).

    (* parser for a literal character c *)
    Definition lit(c:char) : parser_t ([Lit G c]).
      unfp; refine (fun c penv ins n FM t => 
        copt <- next ins [n]%inhabited <@> _; 
        IfNull copt As c' Then
          {{Return None}}
        Else
          if char_eq c c' then
            {{Return (Some (1, c))}}
          else
            {{Return None}}
      ); t';
      repeat match goal with
               | [ |- context[if ?E then _ else _] ] => destruct E
               | [ H : Some _ = nth_error ?x ?x0 |- context[nthtail ?x ?x0] ] =>
                 exrewrite (NthErrorSomeNthTail (sym_eq H))
               | [ H : nthtail _ _ = _ :: _ |- _ ] => rewrite (NthTailPop H)
             end; t'. 
    Defined.

    (* parser for a literal character c *)
    Definition litclass(cl: CharClass cs) : parser_t ([LitClass G cl]).
      unfold parser_t, basic_parser_t ; intros.
      refine (copt <- next ins [n]%inhabited <@> _; 
        IfNull copt As c' Then
          {{ Return None }}
        Else
          if In_CharClass_dec cl c' then
            {{ Return (Some (1,c')) }}
          else
            {{ Return None }}); t';
      repeat match goal with
               | [ |- context[if ?E then _ else _] ] => destruct E
               | [ H : Some _ = nth_error ?x ?x0 |- context[nthtail ?x ?x0] ] =>
                 exrewrite (NthErrorSomeNthTail (sym_eq H))
               | [ H : nthtail _ _ = _ :: _ |- _ ] => rewrite (NthTailPop H)
             end; t'.
    Defined.

    (* a more efficient parser for sets of characters *)
    Fixpoint charset(cs:list char) : term G Char := 
      match cs with 
        | nil => Void G Char
        | c::cs => Alt (Lit G c) (charset cs)
      end.

    Fixpoint member(c:char)(cs:list char) : Prop := 
      match cs with 
        | nil => False
        | c'::cs => (c = c') \/ member c cs
      end.

    (* Useful for defining things like digit = 0 | 1 | ... | 9.  Here, [cs] is a set
     * of characters, f is a test that determines whether a character is in [cs], and
     * the resulting parser is equivalent to running the alternation of the literals
     * in the list. *)
    Definition satisfy(cs:list char)
                      (f:forall c, {member c cs} + {~member c cs}) : parser_t [charset cs].
      unfp ;
      refine ( 
        fun cs f penv ins n FM t => 
          copt <- next ins (inhabits n) <@> _ ;
          {{Return (match copt with 
                      | None => None
                      | Some c => if f c then Some (1,c) else None
                    end)}}
      ) ; t. destruct (NthError x x0).
      rewrite H0 ; rewrite (NthErrorNoneNthTail _ _ H0) ; t. clear f.
      induction cs0 ; t. econstructor. apply IHcs0. destruct H0 ; rewrite H0 ; 
      destruct (NthErrorSomeNthTail H0) as [v1 [v2 [H3 H4]]].
      rewrite H4. destruct (f x1). rewrite (plus_comm x0 1). t.
      pose (NthTailSucc _ _ H4). simpl in *. rewrite e. clear f.
      induction cs0. simpl in *. contradiction m. simpl. destruct (char_eq a x1).
      econstructor. econstructor. simpl. rewrite e0. constructor.
      destruct m. congruence. econstructor. econstructor. simpl. apply IHcs0. auto.
      t. clear f. induction cs0. simpl ; constructor. simpl in *.
      destruct (char_eq a x1). assert False. apply f0. left. symmetry. auto. contradiction.
      t. econstructor. simpl. auto.
    Defined.

    Definition inhabit_unpacks T1 T2 U (x:[T1]) (y:[T2]) (f:T1 -> T2 -> U) : [U] := 
      match x with
        | inhabits xv => match y with
                           | inhabits yv => inhabits (f xv yv)
                         end
      end.

    Notation "<< x , y >> ~~~ f" := (inhabit_unpacks x y (fun x y => f)) 
      (at level 91, right associativity).

    (* parser for p1 or p2 *)
    Definition alt T (e1 e2:[term G T]) (p1:parser_t e1) (p2:parser_t e2) : 
      parser_t(<<e1,e2>> ~~~ Alt e1 e2).
      unfp ; 
      refine (fun T e1 e2 p1 p2 penv ins n FM t => 
        ans1 <- p1 penv ins n FM t ; 
        IfNull ans1 As ans1' Then
          seek ins n <@> _ ;;
          {{ p2 penv ins n FM t <@> _ }}
        Else
          {{ Return ans1 }}
      ). t'. t'. t'. t'. t'. t'. t. t.
    Defined.

   (* parser for p1 concatenated with p2 *)
   Definition seq t1 t2 (e1:[term G t1]) (e2:[term G t2]) (p1:parser_t e1) (p2:parser_t e2) : 
     parser_t(<<e1,e2>> ~~~ Seq e1 e2).
     unfp ; 
     refine (
       fun t1 t2 e1 e2 p1 p2 penv ins n FM t => 
             vopt1 <- p1 penv ins n FM t ; 
             match vopt1 return 
               STsep (ans_correct ins n e1 vopt1 * rep_ans ins n vopt1 * fminv FM t)
                     (fun vopt => ans_correct ins n (<<e1,e2>> ~~~ Seq e1 e2) vopt * 
                                  rep_ans ins n vopt * fminv FM t) 
             with 
               | None => {{Return None}}
               | Some (m1,v1) => 
                 vopt2 <- p2 penv ins (m1 + n) FM t <@> 
                 ans_correct ins n e1 (Some (m1,v1)); 
                 match vopt2 return
                   STsep (ans_correct ins n e1 (Some(m1,v1)) * 
                          ans_correct ins (m1 + n) e2 vopt2 *
                          rep_ans ins (m1 + n) vopt2 * fminv FM t)
                         (fun vopt => ans_correct ins n (<<e1,e2>> ~~~ Seq e1 e2) vopt * 
                                      rep_ans ins n vopt * fminv FM t) 
                   with 
                   | None => {{Return None}}
                   | Some (m2,v2) => {{Return (Some (m2 + m1, (v1,v2)))}}
                 end
             end) ; t. 
     rewrite plus_comm ; t. 
     assert (m1 + n + m2 = n + (m2 + m1)) ; [omega | rewrite <- H2] ; t. 
     destruct m1 ; destruct m2 ; t ; rewrite <- plus_assoc ; simpl ; constructor.
   Defined.

   (* the followby parser -- doesn't consume input *)
   Definition followby(T:ty)(e:[term G T])(p:parser_t e) : parser_t (e ~~~ FollowBy e).
     unfp ; 
     refine (
       fun T e p penv ins n FM t => 
             vopt <- p penv ins n FM t  ; 
             match vopt return 
               STsep (ans_correct ins n e vopt * rep_ans ins n vopt * fminv FM t)
                     (fun a => ans_correct ins n (e ~~~ FollowBy e) a * 
                               rep_ans ins n a * fminv FM t)
               with 
               | None => {{ Return None }}
               | Some (m,v) => 
                 seek ins n <@> (ans_correct ins n e (Some(m,v)) * fminv FM t) ;; 
                 {{ Return Some(0,v) }}
             end) ; 
     t ; rewrite plus_comm ; t.
   Defined.

   (* the notfollowby parser -- doesn't consume input *)
   Definition notfollowby(T:ty)(e:[term G T])(p:parser_t e) : parser_t (e ~~~ NotFollowBy e).
     unfp ; 
     refine (
       fun T e p penv ins n FM t => 
             vopt <- p penv ins n FM t ; 
             match vopt return
               STsep (ans_correct ins n e vopt * rep_ans ins n vopt * fminv FM t)
                     (fun a => ans_correct ins n (e ~~~ NotFollowBy e) a * 
                               rep_ans ins n a * fminv FM t)
               with 
               | None => 
                 seek ins n <@> (ans_correct ins n e None * fminv FM t) ;;   
                 {{ Return Some(0,tt) }}
               | Some _ => 
                 {{ Return None }}
             end) ; 
     t ; rewrite plus_comm ; t.
   Defined.

   Definition map(t1 t2:ty)(f:tyDenote t1->tyDenote t2)(e:[term G t1])(p:parser_t e) : parser_t(e ~~~ Map _ f e).
     unfp ; 
     refine (
       fun t1 t2 f e p penv ins n FM t => 
             vopt <- p penv ins n FM t ; 
             {{ Return match vopt with 
                      | None => None
                      | Some (m,v) => Some (m, f v)
                    end }} ) ; 
     t ; destruct vopt ; try destruct p ; t.
   Defined.

   (* lookup the basic parser associated with a variable in the environment *)                 
   Fixpoint get_bp(penv_delay:STsep __ (fun _:penv_t G env => __))(n:nat) G1 {struct n} : 
      forall (env : Env (term G) G1), penv_t G1 env -> 
        basic_parser_t [lookup (term G) (Epsilon G) G1 n env] := 
        match n return forall (env : Env (term G) G1), penv_t G1 env -> 
                          basic_parser_t [lookup (term G) (Epsilon G) G1 n env]
        with 
          | 0 => match G1 return 
                   forall (env : Env (term G) G1), penv_t G1 env -> 
                     basic_parser_t [lookup (term G) (Epsilon G) G1 0 env]
                   with 
                   | nil => fun _ _ => epsilon penv_delay
                   | T::_ => fun env pair => fst pair
                 end
          | S n => match G1 return
                   forall (env : Env (term G) G1), penv_t G1 env -> 
                     basic_parser_t [lookup (term G) (Epsilon G) G1 (S n) env]
                     with 
                     | nil => fun _ _ => epsilon penv_delay
                     | _::G1' => fun env pair => get_bp penv_delay n G1' (snd env) (snd pair)
                   end
        end.

    (* the (uncached) parser for non-terminals *)
    Definition var(x:nat) : parser_t [look G env x].
      unfp ; 
      refine (
        fun x penv ins n FM t => 
              penv0 <- penv <@> _ ; 
              (get_bp penv x G env penv0) ins n FM t) ; 
      t.
    Defined.

    Lemma lookup_valid : 
      forall elts k al, valid_al elts al -> 
        forall v, Some v = flookup_al k al
          -> evals env
          (denote env (lookup (term G) (Epsilon G) G (key_non_terminal k) env)
            (nthtail elts (key_pos k)))
          match v with
            | Some (pair len v0) =>
              Succeed (if eq_nat_dec 0 len then NoConsume else Consume)
              (nthtail elts (len + key_pos k)) v0
            | None => Fail _
          end.
      induction al ; simpl ; intros. congruence. destruct (key_eq k0 k). inversion H0.
      unfold FiniteMapInterface.coerce_al. unfold eq_rec. unfold eq_rect. 
      destruct H. generalize e v H. clear H2 H0 v0 H1 H IHal al v. rewrite e.
      intros. rewrite (key_eq_irr e0). auto. apply IHal ; tauto.
    Qed.

    Implicit Arguments lookup_valid [elts k al v].

    Hint Resolve valid_al_remove.

    Lemma rep_plus_comm : forall elt (ins : instream_t elt) m n,
      rep ins (m + n) ==> rep ins (n + m).
      intros; rewrite plus_comm; t.
    Qed.

    Hint Immediate rep_plus_comm.

    (* a memoizing version of a non-terminal -- we first lookup the non-terminal 
     * and position in the finite map [t], and if we get a hit, return (after 
     * advancing the input stream an appropriate amount.)  If we don't get a hit,
     * then we lookup the basic parser associated with [x] in the environment, 
     * run it, and then insert the result into [t] before returning. 
     *)    
    Definition memovar'(x:nat) : parser_t [look G env x].
      unfp; refine (fun x penv ins n FM t =>
        let invariant := (fun al => elts :~~ stream_elts ins in [valid_al elts al]) in
        (* lookup this non-terminal and position in the finite map t *)
        vopt <- FiniteMapInterface.lookup FM t (mkKey x n) invariant <@> _;
        IfNull vopt As v Then
          (* nothing in the memo table -- run the parser associated with the non-
           * terminal to get out a result. *)
          ans <- var x penv n FM t ; 
          (* cache the answer for later lookups *)
          FiniteMapInterface.insert FM t (mkKey x n) ans invariant <@> _;;
          (* finally, return the computed answer *)
          {{ Return ans }}
        Else
          (* here we have a cached answer v and the fminv should imply that it is correct *)
          IfNull v Then
            {{ Return None }}
          Else
            (* in the case that we have a cached answer, we need to seek
             * to position (n + m) to maintain the invariant that a successful
             * parse leaves us just after the consumed part of the input *)
            seek ins (fst v + n) <@> _ ;; 
            (* then we can just return the cached result *)
            {{ Return (Some v) }}
      ); unf'; t';
      try match goal with
        | [ H : valid_al _ _, H' : Some _ = FiniteMapInterface.lookup_al _ _ _ |- _ ] =>
          generalize (lookup_valid H H')
      end; t'. 
    Defined.

    Hint Constructors evals.

    (* same as above, but instead of parser_t(look G env x) we get parser_t(Var G x) *)
    Definition memovar(x:nat) : parser_t [Var G x].
      unfp ; 
      refine (fun x penv ins n FM t => {{ @memovar' x penv ins n FM t }}) ; t; eauto.
    Defined.

  End Parsing.

  (* Now that we have combinators for all of the grammar terms, we can map a grammar
   * to an imperative parser, given a suitable parser environment. *)
  Fixpoint exp2parser(G:Ctxt)(t:ty)(e:term G t)(env : Env (term G) G) {struct e} :
    parser_t env [e] := 
    match e return parser_t env [e] with 
      | Epsilon => @epsilon G env
      | Void t => void env t
      | Lit c => @lit G env c
      | LitClass cl => @litclass G env cl
      | Alt t e1 e2 => @alt G env t [e1] [e2] (@exp2parser G t e1 env) (@exp2parser G t e2 env)
      | Seq t1 t2 e1 e2 => 
        @seq G env t1 t2 [e1] [e2] (@exp2parser G t1 e1 env) (@exp2parser G t2 e2 env)
      | FollowBy t e => @followby G env t [e] (@exp2parser G t e env)
      | NotFollowBy t e => @notfollowby G env t [e] (@exp2parser G t e env)
      | Map t1 t2 f e => @map G env t1 t2 f [e] (@exp2parser G t1 e env)
      | Var x => @memovar G env x
    end.

  (* Same as a penv_t (h-list of basic parsers) except that it's an h-list of 
   * parsers, which are basic parsers that abstract over a penv_t env. *)
  Fixpoint genv_t(G:Ctxt)(env: Env (term G) G)(G1:Ctxt) {struct G1} : Env (term G) G1 -> Type 
    := 
    match G1 as G2 return Env (term G) G2 -> Type with 
      | nil => fun _ => unit
      | T::G1' => 
        fun env0 : Env (term G) (T::G1') => 
          (parser_t env [fst env0] * genv_t G env G1' (snd env0))%type
    end.

  (* Given a mapping from non-terminals to grammar terms [env], we can now produce
   * an environment mapping non-terminals to parser_t's. *)
  Fixpoint mkgenv(G:Ctxt)(env : Env (term G) G)(G1:Ctxt) { struct G1 } : 
    forall (env1 : Env (term G) G1), genv_t G env G1 env1 := 
      match G1 return forall (env1 : Env (term G) G1), genv_t G env G1 env1 with
        | nil => fun env1 => tt
        | T::G1 => fun env1 => (@exp2parser G T (fst env1) env, 
                                @mkgenv G env G1 (snd env1))
      end.

  (* This function is used to map the genv_t (an environment of parsers that abstract
   * over an envirnoment of basic parsers) to a penv_t (an environment of basic parsers).
   * We really don't need to separate this from mkgenv. *)
  Definition mkpenv'(G:Ctxt)(env : Env (term G) G)
                    (self: forall (genv : genv_t G env G env), 
                             STsep __ (fun a : penv_t G env G env => __))
                    (genv : genv_t G env G env) : STsep __ (fun a : penv_t G env G env => __).
    intros.
    refine {{ Return 
      ((fix instenv(G1:Ctxt) : forall (env1: Env (term G) G1), genv_t G env G1 env1 -> 
                                 penv_t G env G1 env1 := 
          match G1 return forall (env1: Env (term G) G1), genv_t G env G1 env1 -> 
                            penv_t G env G1 env1 with 
            | nil => fun env1 genv1 => tt
            | T::G1' => fun env1 genv1 => 
                ((fst genv1) (self genv), instenv G1' (snd env1) (snd genv1))
          end) G env genv) }} ; sep fail auto.
  Defined.

  (* Finally, tie the knot in the environment by using the Ynot Fix *)
  Definition mkpenv(G:Ctxt)(env:Env (term G) G) : 
    STsep __ (fun a : penv_t G env G env => __) := 
    (SepFix _ _ (@mkpenv' G env) (mkgenv G env G env)).

  (* Build association list and hash-table interfaces for our key-value pairs *)
  Definition newAssocList(G:Ctxt)(env:Env (term G) G)(ins:instream_t char) : FM_t G ins := 
    @RefAssocList.ref_assoc_list key_t key_eq (value_t G). 

  Definition newHashTable(G:Ctxt)(env:Env (term G) G)(ins:instream_t char) : FM_t G ins.
    intros.
    refine (@HashTable.hash_table _ key_eq
              (fun k => 2*(key_non_terminal k) + 3*(key_pos k)) _ 
              101 _ (newAssocList G env ins)). auto with arith.
  Defined.

  (* Build a parser given a grammar [env] and term [e] for instream [ins].  We
   * construct parsers for all of the non-terminals using mkpenv, construct a
   * parser [p] for [e], build the hash-table used for memoizing things, run 
   * [p] to get the answer [ans], free the hash-table, and return [ans]. *)
  Definition mkparser(G:Ctxt)(env:Env (term G) G)(t:ty)(e:term G t)(ins:instream_t char) n : 
    STsep (rep ins n)
          (fun a:option (nat * tyDenote t) => ans_correct env ins n [e] a * rep_ans ins n a).
    intros.
    Ltac t := (idtac ; 
               match goal with 
                 [ |- _ ==> (Exists v :@ FiniteMapInterface.alist_t _, _) * _ ] => 
                 eapply himp_ex_conc ; exists (@FiniteMapInterface.Nil_al key_t (value_t _))
               | _ => auto
             end).
    refine (let penv := mkpenv G env in 
            let p := @exp2parser G t e env in 
            let FM := newHashTable G env ins in
            table <- FiniteMapInterface.new FM <@> _ ; 
            ans <- p penv ins n FM table ; 
            FiniteMapInterface.free FM table <@> _ ;; 
            {{ Return ans }}
           ); unfold fminv, fmrep;
    (cbv zeta;
      solve [ sep fail ltac:t
        | simpl; match goal with
                   | [ |- ?P1 * ?P2 * _ ==> ?Q * _ ] => equate (P1 * P2) Q
                 end; sep fail ltac:t ]).
  Defined.

End Packrat.
End Packrat.

