Require Import Ynot.
Require Import RSep.
Require Import Specif.

Require Import IO Net FS.
Require Import List Ascii String.
Require Import UdpServer TcpServer.
Require Import Stream Parsec Charset.

Import STRING_INSTREAM.
Import INSTREAM.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Set Implicit Arguments.

Opaque ReadString.
Opaque ReadLine.
Opaque WroteString.

(* An applications that our server can run. *)
Module Type App.
  Parameter Q: Set. (** Type of parsed queries **)
 
  Parameter T  : Set.              (** Type of Execution context **)
  Parameter RR : Set.              (** Type of the return value **)
  Parameter M  : Set.              (** Modeling type for the context **)

  Parameter rep : T -> M -> hprop. (** Context representation **)
  Parameter I : M -> Prop.         (** Context Invariant **)

  Parameter func : Q -> M -> (RR * M). (** The function we implement **)
  Parameter AppIO : Q -> M -> RR -> M -> Trace.

  Parameter exec : forall (t : T) (q : Q) (m : [M]) (tr : [Trace]),
    STsep (tr ~~ m ~~ rep t m * traced tr * [I m]) 
          (fun r : RR => tr ~~ m ~~ 
           let m' := snd (func q m)
           in  [r = fst (func q m)] * rep t m' * [I m'] * 
               traced (AppIO q m r m' ++ tr)).
 
  Parameter init :
    STsep (__)
          (fun tm : T * [M] => hprop_unpack (snd tm) (fun m => rep (fst tm) m * [I m])).

  Parameter cleanup : forall (t : T) (m : [M]),
    STsep (m ~~ rep t m * [I m])
          (fun _:unit => __).

  Parameter func_preserves_I : forall q m, I m -> I (snd (func q m)).
End App.

Module Type AppInterface.
  Declare Module A : App.

  Parameter grammar : Term AsciiCharset A.Q.
  Parameter parser  : parser_t grammar.
  
  Parameter printer : A.RR -> list ascii.
  Parameter err : consumed_t -> list ascii.
End AppInterface.

Module AppServer (A: App) (AI : AppInterface with Module A := A) : TcpServer.STATE_EXECPARAMS.

  Ltac solver := auto.

  Definition context := A.T.
  Definition cmodel := A.M.
  Definition rep := A.rep.
  Definition inv := A.I.

  Definition mutate a (b : cmodel) := snd (A.func a b).
  Definition reply  a (b : cmodel) := fst (A.func a b).
  
  Inductive ccorrect' (local remote : SockAddr) (fd : File (BoundSocketModel local remote) (R :: W :: nil))
    : cmodel -> cmodel -> Trace -> Prop :=
  | DoneCorrect : forall past m m', ecorrect fd m m' past -> ccorrect' fd m m' (Flush fd :: ReadLine fd nil ++ past)
  with ecorrect (local remote : SockAddr) (fd : File (BoundSocketModel local remote) (R :: W :: nil))
    : cmodel -> cmodel -> Trace -> Prop :=
  | NilCorrect : forall m, ecorrect fd m m nil
  | Cons_parse_err : forall s e past (m m' : cmodel),
       s <> nil -> ecorrect fd m m' past -> parses AI.grammar s (Error _ _ e) ->
       ecorrect fd m m' (Flush fd :: WroteString fd (AI.err e) ++ ReadLine fd s ++ past) 

  | Cons_parse_ok  : forall s p1 p3 past (q: A.Q) (m m' m'' : cmodel) (r: A.RR),
       s <> nil -> ecorrect fd m m' past -> parses AI.grammar s (Okay _ p1 q p3) -> m'' = mutate q m' ->
       ecorrect fd m m'' (Flush fd :: WroteString fd (AI.printer (reply q m')) ++ A.AppIO q m' r m'' ++ ReadLine fd s ++ past).
  Hint Constructors ecorrect ccorrect'.

  Definition ccorrect := ccorrect'.

  Definition traceCombine (t1 t2 : [Trace]) := inhabit_unpack2 t1 t2 (fun t1 t2 => t1 ++ t2).
  Definition traceAfter (t1 t2 : [Trace]) (f : Trace -> Trace) := inhabit_unpack2 t1 t2 (fun t1 t2 => f (t1 ++ t2)).

  Definition empty_eq : forall T (a : list T), {a = nil} + {a <> nil}.
    intros; destruct a; firstorder.
  Qed.

  Ltac rcombine := idtac;
    match goal with
      | [ H : traceCombine ?X ?Y = [_]%inhabited |- _ ] =>
        rwpack X H; rwpack Y H; simpl in H; rewrite <- (pack_injective H) in *; clear H
      | [ H : traceAfter ?X ?Y _ = [_]%inhabited |- _ ] =>
        rwpack X H; rwpack Y H; simpl in H; rewrite <- (pack_injective H) in *; clear H
      | [ H : (inhabit_unpack ?X _) = [_]%inhabited |- _ ] =>
        rwpack X H; simpl in H; rewrite <- (pack_injective H)
    end.

  Ltac s := solve [ try unfold traceAfter; rsep fail auto; repeat rcombine; rsep fail auto ].

  Ltac dpack x := 
    let e := fresh "e" in pose (e := pack_type_inv x); destruct e.

  Lemma rw_model : A.M = cmodel.
    unfold cmodel; reflexivity.
  Qed.

  Definition io : forall (local remote : SockAddr)
    (fd : File (BoundSocketModel local remote) (R :: W :: nil)) (tr : [Trace])
    (ctx : context) (m0 : [cmodel]),
    STsep (tr ~~ m0 ~~ traced tr * handle fd * rep ctx m0 * [inv m0])
          (fun res':([Trace] * [cmodel]) => m0 ~~ tr ~~ 
            hprop_unpack (fst res') (fun tr' => 
              hprop_unpack (snd res') (fun m' =>
                traced (tr' ++ tr) * [ccorrect fd m0 m' tr'] * rep ctx m' * [inv m']))).
    intros. refine (
      {{Fix3 (fun (ctx:context) (m:[cmodel]) tr' => tr ~~ tr' ~~ m ~~ m0 ~~ 
                traced (tr' ++ tr) * handle fd * rep ctx m * [ecorrect fd m0 m tr'] * [inv m])
           (fun (ctx:context) (m:[cmodel]) _ (res:([Trace] * [cmodel])) => tr ~~ m ~~ m0 ~~ 
                hprop_unpack (fst res) (fun tr' => 
                  hprop_unpack (snd res) (fun m' => 
                    traced (tr' ++ tr) * [ccorrect fd m0 m' tr'] * rep ctx m' * [inv m'])))
           (fun self ctx m tr' =>
             str <- readline fd rw_readable (traceCombine tr' tr) <@> (tr' ~~ m0 ~~ m ~~ [ecorrect fd m0 m tr'] * [inv m] * rep ctx m) ;
             if empty_eq str then
               flush fd (traceAfter tr' tr (fun t => ReadLine fd str ++ t)) rw_writeable <@> _ ;;
               FS.close fd <@> (tr ~~ tr' ~~ m ~~ m0 ~~ [inv m] * rep ctx m * [ecorrect fd m0 m tr'] * traced (Flush fd :: ReadLine fd str ++ tr' ++ tr));;
               {{Return (tr' ~~~ Flush fd :: ReadLine fd str ++ tr', m)}}
             else
               is  <- instream_of_list_ascii str <@> _ ;
               let _:instream_t (char AsciiCharset) := is in
               ans <- AI.parser is (inhabits 0) <@> _ ;
               close is <@> (tr ~~ tr' ~~ m0 ~~ m ~~ rep ctx m * [inv m] * handle fd * [ecorrect fd m0 m tr'] * 
                 traced (ReadLine fd str ++ tr' ++ tr) * (hprop_unpack (stream_elts is) (fun is => [is = str])) * 
                 match ans with 
                   | ERROR c _ => @error AsciiCharset _ [0] is AI.grammar c
                   | OKAY c n q => @okay AsciiCharset _ [0] is AI.grammar c n q
                 end) ;;
               match ans as ans 
                 return STsep (tr ~~ tr' ~~ m0 ~~ m ~~ rep ctx m * [inv m] * traced (ReadLine fd str ++ tr' ++ tr) * 
                                   (hprop_unpack (stream_elts is) (fun is => [is = str])) * [ecorrect fd m0 m tr'] * handle fd *
                                   match ans with 
                                     | ERROR c _ => @error AsciiCharset _ [0] is AI.grammar c
                                     | OKAY c n q => @okay AsciiCharset _ [0] is AI.grammar c n q
                                   end)
                              (fun res:([Trace] * [cmodel]) => tr ~~ m ~~ m0 ~~ 
                                hprop_unpack (fst res) (fun tr' => 
                                  hprop_unpack (snd res) (fun m' => 
                                    traced (tr' ++ tr) * [ccorrect fd m0 m' tr'] * rep ctx m' * [inv m'])))
                 with
                 | ERROR e' _ =>
                   let reply' := AI.err e' in
                   (writeline fd reply' rw_writeable (traceAfter tr' tr (fun t => ReadLine fd str ++ t));;
                    flush fd (traceAfter tr' tr (fun t => WroteString fd reply' ++ ReadLine fd str ++ t)) rw_writeable) <@>  _;;
                   {{self ctx m (tr' ~~~ Flush fd :: WroteString fd reply' ++ ReadLine fd str ++ tr')}}
                 
                 | OKAY c n q =>
                   res <- A.exec ctx q m (traceAfter tr' tr (fun x => ReadLine fd str ++ x)) <@> 
                       (m ~~ m0 ~~ tr' ~~ tr ~~ [inv m] * @okay AsciiCharset _ [0] is AI.grammar c n q * handle fd * [ecorrect fd m0 m tr'] * (hprop_unpack (stream_elts is) (fun is => [is = str]))) ;
                   let reply' := AI.printer res in
                   (writeline fd reply' rw_writeable (inhabit_unpack3 tr' tr m (fun tr' tr m => A.AppIO q m res (mutate q m) ++ ReadLine fd str ++ tr' ++ tr)) ;;
                       flush fd (inhabit_unpack3 tr' tr m (fun tr' tr m => WroteString fd reply' ++ A.AppIO q m res (mutate q m) ++ ReadLine fd str ++ tr' ++ tr)) rw_writeable) <@> 
                   (m0 ~~ m ~~ tr ~~ tr' ~~ A.rep ctx (mutate q m) * [res = reply q m] * (*[m' = mutate q m] *)
                     [inv (mutate q m)] * (hprop_unpack (stream_elts is) (fun is => [is = str])) * [ecorrect fd m0 m tr'] *
                     @okay AsciiCharset _ [0] is AI.grammar c n q * [inv m]);;
                   {{self ctx (m ~~~ mutate q m) (inhabit_unpack2 tr' m (fun tr' m =>  Flush fd :: WroteString fd reply' ++ A.AppIO q m res (mutate q m) ++ ReadLine fd str ++ tr')) <@> 
                       (tr' ~~ m ~~ m0 ~~ [res = reply q m] * [inv (mutate q m)] * [inv m] *
                           (hprop_unpack (stream_elts is) (fun is => [is = str])) * [ecorrect fd m0 m tr'] * [parses AI.grammar (nthtail str 0) (Okay AsciiCharset c q (nthtail str (n + 0)))])}}
                 
             end)
         ctx m0 [nil]%inhabited}}
    ); try clear self; try unfold char in *.
    s.
    s.
    s.
    s.
    s.
    s.
    s.
    Ltac simplr := 
      unfold Parsec.char; simpl char; subst; simpl in *.
    rsep simplr ltac:((try norm_list); auto). rsep fail auto. cut_pure; constructor; auto.
    s.
    s.
    unfold Parsec.char; simpl char. rsep fail auto.
    s.
    unfold Parsec.char; simpl char; rsep fail auto; rcombine; rsep fail auto.
    unfold ans_str_correct, okaystr, errorstr, okay, error; destruct ans; rsep fail auto; sep fail auto.
    s.
    s.
    s.
    s.
    s.    
    unfold ans_str_correct, okay, error, okaystr, errorstr; unfold char in *; rsep fail auto; destruct ans; sep fail auto.
    s.
    unfold Parsec.char, rep, ans_str_correct, okay, error, okaystr, errorstr in *; unfold char in *; rsep ltac:(progress norm_list) auto.
    unfold Parsec.char in *. simpl char in *. rewrite H3 in H4. rewrite (pack_injective H4) in *. rewrite H10 in *. rsep fail auto.
    cut_pure.
    Lemma ec_ok_parse : forall local remote res reply' q x0 x (fd : File (BoundSocketModel local remote) (R :: W :: nil)) x3 x2 n str c,
      res = reply q x0 ->
      reply' = AI.printer res ->
      ecorrect fd x x0 x2 ->
      parses AI.grammar (nthtail str 0) (Okay AsciiCharset c q (nthtail str (n + 0))) ->
      x3 = str ->
      str <> nil ->
      ecorrect fd x (mutate q x0)
      (Flush fd :: WroteString fd reply' ++
        A.AppIO q x0 res (mutate q x0) ++ ReadLine fd x3 ++ x2).
      intros; subst; econstructor; eauto. 
    Qed.
    Hint Resolve pack_injective ec_ok_parse.
    eauto.
    s.
    s.
    s.
    s.
    s.
    unfold Parsec.char, ans_str_correct, okay, error, okaystr, errorstr in *; simpl char in *; rsep fail auto. norm_list. rsep fail auto.
    cut_pure. unfold Parsec.char in *. simpl char in *. rewrite H2 in H3.
    Lemma ec_err_parse : forall local remote reply' x0 x (fd : File (BoundSocketModel local remote) (R :: W :: nil)) x3 str x1 e',
      reply' = AI.err e' ->
      ecorrect fd x0 x1 x ->
      parses AI.grammar (nthtail x3 0) (Error AsciiCharset A.Q e') ->
      x3 = str ->
      str <> nil ->
      ecorrect fd x0 x1
      (Flush fd :: WroteString fd reply' ++ ReadLine fd str ++ x).
      intros; subst; econstructor; eauto. 
    Qed.
    Hint Resolve ec_err_parse.
    eapply ec_err_parse; eauto. unfold reply'; eauto. subst; eauto.

    s.
    s.
    s.
  Qed.

  Definition init : 
    STsep (__)
          (fun cm:(context * [cmodel]) => hprop_unpack (snd cm) 
            (fun m => rep (fst cm) m * [inv m])).
    refine A.init.
  Qed.

  Definition cleanup : forall (t : A.T) (m : [A.M]),
    STsep (m ~~ rep t m * [inv m])
          (fun _:unit => __).
    refine A.cleanup.
  Qed.

End AppServer.


(* An applications that our server can run. *)
Module Type AppNoInv.
  Parameter Q: Set. (** Type of parsed queries **)
 
  Parameter T  : Set.              (** Type of Execution context **)
  Parameter RR : Set.              (** Type of the return value **)
  Parameter M  : Set.              (** Modeling type for the context **)

  Parameter rep : T -> M -> hprop. (** Context representation **)

  Parameter func : Q -> M -> (RR * M). (** The function we implement **)
  Parameter AppIO : Q -> M -> RR -> M -> Trace.
 
  Parameter exec : forall (t : T) (q : Q) (m : [M]) (tr : [Trace]),
    STsep (tr ~~ m ~~ rep t m * traced tr) 
          (fun r : RR => tr ~~ m ~~ 
           let m' := snd (func q m)
           in  [r = fst (func q m)] * [m' = snd (func q m)] * 
               rep t m' * 
               traced (AppIO q m r m' ++ tr)).
  Parameter init :
    STsep (__)
          (fun tm : T * [M] => hprop_unpack (snd tm) (fun m => rep (fst tm) m)).

  Parameter cleanup : forall (t : T) (m : [M]),
    STsep (m ~~ rep t m)
          (fun _:unit => __).

End AppNoInv.

Module ADD_INV(A : AppNoInv) : App.
  Definition Q := A.Q. (** Type of parsed queries **)
 
  Definition T := A.T.               (** Type of Execution context **)
  Definition RR := A.RR.              (** Type of the return value **)
  Definition M := A.M.              (** Modeling type for the context **)

  Definition rep := A.rep.  (** Context representation **)
  Definition I (_:M) := True.         (** Context Invariant **)

  Definition func := A.func. (** The function we implement **)

  Definition AppIO := A.AppIO.

  Definition exec : forall (t : T) (q : Q) (m : [M]) (tr : [Trace]),
    STsep (tr ~~ m ~~ rep t m * traced tr * [I m]) 
          (fun r : RR => tr ~~ m ~~ 
           let m' := snd (func q m)
           in  [r = fst (func q m)] * rep t m' * [I m'] * 
               traced (AppIO q m r m' ++ tr)).
    intros. refine {{A.exec t q m tr}};
    unfold rep; rsep fail auto. unfold I; sep fail auto. 
  Qed.

  Definition init :
    STsep (__)
          (fun tm : T * [M] => hprop_unpack (snd tm) (fun m => rep (fst tm) m * [I m])).
    refine {{A.init}}.
    rsep fail auto.
    unfold rep; rsep fail auto. unfold I, M, T in *. rewrite H in H0. rewrite (pack_injective H0). sep fail auto.
  Qed.
  
  Definition cleanup : forall (t : T) (m : [M]),
    STsep (m ~~ rep t m * [I m])
          (fun _:unit => __).
    intros; refine {{A.cleanup t m}};
    unfold I, rep; rsep fail auto.
  Qed.    

  Theorem func_preserves_I : forall q m, I m -> I (snd (func q m)).
    unfold I; auto.
  Qed.
End ADD_INV.
