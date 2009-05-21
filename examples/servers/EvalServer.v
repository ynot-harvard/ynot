Require Import Ynot Basis.
Require Import UdpServer TcpServer SslServer.
Require Import IO Net FS.
Require Import Parsers.
Require Import Stream Parsec Charset.
Require Import List Ascii String.

Require Import RSep.
Import STRING_INSTREAM.
Import INSTREAM.
Import Expressions.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Set Implicit Arguments.

Module Type EVALPARAMS.

  Variable t: Set.
  Variable grammar : Term AsciiCharset t.
  Variable parser  : parser_t grammar.
  Variable e : list ascii.      (* error list ascii *)
  Variable f : t -> list ascii. (* value serializer *)

End EVALPARAMS.

Module PrefixServer : EVALPARAMS.
 Import Expressions.
 Definition t := nat.
 Definition grammar : Term AsciiCharset nat := prefix.
 Definition parser := prefix_p.
 Require Import Ascii.
 Open Scope char_scope.

 Definition e : list ascii := str2la "error"%string.
 Definition f x := ntos 3 x nil.

End PrefixServer.

Module UdpEvalServerParams (A : EVALPARAMS) : UdpServer.EXECPARAMS.
  Export A.

  Definition resp (CH : Charset) (r :reply_t CH t) := 
    match r with
      | Okay _ a _ => f a 
      | Error _ => e 
    end.

  Inductive ccorrect' (req : list ascii) : Trace -> Prop :=
  | NilCorrect : ccorrect' req nil.
  Definition ccorrect := ccorrect'.

  Inductive reply' (req : list ascii) : list ascii -> Prop :=
  | ReplyIdentity : forall v, parses grammar req v -> reply' req (resp v).
  Definition reply := reply'.

  Definition io : forall (req : list ascii) (tr : [Trace]),
    STsep (tr ~~ traced tr)
          (fun r:(list ascii * [Trace]) => tr ~~ tr' :~~ (snd r) in traced (tr' ++ tr) * [reply req (fst r)] * [ccorrect req tr']).
    intros. refine ( 
      is  <- instream_of_list_ascii req <@> _ ;
      ans <- parser is (inhabits 0) <@> (tr ~~ elts :~~ (stream_elts is) in traced tr * [elts = req]);

      close is <@> _ ;;
      {{ Return (match ans with
                   | ERROR _ _ =>  e
                   | OKAY _ _ a => f a
                 end, [nil]%inhabited) }}).
    rsep fail auto.
    rsep fail auto.
    lazy zeta. rsep fail auto.
    rsep fail auto.
    solve [ unfold ans_str_correct, okaystr, errorstr;
            instantiate (1 := tr ~~ 
              hprop_unpack (stream_elts is)
              (fun elts => 
                traced tr * [elts = req] *
                match ans with
                  | OKAY c m v =>
                    @okay AsciiCharset _ [0] is grammar c m v
                  | ERROR c _ => @error AsciiCharset _ [0] is grammar c
                end));
            destruct ans; sep fail auto ].
    solve [ sep fail auto ].
    solve [ sep fail auto ].
    unfold char, okay, error in *. rsep fail auto. subst; norm_prod. destruct ans. rsep ltac:(norm_list) auto. cut_pure. unfold ccorrect; constructor. unfold reply. 
    pose (ReplyIdentity H1). simpl in *. unfold char in *. rewrite H in H0. rewrite <- (pack_injective H0); auto.

    
    rsep ltac:(norm_list) auto. cut_pure; try constructor; auto. unfold reply. pose (ReplyIdentity H1). simpl in *. unfold char in *. rewrite H in H0. rewrite <- (pack_injective H0); auto.
  Qed.

End UdpEvalServerParams.

Module TcpEvalServerParams (A : EVALPARAMS).
  Export A.

  Ltac solver := auto.
  
  Definition resp (CH : Charset) (r :reply_t CH t) := 
    match r with
      | Okay _ a _ => f a 
      | Error _ => e 
    end.

  Inductive ccorrect' (local remote : SockAddr) (fd : File (BoundSocketModel local remote) (R :: W :: nil)) : Trace -> Prop :=
  | DoneCorrect : forall past, ecorrect fd past -> ccorrect' fd (Flush fd :: ReadLine fd nil ++ past)
  with ecorrect (local remote : SockAddr) (fd : File (BoundSocketModel local remote) (R :: W :: nil)) : Trace -> Prop :=
  | NilCorrect : ecorrect fd nil
  | ConsCorrect : forall s v past rep, s <> nil -> rep = resp v -> ecorrect fd past -> parses grammar s v ->
    ecorrect fd (Flush fd :: WroteString fd rep ++ ReadLine fd s ++ past).
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

  Definition io : forall (local remote : SockAddr) (fd : File (BoundSocketModel local remote) (R :: W :: nil)) (tr : [Trace]),
    STsep (tr ~~ traced tr * handle fd)
          (fun tr':[Trace] => tr ~~ tr' ~~ traced (tr' ++ tr) * [ccorrect fd tr']).
    intros. refine (
      lt <- Fix (fun tr' => tr ~~ tr' ~~ traced (tr' ++ tr) * [ecorrect fd tr'] * handle fd)
                (fun _ tr' => tr ~~ tr' ~~ traced (tr' ++ tr) * [ccorrect fd tr'])
                (fun self tr' =>
                  str <- readline fd rw_readable (traceCombine tr' tr) <@> (tr' ~~ [ecorrect fd tr']);
                  if empty_eq str then
                    flush fd (traceAfter tr' tr (fun t => ReadLine fd str ++ t)) rw_writeable <@> 
                      (tr' ~~ [ecorrect fd tr']) ;;
                    FS.close fd <@> (tr ~~ tr' ~~ [ecorrect fd tr'] * traced (Flush fd :: ReadLine fd str ++ tr' ++ tr)) ;;
                    {{Return (tr' ~~~ Flush fd :: ReadLine fd str ++ tr')}}
                  else
                    is  <- instream_of_list_ascii str <@> _ ;
                    ans <- parser is (inhabits 0) <@> _ ;
                    close is <@> _ ;;
                    let reply := match ans with
                                   | ERROR _ _ =>  e
                                   | OKAY _ _ a => f a
                                 end in
                    writeline fd reply rw_writeable (traceAfter tr' tr (fun t => ReadLine fd str ++ t)) <@> _;;
                    flush fd (traceAfter tr' tr (fun t => WroteString fd reply ++ ReadLine fd str ++ t)) rw_writeable <@> _;;
                    {{self (tr' ~~~ Flush fd :: WroteString fd reply ++ ReadLine fd str ++ tr')}})
                [nil]%inhabited;
      {{Return lt}}); try clear self; simpl char in *.
    unfold traceAfter, traceCombine. rsep fail auto.
    solve [ rsep fail auto ].
    solve [ unfold traceAfter, traceCombine; rsep fail auto ].
    solve [ unfold traceAfter, traceCombine; rsep fail auto ].
    solve [ unfold traceAfter, traceCombine; rsep fail auto ].
    solve [ unfold traceAfter, traceCombine; rsep fail auto ].
    solve [ unfold traceAfter, traceCombine; rsep fail auto ].
    solve [ unfold traceAfter, traceCombine, ccorrect; rsep ltac:(norm_list) auto; cut_pure; subst; constructor; auto ].
    solve [ unfold traceAfter, traceCombine; rsep fail auto ].
    solve [ unfold traceAfter, traceCombine; rsep fail auto ].
    unfold traceAfter, traceCombine. rsep fail auto.
    instantiate (1 := tr ~~ tr' ~~ x1 :~~ (stream_elts is) in [x1 = str] * handle fd * [ecorrect fd tr'] * traced (ReadLine fd x1 ++ tr' ++ tr)). sep fail auto. (** Should be able to solve this? **)
    solve [ unfold traceAfter, traceCombine; rsep fail auto ].
    rsep fail auto.
    unfold ans_str_correct, okaystr, okay, errorstr, error.
    instantiate (1 := tr ~~ tr' ~~ x1 :~~ (stream_elts is) in
      traced (ReadLine fd x1 ++ tr' ++ tr) * handle fd * [ecorrect fd tr'] * [x1 = str] *
        [parses grammar (nthtail x1 0) (match ans with
                                          | OKAY c m v => @Okay AsciiCharset _ c v (nthtail x1 m)
                                          | ERROR c _ => @Error AsciiCharset _ c
                                        end)]).
    cbv zeta. rsep fail auto. destruct ans; rsep fail auto. unfold Parsec.char in *. simpl char in *.
    assert (n + 0 = n). omega. rewrite H6. rewrite H1 in H4. rewrite (pack_injective H4). sep fail auto. (** We don't handle Exists yet **)
    unfold Parsec.char in *; simpl char in *. rewrite H1 in H4. rewrite (pack_injective H4). rsep fail auto.
    (** Solvable with some additional instramentation, unfolding of char **)

    solve [ unfold traceAfter, traceCombine; rsep fail auto ].
    unfold traceAfter, traceCombine. rsep fail auto.
    instantiate (1 := (tr' ~~ x1 :~~ (stream_elts is) in [ecorrect fd tr'] * [x1 = str] *
      [parses grammar (nthtail x1 0) match ans with
                                        | OKAY c m v => @Okay AsciiCharset _ c v (nthtail x1 m)
                                        | ERROR c _ => @Error AsciiCharset _ c
                                      end])%hprop).
    cbv zeta. subst. rsep fail auto. 
    solve [ unfold traceAfter, traceCombine; rsep fail auto ].
    solve [ unfold traceAfter, traceCombine; rsep fail auto ]. 
    solve [ unfold traceAfter, traceCombine; rsep fail auto ].
    unfold traceAfter, traceCombine; rsep fail auto. 
    simpl. norm_list. rsep fail auto. cut_pure.
      eapply ConsCorrect; auto. 
      instantiate (1 := match ans with
                          | OKAY c m v => @Okay AsciiCharset _ c v (nthtail x0 m)
                          | ERROR c _ => @Error AsciiCharset t c
                        end). destruct ans; auto.
      destruct ans; rewrite H2 in *; trivial.
    solve [ unfold traceAfter, traceCombine; rsep fail auto ].
    unfold traceAfter, traceCombine; rsep ltac:(norm_list) auto; cut_pure; constructor.
    solve [ unfold traceCombine; rsep fail auto ].
    solve [ unfold traceCombine; rsep fail auto ].
    solve [ unfold traceCombine; rsep fail auto ].
  Qed.
End TcpEvalServerParams.


Module uprefix_params := UdpEvalServerParams PrefixServer.
Module tprefix_params := TcpEvalServerParams PrefixServer.
Module sprefix_params := TcpEvalServerParams PrefixServer.

Module umes  := UdpServer.ExecImpl uprefix_params.
Module tmes' := TcpServer.ADD_STATE(tprefix_params).
Module tmes  := TcpServer.ExecImpl(tmes').
Module smes' := SslServer.ADD_STATE(sprefix_params).
Module smes  := SslServer.ExecImpl(smes').

Definition udp := umes.main.
Definition tcp := tmes.main.
Definition ssl := smes.main.
