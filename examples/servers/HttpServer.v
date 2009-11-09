Require Import Ynot Basis.
Require Import List Ascii String.
Require Import IO FS Net.
Require Import TcpServer SslServer.
Require Import Stream HttpParser.
Require Import AppServer.
Require Import RSep.
Require Import Charset.

Opaque ReadString.
Opaque WroteString.
Opaque ReadAll.
Opaque la2str str2la.

Set Implicit Arguments.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Module HttpAppStateParams (AP : App) (AI : AppInterface with Module A := AP) : TcpServer.STATE_EXECPARAMS.

  Definition context := AP.T.
  Definition cmodel := AP.M.
  Definition rep := AP.rep.
  Definition inv := AP.I.

  Definition mutate a (b : cmodel) := snd (AP.func a b).
  Definition reply  a (b : cmodel) := fst (AP.func a b).

  Definition crlf : string := String (ascii_of_nat 13) (String (ascii_of_nat 10) EmptyString).

  Definition HTTP_ok  (len : nat) := str2la ("HTTP/1.0 200 OK" ++ crlf ++ "Content-Length: " ++ (ntos len) ++ crlf ++ crlf)%string.
  Definition HTTP_bad             := str2la "HTTP/1.0 400 Bad Request".

  Definition ReadQuery (fp : list mode) (fm : fd_model) (fd : File fm fp) strs :=
    List.fold_right (fun s l => ReadLine fd (str2la s) ++ l) nil strs.

  Definition QueryRead (strs : list string) (res : option string) : Prop :=
    match res,strs with
      | None,_ => True
      | Some str,nil => False
      | Some str,a :: b => a = (String "013"%char (String "010"%char EmptyString)) /\
                           str = List.fold_left (fun a c => String.append c a) (a :: b) EmptyString
    end.
  
  Definition hexDig (c : ascii) : nat :=
    match c with 
      | "0" => 0
      | "1" => 1
      | "2" => 2
      | "3" => 3
      | "4" => 4
      | "5" => 5
      | "6" => 6
      | "7" => 7
      | "8" => 7
      | "9" => 9
      | "A" => 10
      | "B" => 11
      | "C" => 12
      | "D" => 13
      | "E" => 14
      | "F" => 15
      | _ => 0
    end%char.

  Definition unify (c1 : ascii) (c2 : ascii) : ascii :=
    ascii_of_nat ((hexDig c1) * 16 + (hexDig c2)).

  Fixpoint descape (s : string) : string :=
    match s with
      | EmptyString => EmptyString
      | String "+"%char s' => String " "%char (descape s')
      | String "%"%char (String c1 (String c2 s')) => String (unify c1 c2) (descape s')
      | String a b => String a (descape b)
    end.


  Fixpoint extractQuery (s : string) : string :=
    match s with
      | EmptyString => EmptyString
      | String "?"%char (String "q"%char (String "=" r)) => descape r
      | String _ r => extractQuery r
    end.

  Inductive acorrect (str : list ascii) : cmodel -> cmodel -> list ascii -> Trace -> Prop :=
  | AppOk  : forall p1 p3 (q: AP.Q) (m m' : cmodel) (r: AP.RR),
       m' = snd (AP.func q m) -> r = fst (AP.func q m) -> 
       Parsec.parses AI.grammar str (Parsec.Okay AsciiCharset p1 q p3) ->
       acorrect str m m' (AI.printer r) (AP.AppIO q m r m')
  | AppErr : forall e (m m' : cmodel),
       m' = m -> Parsec.parses AI.grammar str (Parsec.Error AsciiCharset _ e) ->
       acorrect str m m (AI.err e) nil.

  Inductive hcorrect (local remote : SockAddr) 
    (fd : File (BoundSocketModel local remote) (R :: W :: nil)) 
    (str : list ascii) : cmodel -> cmodel -> Trace -> Prop :=
  | HttpOk  : forall (q: list ascii) (m m' : cmodel) resp proc is n method uri ver headers body,
       acorrect q m m' resp proc ->
       INSTREAM.stream_elts is = [str]%inhabited ->
       (HTTP_correct is 0 (Some (n, ((method, uri, ver), headers, body)))) empty ->
       la2str q = extractQuery uri ->
       hcorrect fd str m m' (WroteString fd resp ++ WroteString fd (HTTP_ok (List.length resp)) ++ proc)

  | HttpErr : forall (m m' : cmodel) is,
       m = m' -> 
       INSTREAM.stream_elts is = [str]%inhabited ->
       (HTTP_correct is 0 None) empty ->
       hcorrect fd str m m' (WroteString fd HTTP_bad).

  Inductive ccorrect' (local remote : SockAddr) 
    (fd : File (BoundSocketModel local remote) (R :: W :: nil)) :
    cmodel -> cmodel -> Trace -> Prop :=
  | RWBad : forall m m' strs, 
       QueryRead strs None -> m = m' -> ccorrect' fd m m' (ReadQuery fd strs)
  | RWCorrect : forall proc m m' str strs, 
       hcorrect fd str m m' proc -> QueryRead strs (Some (la2str str)) ->
       ccorrect' fd m m' (Flush fd :: proc ++ ReadQuery fd strs).

  Definition ccorrect := ccorrect'.  

  Definition init :
    STsep (__)
          (fun cm:(context * [cmodel]) => hprop_unpack (snd cm)
            (fun m => rep (fst cm) m * [inv m])).
    refine AP.init.
  Qed.
  
  Ltac unfold_all := repeat progress unfold Parsec.char, char, AsciiCharset, Parsec.ans_str_correct, Parsec.okay, Parsec.error, Parsec.okaystr, Parsec.errorstr in *.

  Ltac solver := auto.

  Ltac s := solve [ rsep fail solver; unfold_all; rsep fail auto ].

  Definition delegateParse (str : list ascii) :
    STsep (__)
          (fun res:Parsec.parse_reply_t AP.Q =>
           Exists is :@ INSTREAM.instream_t ascii, [INSTREAM.stream_elts is = [str]%inhabited] * 
              match res with 
                | Parsec.ERROR c _ => @Parsec.error AsciiCharset _ [0] is AI.grammar c
                | Parsec.OKAY c n q => @Parsec.okay AsciiCharset _ [0] is AI.grammar c n q
              end).
    refine (fun str =>
      is  <- STRING_INSTREAM.instream_of_list_ascii str <@> _ ;
      ans <- AI.parser is (inhabits 0) <@> _ ;
      INSTREAM.close is <@> ([INSTREAM.stream_elts is = [str]%inhabited] *
                               match ans with 
                                 | Parsec.ERROR c _ => @Parsec.error AsciiCharset _ [0] is AI.grammar c
                                 | Parsec.OKAY c n q => @Parsec.okay AsciiCharset _ [0] is AI.grammar c n q
                               end) ;;
      {{Return ans}}); unfold char;
    solve [ s 
          | rsep fail auto; unfold_all; destruct ans; sep fail auto
          | rsep fail auto; rewrite H0; sep fail auto ].
  Qed.

  Theorem fl_app : forall x b c,
    (fold_left (fun a c => c ++ a) x c ++ b = fold_left (fun a c => c ++ a) x (c ++ b))%string.
    induction x.
      auto.
      simpl. intros. rewrite IHx.
      Lemma string_app_ass : forall a b c, ((a ++ c) ++ b = a ++ c ++ b)%string.
        induction a; auto.
        intros; simpl. rewrite IHa. auto.
      Qed.
      rewrite string_app_ass. auto.
  Qed.

  Definition readQuery : forall (fp : list mode) (fm : fd_model) (fd : File fm fp) (pf : In R fp) (tr : [Trace]),
    STsep (tr ~~ traced tr * handle fd)
          (fun res:((option string) * [list string]) => tr ~~ hprop_unpack (snd res) (fun strs =>
            traced (ReadQuery fd strs ++ tr) * [QueryRead strs (fst res)] * handle fd)).
    refine (fun fp fm fd pf tr =>
      {{ Fix2 (fun str strs => tr ~~ strs ~~ traced (ReadQuery fd strs ++ tr) * [str = List.fold_left (fun a c => String.append c a) strs EmptyString] * handle fd)
              (fun str strs res => tr ~~ hprop_unpack (snd res) (fun strs =>
                traced (ReadQuery fd strs ++ tr) * [QueryRead strs (fst res)] * handle fd))
              (fun self str strs =>
                ln' <- readline fd pf (inhabit_unpack2 tr strs (fun tr strs =>  ReadQuery fd strs ++ tr)) <@> _ ;
                let ln := la2str ln' in
                if string_dec ln EmptyString then 
                  {{ Return (None, (strs ~~~ ln :: strs)) }}
                else if string_dec ln crlf then
                  {{ Return (Some (String.append str ln), (strs ~~~ ln :: strs)) }}
                else 
                  {{ self (String.append str ln) (strs ~~~ ln :: strs) }})
              EmptyString [nil]%inhabited }} ); try clear self.
    s.
    s.
    s.
    rsep fail auto. unfold ln in  *. rewrite H1 in *. simpl.
    assert (ReadLine fd ln' ++ ReadQuery fd x ++ x1 = ReadQuery fd x2 ++ x1).
      simpl in H4. rewrite <- (pack_injective H4). simpl. rewrite la2str_inv_str2la. norm_list. auto.
    rewrite H5. rsep fail auto.
    s.
    rsep fail auto. rewrite H1 in *. simpl in *. rewrite <- (pack_injective H4). simpl. unfold ln. rewrite la2str_inv_str2la. norm_list. rsep fail auto.
    Ltac sep_pure := idtac;
      match goal with 
        | [ |- _ ==> [?X] ] => assert X; [ | rsep fail auto ]
      end.
    sep_pure. split. unfold ln in *. rewrite _H0. auto.
    rewrite H2. pose (fl_app x (la2str ln') ""). simpl in e. rewrite e.
    Lemma string_app_nil : forall a, a = (a ++ "")%string.
      induction a; firstorder.
      simpl. rewrite <- IHa. auto.
    Qed.
    rewrite <- string_app_nil. auto.

    rsep fail auto. simpl. norm_list. unfold ln. rewrite la2str_inv_str2la. rsep fail auto. sep_pure.
    rewrite H1. pose (fl_app x (la2str ln') ""). simpl in e. rewrite e.
    rewrite <- string_app_nil. auto.
    s.
    s.
    s.
  Qed.

  Ltac combine_all :=
    repeat match goal with
      | [ H : ?P |- _ ] => 
        match P with 
          | context [ inhabit_unpack ?X _ ] =>
            match goal with 
              | [ H' : X = [_]%inhabited |- _ ] => rewrite H' in H; simpl inhabit_unpack in H
            end
          | context [ inhabit_unpack2 ?X _ _ ] => 
            match goal with 
              | [ H' : X = [_]%inhabited |- _ ] => rewrite H' in H; simpl inhabit_unpack2 in H
            end
          | context [ inhabit_unpack2 _ ?X _ ] => 
            match goal with 
              | [ H' : X = [_]%inhabited |- _ ] => rewrite H' in H; simpl inhabit_unpack2 in H
            end
          | context [ match ?X with | [_]%inhabited => _ end ] =>
            match goal with 
              | [ H' : X = [_]%inhabited |- _ ] => rewrite H' in H; simpl in H
            end
        end
    end;
    repeat match goal with 
             | [ H : [_]%inhabited = [_]%inhabited |- _ ] => rewrite <- (pack_injective H)
           end.

  Ltac get_ex := idtac;
    match goal with 
      | [ |- context [ [?X]%inhabited = [_]%inhabited ] ] => exists X; split; auto
    end.

  Definition io : forall (local remote : SockAddr)
    (fd : File (BoundSocketModel local remote) (R :: W :: nil)) (tr : [Trace])
    (ctx : context) (m : [cmodel]),
    STsep (tr ~~ m ~~ traced tr * handle fd * rep ctx m * [inv m])
          (fun res':([Trace] * [cmodel]) => m ~~ tr ~~
            hprop_unpack (fst res') (fun tr' =>
              hprop_unpack (snd res') (fun m' =>
                traced (tr' ++ tr) * [ccorrect fd m m' tr'] * rep ctx m' * [inv m']))).
    refine (fun local remote fd tr ctx m =>
      req' <- readQuery fd rw_readable tr <@> _ ;
      match req' as r' return req' = r' -> _ with 
        | (None,strs) => fun _ => 
          close fd <@> _ ;;
          {{ Return (strs ~~~ ReadQuery fd strs, m) }}
        | (Some req,strs) => fun _ =>
          (** Parse **)
          is <- STRING_INSTREAM.instream_of_list_ascii (str2la req) <@> _ ;
          parse <- http_parse is 0 <@> _ ;
          INSTREAM.close is <@> (m ~~ tr ~~ strs ~~
                                  hprop_unpack (INSTREAM.stream_elts is) (fun l0 : list ascii =>
                                    [l0 = str2la req] *
                                    traced (ReadQuery fd strs ++ tr) * [QueryRead strs (Some req)] *
                                    handle fd * rep ctx m * [inv m])) *
                                (HTTP_correct is 0 parse) ;;
          let tr'' := inhabit_unpack2 strs tr (fun strs tr => (ReadQuery fd strs ++ tr)) in

          match parse as parse'
            return STsep ([parse = parse'] * _)
                         (fun res':([Trace] * [cmodel]) => m ~~ tr ~~
                           hprop_unpack (fst res') (fun tr' =>
                             hprop_unpack (snd res') (fun m' =>
                               traced (tr' ++ tr) * [ccorrect fd m m' tr'] * rep ctx m' * [inv m']))) with
            | None => writeline fd HTTP_bad rw_writeable tr'' <@> _ ;;                     
                      flush fd (tr'' ~~~ WroteString fd HTTP_bad ++ tr'') rw_writeable <@> _ ;;
                      close fd <@> _ ;;
                      {{Return (inhabit_unpack strs (fun strs => Flush fd :: WroteString fd HTTP_bad ++ ReadQuery fd strs),
                                  m)}}
                  
            | Some (c,((method, uri, version), headers, body)) =>
              let query := str2la (extractQuery uri) in
              pr <- delegateParse query <@> _ ;
              match pr as pr'
                return STsep (m ~~ tr ~~ hprop_unpack strs (fun strs : list string =>
                                hprop_unpack (INSTREAM.stream_elts is) (fun l0 : list ascii =>
                                  [inv m] * rep ctx m * handle fd *
                                  HTTP_correct is 0 (Some (c, (method, uri, version, headers, body))) *
                                  [l0 = str2la req] *
                                  traced (ReadQuery fd strs ++ tr) * [QueryRead strs (Some req)])) *
                                  (Exists is0 :@ INSTREAM.instream_t (Parsec.char AsciiCharset),
                                    [INSTREAM.stream_elts is0 = [query]%inhabited] *
                                    match pr' with
                                      | Parsec.OKAY c0 n q => Parsec.okay [0] is0 AI.grammar c0 n q
                                      | Parsec.ERROR c0 _ => Parsec.error [0] is0 AI.grammar c0
                                    end) )
                             (fun res':([Trace] * [cmodel]) => m ~~ tr ~~
                               hprop_unpack (fst res') (fun tr' =>
                                 hprop_unpack (snd res') (fun m' =>
                                   traced (tr' ++ tr) * [ccorrect fd m m' tr'] * rep ctx m' * [inv m'])))
                with 
                | Parsec.ERROR e' c' =>
                  writeline fd (HTTP_ok (List.length (AI.err e'))) rw_writeable tr'' <@> _ ;;
                  writeline fd (AI.err e') rw_writeable (tr'' ~~~ WroteString fd (HTTP_ok (List.length (AI.err e'))) ++ tr'') <@> _ ;;
                  flush fd (tr'' ~~~ WroteString fd (AI.err e') ++ WroteString fd (HTTP_ok (List.length (AI.err e'))) ++ tr'') rw_writeable <@> _ ;;
                  close fd <@> _ ;;
                  {{Return (inhabit_unpack2 strs m (fun strs m => 
                              Flush fd :: WroteString fd (AI.err e') ++ WroteString fd (HTTP_ok (List.length (AI.err e'))) ++ ReadQuery fd strs),
                            m)}}
                  
                | Parsec.OKAY c' n q =>
                  res <- AP.exec ctx q m tr'' <@> _ ;
                  let tr''' := inhabit_unpack2 tr'' m (fun tr'' m => AP.AppIO q m res (snd (AP.func q m)) ++ tr'') in
                    writeline fd (HTTP_ok (List.length (AI.printer res))) rw_writeable tr''' <@> _ ;;
                    writeline fd (AI.printer res) rw_writeable (tr''' ~~~ WroteString fd (HTTP_ok (List.length (AI.printer res))) ++ tr''') <@> _ ;;
                    flush fd (tr''' ~~~ WroteString fd (AI.printer res) ++ WroteString fd (HTTP_ok (List.length (AI.printer res))) ++ tr''') rw_writeable <@> _ ;;
                    close fd <@> _ ;;
                    {{Return (inhabit_unpack2 strs m (fun strs m => 
                          Flush fd :: WroteString fd (AI.printer res) ++ WroteString fd (HTTP_ok (List.length (AI.printer res))) ++ AP.AppIO q m res (snd (AP.func q m)) ++ ReadQuery fd strs),
                          m ~~~ (snd (AP.func q m)))}}
              end
          end
      end (refl_equal _)); unfold char in *.
    s.
    s.
    s.
    s.
    solve [ rsep fail auto; unfold char in *; unfold Parsec.char in *; rsep fail auto ].
    s.
    solve [ unfold rep; rsep fail auto; destruct parse; sep fail auto ].
    s.
    s.
    s.
    solve [ unfold tr'',rep in *; rsep fail auto ].
    s.
    solve [ unfold tr''',tr'',rep in *; do 2 (unfold cmodel; rsep fail auto); fold cmodel; rsep fail auto ].
    s.
    solve [ unfold tr''',tr'',rep; do 2 rsep fail auto ].
    s.
    solve [ unfold tr''',tr''; do 2 rsep fail auto ].
    s.
    inhabiter. canceler. sep fail auto.
    s.
    solve [ unfold tr''',tr''; do 2 rsep fail auto ].
    unfold tr''', tr'', rep, inv,Parsec.okay. intros. rsep fail auto. inhabiter. intro_pure. rewrite H in *. 
    simpl in *.
    combine_all. norm_list. unfold rep, inv. rsep fail auto.
    unfold HTTP_correct,Packrat.Packrat.ans_correct. simpl. rewrite H8. inhabiter. intro_pure.
    cut_pure. sep fail auto.
      unfold ccorrect. pose (@RWCorrect local remote fd (WroteString fd (AI.printer res) ++ WroteString fd (HTTP_ok (List.length (AI.printer res))) ++ AP.AppIO q x res (snd (AP.func q x))) x (snd (AP.func q x)) (str2la req) x5). norm_list_hyp c0. apply c0; try (rewrite str2la_inv_la2str; assumption).
      pose (@HttpOk local remote fd (str2la req) query x (snd (AP.func q x)) (AI.printer res) (AP.AppIO q x res (snd (AP.func q x))) is c method uri version headers body). norm_list. norm_list_hyp h. apply h.
      pose (@AppOk query c' (Parsec.nthtail query (n + 0)) q x (snd (AP.func q x)) res). apply a; trivial. rewrite H16 in *. auto. 
        unfold HTTP_correct. unfold Packrat.Packrat.ans_correct. unfold_all. simpl. rewrite H8. unfold hprop_unpack. exists x7. split; trivial.
        get_ex. unfold hprop_inj. split; auto. rewrite (pack_injective H25). rewrite (pack_injective H24). auto. unfold query. rewrite str2la_inv_la2str. auto.
    solve [ unfold tr'' in *; do 2 rsep fail auto ].
    s.
    solve [ unfold tr'' in *; do 2 rsep fail auto ].
    s.
    solve [ unfold tr'' in *; do 2 rsep fail auto ].
    s.
    inhabiter. canceler. sep fail auto.
    s.
    s.
    
    unfold tr'' in *; rsep fail auto. inhabiter. rewrite H in *. simpl in *.
    combine_all. norm_list. canceler. unfold Parsec.error. unfold HTTP_correct. inhabiter. intro_pure. simpl in H8. rewrite <- (pack_injective H8).
    unfold rep, inv,Packrat.Packrat.ans_correct. inhabiter. intro_pure. norm_list. canceler. rewrite H0 in H3. rewrite (pack_injective H3). canceler.
    cut_pure.
    unfold ccorrect. pose (CC := @RWCorrect local remote fd (WroteString fd (AI.err e') ++ WroteString fd (HTTP_ok (List.length (AI.err e')))) x2 x2 (str2la req) x4). norm_list. norm_list_hyp CC. apply CC; trivial.
    pose (CCC := @HttpOk local remote fd (str2la req) query x2 x2 (AI.err e') nil is c method uri version headers body); norm_list_hyp CCC; apply CCC.
    apply (@AppErr query e' x2 x2); trivial.
      rewrite <- (pack_injective H10) in *. unfold_all. simpl in *. rewrite H13 in H11. rewrite (pack_injective H11) in *. assumption. rewrite H15 in *. auto.
      unfold HTTP_correct. unfold Packrat.Packrat.ans_correct. unfold hprop_unpack. exists x6. split; auto.
      get_ex. unfold hprop_inj. split; auto. rewrite (pack_injective H19). simpl in *. rewrite H7 in H18. rewrite (pack_injective H18). auto.
      unfold query. rewrite str2la_inv_la2str. trivial. rewrite str2la_inv_la2str; trivial.

    solve [ unfold tr''; do 2 rsep fail auto ].
    s.
    solve [ unfold tr''; do 2 rsep fail auto ].
    s.
    inhabiter; canceler; sep fail auto.
    s.
    s.

    unfold inv,rep,HTTP_correct,Packrat.Packrat.ans_correct. intros; inhabiter. intro_pure. rewrite H14 in *. simpl in *. unfold tr'' in H.
    combine_all. rsep fail auto. rewrite H1 in *. rewrite (pack_injective H8). canceler. unfold tr'' in H17. rewrite H0 in H17. rewrite H2 in H17. simpl in H17. rewrite <- (pack_injective H17). norm_list. canceler.
    cut_pure.
      unfold ccorrect. 
      apply (@RWCorrect local remote fd (WroteString fd HTTP_bad) x8 x8 (str2la req) x0).
      econstructor. trivial. rewrite H13 in *. eassumption. unfold HTTP_correct. unfold Packrat.Packrat.ans_correct. unfold_all. simpl in *. rewrite H5. unfold hprop_unpack. exists (str2la req). split. rewrite H13; auto. 
      get_ex. unfold hprop_inj. split; auto. rewrite (pack_injective H6). rewrite H13 in *. auto.
      unfold QueryRead. rewrite str2la_inv_la2str. auto.

    s.
    s.
    s.
    rsep fail auto. rewrite H4 in H5,H6. simpl in H5,H6. rewrite <- (pack_injective H6). canceler. subst req'. simpl in H1. rewrite H1 in H5. simpl in H5. rewrite <- (pack_injective H5). canceler.
    cut_pure; unfold ccorrect; constructor; auto.
  Qed.

End HttpAppStateParams.
