Require Import Ynot.
Require Import List String.
Require Import Specif.
Require Import RSep.
Require Import LinkedListSeg.
Require Import Peano_dec.

Set Implicit Arguments.

Module StoreModel.

  (* For now, all columns are nats. *)
  Fixpoint Tuple n {struct n} : Set :=
    match n with 
      | 0 => unit
      | S n' => (nat * Tuple n')%type
    end.

  Definition tpl_dec : forall n (a b : Tuple n), {a = b} + {a <> b}.
    refine (fix dec (n : nat) : forall (a b : Tuple n), {a = b} + {a <> b} :=
      match n as n return forall (a b : Tuple n), {a = b} + {a <> b} with
        | 0 => fun a b => left _ _
        | S n' => fun a b =>
          if eq_nat_dec (fst a) (fst b) then
            if dec n' (snd a) (snd b) then left _ _ else right _ _
            else right _ _
      end);
    destruct a; destruct b; simpl in *; subst; auto.
    unfold not in *. intros. inversion H. auto.
    unfold not in *. intros. inversion H. auto.
  Qed.

 Section X.
  Variable n: nat.

  (* For now, a store is just a single table. *)  
  Definition Table : Set := list (Tuple n).
  
  Definition WHERE := Tuple n -> bool.
  Definition UPDATE := Tuple n -> option (Tuple n).
  Definition AGGREGATE (T : Type) := T -> Tuple n -> T.

  Fixpoint select (wh : WHERE) (rows : Table) {struct rows} : Table :=
    match rows with 
      | nil => nil
      | a :: r => 
        if wh a then 
          a :: select wh r
        else
          select wh r
    end.

  Fixpoint update (up : UPDATE) (rows : Table) {struct rows} : Table :=
    match rows with
      | nil => nil
      | a :: r => match up a with
                    | None => update up r
                    | Some x => x :: update up r
                  end
    end.

  (** foldr **)
  Fixpoint aggregate (T : Type) (agg : AGGREGATE T) (v : T) (rows : Table) {struct rows} : T :=
    match rows with 
      | nil => v
      | a :: b => agg (aggregate agg v b) a
    end.


  (** SELECT properties **)
  Theorem select_just : forall tbl tbl' wh,
    select wh tbl = tbl' ->
    (forall tpl, In tpl tbl' -> wh tpl = true /\ In tpl tbl).
    induction tbl; intros.
      simpl in H. rewrite <- H in *. inversion H0.
      simpl in H. remember (wh a) as RM. destruct RM. rewrite <- H in H0. simpl in H0. destruct H0.
        subst. split; auto. unfold In; auto.
        destruct tbl'. inversion H. inversion H. rewrite H3 in H0. destruct (IHtbl tbl' wh H3 tpl H0). split; auto. unfold In. right. auto.
      destruct (IHtbl tbl' wh H tpl H0). split; auto. unfold In; auto.
  Qed.

  Lemma tpl_eq : forall (a b : Tuple n), {a = b} + {a <> b}.
     induction n; simpl in *. decide equality.
       intros. destruct a. destruct b. pose (IHn0 t t0). destruct s. rewrite e.
       assert ({n1 = n2} + {n1 <> n2}). decide equality.
       destruct H. rewrite e0; auto. right; auto. unfold not. intros. inversion H. congruence.
       right. unfold not; intros. inversion H. congruence.
  Qed.

  Theorem select_all : forall tbl tbl' wh,
    select wh tbl = tbl' ->
    (forall tpl, In tpl tbl -> wh tpl = true -> In tpl tbl').
    induction tbl; intros.
      inversion H0.
      simpl in H. destruct (tpl_eq a tpl). subst. rewrite H1 in *. unfold In; auto.
      simpl in H0. destruct (wh a). destruct tbl'. congruence. inversion H. simpl. right. destruct H0. congruence. eapply IHtbl; auto; try eassumption.
      eapply IHtbl; auto. eassumption. destruct H0. congruence. auto. auto.
  Qed.

End X.

  Definition PROJECT (n n' : nat) := Tuple n -> Tuple n'.

  Lemma zleast : forall x, x < 0 -> False.
    intros. omega.
  Qed.

  Definition GET_COL' : forall (n c : nat) (pf : c < n), PROJECT n 1.
    refine (fix GET_COL (n c : nat) (pf : c < n) {struct n} : PROJECT n 1 :=
      match n as n' return n = n' -> c < n' -> PROJECT n' 1 with
        | 0 => fun _ pf' _ => False_rect _ (zleast pf')
        | S n' => fun _ _ tpl => match c as c' return c = c' -> Tuple 1 with 
                                 | 0 => fun _ => (fst tpl, tt)
                                 | S c' => fun pf' => @GET_COL n' c' _ (snd tpl)
                               end (refl_equal _)
      end (refl_equal _) pf).    
    omega.
  Defined.

  Definition GET_COL : forall (n c : nat) (pf : c < n), PROJECT n 1 := GET_COL'.
    
  Fixpoint PROJ (n : nat) (cols : list (sig (fun x:nat => x < n))) {struct cols} : PROJECT n (List.length cols) :=
    match cols as cols' return cols = cols' -> PROJECT n (List.length cols') with 
      | nil => fun _ _ => tt
      | a :: b => fun _ tpl => 
        (fst (GET_COL (proj2_sig a) tpl), PROJ b tpl)
    end (refl_equal _).

  (** map **)
  Fixpoint project (n n' : nat) (proj : PROJECT n n') (rows : Table n) {struct rows} : Table n' :=
    match rows with
      | nil => nil
      | a :: b => (proj a) :: project proj b
    end.

  (** GET_COL Properties **)
  Fixpoint get_col (n c : nat) (tpl : Tuple n) {struct n} : option nat :=
    match n as n' return Tuple n' -> option nat
      with 
      | 0 => fun _ => None
      | S n' => fun tpl => match c with 
                             | 0 => Some (fst tpl)
                             | S c' => get_col n' c' (snd tpl)
                           end
    end tpl.

  Theorem GET_COL_projs : forall n c t pf,
    Some (fst (@GET_COL n c pf t)) = get_col n c t.
    unfold GET_COL.
    induction n.
      intros. elimtype False. omega.
      intros. Set Printing All. destruct c. reflexivity.
      simpl. unfold GET_COL'. auto.
  Qed.

End StoreModel.

Module TableSerializer.

Section Serialize.
  Import StoreModel.

  Fixpoint toString (n : nat) : string :=
    match n with 
      | 0 => "*"%string
      | S n => String "1" (toString n)
    end.

  Fixpoint st (n' : nat) (t : Tuple n') {struct n'} : string :=
    (match n' as n'
       return Tuple n' -> string with
       | 0    => fun _ => "#"
       | S n' => fun t => toString (fst t) ++ st n' (snd t)
     end t)%string.

  Fixpoint serial' n (m : Table n) {struct m} : string :=
    match m with
      | nil => ""
      | f :: r => st n f ++ serial' r
    end%string.

  Definition serial n (m : Table n) : string :=
    (toString (List.length m) ++ ":" ++ serial' m)%string.

  Fixpoint fromString (s : string) : option (nat * string) :=
    match s with 
      | EmptyString => None
      | String "1" s' => match fromString s' with
                           | None => None
                           | Some (x,y) => Some (S x, y)
                         end
      | String "*" b => Some (0, b)
      | String _ b => None
    end.

  Fixpoint dt n (str : string) {struct n} : option (Tuple n * string) :=
    match n as n, str return option (Tuple n * string) with
      | 0, String "#" str' => Some (tt, str')
      | S n', str => match fromString str with
                  | None => None
                  | Some (v,r) => match dt n' r with
                                    | None => None
                                    | Some (vr,r) => Some ((v,vr), r)
                                  end
                end
      | _,_ => None
    end.

  Fixpoint deserial' (n cnt : nat) (str : string) {struct cnt} : option (Table n) :=
    match cnt, str with
      | 0, EmptyString => Some nil
      | S cnt', s => match dt n s with
                       | None => None
                       | Some (t,sr) => match deserial' n cnt' sr with
                                          | None => None
                                          | Some tbl => Some (t :: tbl)
                                        end
                     end
      | _,_ => None
    end.

  Definition deserial n (str : string) : option (Table n) :=
    match fromString str with
      | Some (cnt,String ":" s) => deserial' n cnt s
      | _ => None
    end.

  Lemma fromString_toString : forall n s,
    fromString (toString n ++ s) = Some (n,s).
    induction n; intros;
      [ reflexivity
      | simpl; rewrite (IHn s); trivial ].
  Qed.
  
  Lemma str_app_ass : forall (a b c : string),
    ((a ++ b) ++ c = a ++ (b ++ c))%string.
    induction a; intros;
      [ reflexivity 
      | simpl; rewrite (IHa b c); trivial ].
  Qed.

  Lemma dt_st : forall n t s, 
    dt n (st n t ++ s) = Some (t,s).
    induction n; intros; simpl in *.
      destruct t; trivial.
      rewrite str_app_ass. rewrite fromString_toString. pose (IHn (snd t) s). simpl in *. unfold Tuple in *. rewrite e. fold Tuple in *.
        assert (t = (fst t, snd t)). destruct t; auto. rewrite H. reflexivity.
  Qed.

  Lemma serial_deserial' : forall n (tbl : Table n) cnt,
    List.length tbl = cnt -> 
    deserial' n cnt (serial' tbl) = Some tbl.
    induction tbl; intros cnt H; simpl in H; rewrite <- H.
      reflexivity.
      destruct n. simpl. pose (IHtbl (List.length tbl) (refl_equal (List.length tbl))). simpl in *. rewrite e. destruct a. reflexivity.
      simpl. rewrite str_app_ass. rewrite fromString_toString. rewrite dt_st. pose (IHtbl (List.length tbl) (refl_equal (List.length tbl))). simpl in *. rewrite e.
      assert (a = (fst a, snd a)). destruct a; auto. rewrite H0; auto.
  Qed.

  Theorem serial_deserial : forall n (tbl : Table n),
    deserial n (serial tbl) = Some tbl.
    intros; unfold serial, deserial; rewrite fromString_toString; simpl; apply serial_deserial'; trivial.
  Qed.
End Serialize.

End TableSerializer.

Module Type Store.

  Export  StoreModel.

  Open Local Scope hprop_scope.

  (** Concrete type **)
  Parameter t : Set.

  Section X.
  Variable n : nat.

  (** Representation heap predicate **)
  Parameter rep : t -> Table n -> hprop.

  Parameter new : STsep (__) (fun r:t => rep r nil).
  Parameter free : forall (r : t) (m : [Table n]), 
    STsep (m ~~ rep r m) (fun _:unit => __).

  Parameter select : forall (r : t) (wh : WHERE n) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun res:Table n => m ~~ rep r m * [res = select wh m]).

  Parameter update : forall (r : t) (up : UPDATE n) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun _:unit => m ~~ rep r (update up m)).

  Parameter insert : forall (r : t) (new_rows : Table n) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun _:unit => m ~~ rep r (m ++ new_rows)).

  Parameter aggregate : forall (T : Type) (r : t) (agg : AGGREGATE n T) (v : T) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun res:T => m ~~ rep r m * [res = aggregate agg v m]).

  Parameter serial : forall (m : Table n), string.
  Parameter deserial : forall (s : string), option (Table n).
  Parameter serial_deserial : forall (tbl : Table n),
    deserial (serial tbl) = Some tbl.

  Parameter serialize : forall (r : t) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun str:string => m ~~ rep r m * [str = serial m]).
  Parameter deserialize : forall (r : t) (s : string),
    STsep (@rep r nil)
          (fun m:option [Table n] =>
	      match m with 
	  	| None => @rep r nil * [None = deserial s]
		| Some m => m ~~ rep r m * [Some m = deserial s]
              end).
End X.

  Parameter project : forall (n n' : nat) (r : t) (proj : PROJECT n n') (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun res:t * [Table n'] => m ~~ hprop_unpack (snd res) (fun m' => 
            rep r m * rep (fst res) m' * [m' = project proj m])).

End Store.

Module RefStore : Store.
  Export StoreModel.

  Open Local Scope hprop_scope.
  Open Local Scope stsepi_scope.

  Definition t := ptr.

  Section Size.
    Variable n : nat.

  Definition rep (n : nat) (p : t) (m : Table n) := p --> m.

  Ltac s := unfold t, rep; sep fail auto.

  Definition new : STsep (__) (fun r:t => @rep n r nil).
    intros; refine (n <- New (@nil (Tuple n));
            {{Return n}});
    s.
  Qed.

  Definition free : forall (r : t) (m : [Table n]), 
    STsep (m ~~ @rep n r m) (fun _:unit => __).
    intros; refine {{Free r}};
    s.
  Qed.

  Definition select : forall (r : t) (wh : WHERE n) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun res:Table n => m ~~ rep r m * [res = select wh m]).
    intros; refine (
      v <- !r;
      {{Return (select wh v)}}); 
    s.
  Qed.

  Definition update : forall (r : t) (up : UPDATE n) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun _:unit => m ~~ rep r (update up m)).
    intros; refine (
      v <- !r ; 
      r ::= update up v;;
      {{Return tt}});
    s.
  Qed.
    
  Definition insert : forall (r : t) (new_rows : Table n) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun _:unit => m ~~ rep r (m ++ new_rows)).
    intros; refine (
      v <- !r ; 
      r ::= v ++ new_rows;;
      {{Return tt}});
    s.
  Qed.

  Definition aggregate : forall (T : Type) (r : t) (agg : AGGREGATE n T) (v : T) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun res:T => m ~~ rep r m * [res = aggregate agg v m]).
    intros; refine (
      m <- !r ;
      {{ Return (aggregate agg v m) }});
    s.
  Qed.

  Definition serial := TableSerializer.serial.
  Definition deserial := TableSerializer.deserial.
  Definition serial_deserial := TableSerializer.serial_deserial.

  Definition serialize : forall (r : t) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun str:string => m ~~ rep r m * [str = serial m]).
    intros; refine (
      v <- !r ;
      {{Return (serial v)}}).
    unfold rep. instantiate (1 := (fun v => m ~~ [v = m])). sep fail auto.
    s.
    s.
    s.
  Qed.

  Definition deserialize : forall (r : t) (s : string),
    STsep (@rep n r nil)
          (fun m:option [Table n] =>
	      match m with 
	  	| None => @rep n r nil * [None = deserial n s]
		| Some m => m ~~ rep r m * [Some m = deserial n s]
              end).
    intros; refine (
      {{match deserial n s as d
          return STsep (r --> nil * [d = deserial n s])
                       (fun m:option [Table n] =>
	                 match m with 
	  	           | None => @rep n r nil * [None = deserial n s]
		           | Some m => m ~~ rep r m * [Some m = deserial n s]
                         end)
          with
          | None => {{Return None}}
          | Some m => r ::= m ;;
                      {{Return (Some [m]%inhabited)}}
        end}}); 
    solve [ do 2 (unfold Table in *; simpl in *; s) ].
  Qed.
End Size.

  Definition project : forall (n n' : nat) (r : t) (proj : PROJECT n n') (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun res:t * [Table n'] => m ~~ hprop_unpack (snd res) 
             (fun m' => rep r m * rep (fst res) m' * [m' = project proj m])).
    intros. refine (
      m <- !r ;
      let m' := project proj m in
      r' <- New m' ;
      {{ Return (r', inhabits m') }});
    try solve [ unfold t, rep; sep fail auto ].
    rsep fail auto. rewrite H1 in *. simpl in H2. rewrite <- (pack_injective H2).
    sep fail auto.
  Qed.

End RefStore.

Module ListStore : Store.
  Import StoreModel.

  Open Local Scope hprop_scope.
  Open Local Scope stsepi_scope.

  Definition t := ptr.

Section Parametric.
  Variable n : nat.
  Definition R := HeapLinkedListSeg (Tuple n).

  Definition llistR := @llist (Tuple n) R.
  Definition nil_empty := @nil_empty (Tuple n) R.
  Hint Unfold llistR.
  Hint Resolve nil_empty.
  Lemma empty_list : __ ==> llistR None nil.
    unfold llistR. unfold llist. sep fail auto.
  Qed.
  Hint Resolve empty_list.

  Definition rep (p : t) (m : Table n) := Exists d :@ LinkedList R, p --> d * llistR d m.

  Ltac s := unfold llistR, t, rep, llist; sep fail auto.

  Definition new : STsep (__) (fun r:t => rep r nil).
    refine (
      tbl <- empty R;
      n <- New tbl;
      {{ Return n }});
    s.
  Qed.
  
  Definition free : forall (r : t) (m : [Table n]), 
    STsep (m ~~ rep r m) (fun _:unit => __).
    refine (fun r m =>
      tbl <- !r;
      @freeList (Tuple n) R tbl None m <@> (r --> tbl);;
      {{Free r}}); 
    s.
  Qed.

  Definition select : forall (r : t) (wh : WHERE n) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun res:Table n => m ~~ rep r m * [res = select wh m]).
    refine (fun r wh m =>
      tbl <- !r;
      v <- @elements (Tuple n) R tbl None m <@> (r --> tbl);
      {{Return (select wh v)}});
    s.
  Qed.

  Definition updateDelegate (up : UPDATE n) (tpl : Tuple n) := 
    match up tpl with
      | None => Del (Tuple n)
      | Some tpl' => Update tpl'
    end.

  Theorem update_to_proc : forall (up : UPDATE n) (x : Table n),
    process_model x (updateDelegate up) = update up x.
    induction x;
      [ reflexivity
      | unfold updateDelegate, process_model, update in *; destruct (up a); rewrite IHx; trivial ].
  Qed.

  Definition update : forall (r : t) (up : UPDATE n) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun _:unit => m ~~ rep r (update up m)).
    refine (fun r up m =>
      tbl <- !r ; 
      tbl' <- process tbl None (updateDelegate up) m <@> (r --> tbl);
      r ::= tbl' ;;
      {{Return tt}});
    solve [ s; rewrite update_to_proc; s ].
  Qed.
  
  Definition to_heap : forall (r : Table n),
    STsep (__)
          (fun res:LinkedList R => llistR res r).
    refine (fun r =>
      Fix (fun _ => __)
          (fun r res => llistR res r)
          (fun self r =>
            match r as r 
              return STsep (__) (fun res => llistR res r)
              with
              | nil => {{empty R}}
              | a :: b => 
                res' <- self b;
                {{@cons (Tuple n) R a res' [None] [b]}}
            end)
          r);
    solve [ s ].
  Qed.

  Definition insert : forall (r : t) (new_rows : Table n) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun _:unit => m ~~ rep r (m ++ new_rows)).
    unfold Table; refine (fun r new_rows m =>
      tbl <- !r ; 
      new_rows' <- to_heap new_rows <@> _ ;
      tbl' <- @append (Tuple n) R tbl new_rows' m [new_rows] <@> (r --> tbl);
      r ::= tbl' ;;
      {{Return tt}});
    solve [ s ].
  Qed.

  Lemma foldr_aggregate : forall T x v agg,
    foldr_model (fun (a : Tuple n) (b : T) => agg b a) x v = aggregate agg v x.
    induction x. reflexivity. intros. simpl. rewrite IHx; auto.
  Qed.

  Definition aggregate : forall (T : Type) (r : t) (agg : AGGREGATE n T) (v : T) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun res:T => m ~~ rep r m * [res = aggregate agg v m]).
    Hint Resolve foldr_aggregate.
    refine (fun T r agg v m =>
      tbl <- !r ;
      res <- foldr_f tbl None (fun a b => agg b a) m v <@> (r --> tbl) ;
      {{ Return res }});
    s.   
  Qed.

  Definition serial := TableSerializer.serial.
  Definition deserial := TableSerializer.deserial.
  Definition serial_deserial := TableSerializer.serial_deserial.

  Lemma ser_impl : forall (ls : Table n) data, 
    data = foldr_model (fun a s => (TableSerializer.st n a ++ fst s, S (snd s))%string) ls (EmptyString, 0)
    -> snd data = List.length ls /\ fst data = TableSerializer.serial' ls.
    split; generalize dependent data;
    (induction ls;
      [ intros; destruct data; simpl in *; inversion H; firstorder
      | intros; simpl in H; 
        rewrite (IHls (foldr_model
          (fun (a : Tuple n) (s : string * nat) =>
            ((TableSerializer.st n a ++ fst s)%string, S (snd s))) 
          ls (""%string, 0)) (refl_equal _)) in H; destruct data; inversion H; reflexivity ]).
  Qed.    

  Definition serialize : forall (r : t) (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun str:string => m ~~ rep r m * [str = serial m]).
    refine (fun r m =>
      v <- !r;
      data <- foldr_f v None (fun a s => (TableSerializer.st n a ++ fst s, 1 + snd s)%string) m (EmptyString,0) <@> _ ;
      {{Return (TableSerializer.toString (snd data) ++ ":" ++ fst data)%string}});
    s. 
    match goal with 
      | [ x : Table n, H : (?X,?Y) = _ |- _ ] => 
        let H' := fresh "H" in
        pose (H' := ser_impl x H); inversion H'; simpl in *
    end. subst. unfold serial. unfold TableSerializer.serial. s.
  Qed.

  Definition deserialize : forall (r : t) (s : string),
    STsep (rep r nil)
          (fun m:option [Table n] =>
	      match m with 
	  	| None => rep r nil * [None = deserial n s]
		| Some m => m ~~ rep r m * [Some m = deserial n s]
              end).
    refine (fun r s =>
      {{match deserial n s as d
          return STsep (rep r nil * [d = deserial n s])
                       (fun m:option [Table n] =>
	                 match m with 
	  	           | None => rep r nil * [None = deserial n s]
		           | Some m => m ~~ rep r m * [Some m = deserial n s]
                         end)
          with
          | None => {{Return None}}
          | Some m => hp <- to_heap m <@> _ ;
                      r ::= hp ;;
                      {{Return (Some [m]%inhabited)}}
        end}});
    solve [ do 2 (unfold Table in *; simpl in *; s)
          | s; seprw (@nil_empty (Tuple n) v0 None); s ].
  Qed.

End Parametric.

  Ltac s := unfold t, rep, llist; sep fail auto.

  Definition project : forall (n n' : nat) (r : t) (proj : PROJECT n n') (m : [Table n]),
    STsep (m ~~ rep r m)
          (fun res:t * [Table n'] => m ~~ hprop_unpack (snd res) 
             (fun m' => rep r m * rep (fst res) m' * [m' = project proj m])).
    refine (fun n n' r proj m =>
      let R' := HeapLinkedListSeg (Tuple n') in
      acc <- empty R' <@> _ ;
      tbl <- !r ;
      tbl' <- foldr tbl None 
              (fun rr c => @llseg (Tuple n') R' rr None (project proj c))
              (fun rr v m => 
                res <- @cons (Tuple n' ) R' (proj v) rr (inhabits None) (m ~~~ project proj m) ;
                {{ Return res }})
              m acc <@> (r --> tbl) ;
      res <- New tbl' ;
      {{ Return (res, (m ~~~ project proj m)) }}             
    );
    solve [ s ].
  Qed.

End ListStore.

Require Export LinkedListSeg.
