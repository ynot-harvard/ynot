Require Import Ynot.Axioms.
Require Import Ynot.Util.
Require Import Ynot.Heap.
Require Import Ynot.Hprop.

Set Implicit Arguments.


Theorem himp_refl : forall p, p ==> p.
  unfold hprop_imp; trivial.
Qed.

Theorem himp_any_conc : forall p, p ==> ??.
  unfold hprop_imp, hprop_any; trivial.
Qed.

Theorem himp_empty_prem : forall p q,
  p ==> q
  -> __ * p ==> q.
  unfold hprop_imp, hprop_empty, hprop_sep; firstorder; subst; autorewrite with Ynot; auto.
Qed.

Theorem himp_empty_prem' : forall p q,
  p * __ ==> q
  -> p ==> q.
  unfold hprop_imp, hprop_empty, hprop_sep; firstorder; subst; autorewrite with Ynot; auto.
  apply H.
  eauto with Ynot.
Qed.

Theorem himp_empty_conc : forall p q,
  p ==> q
  -> p ==> __ * q.
  unfold hprop_imp, hprop_empty, hprop_sep; firstorder; subst; autorewrite with Ynot;
    eauto 6 with Ynot.
Qed.

Theorem himp_empty_conc' : forall p q,
  p ==> q * __
  -> p ==> q.
  unfold hprop_imp, hprop_empty, hprop_sep; intuition.
  generalize (H _ H0); clear H H0; firstorder; subst; autorewrite with Ynot; trivial.
Qed.

Theorem himp_comm_prem : forall p q r,
  q * p ==> r
  -> p * q ==> r.
  unfold hprop_imp, hprop_sep; intuition.
  apply H.
  do 2 destruct H0; intuition.
  exists x0; exists x; intuition.
  apply split_comm; assumption.
Qed.

Theorem himp_assoc_prem1 : forall p q r s,
  p * (q * r) ==> s
  -> (p * q) * r ==> s.
  unfold hprop_imp, hprop_sep; intuition.
  apply H; clear H.
  destruct H0.
  destruct H; intuition.
  do 2 destruct H; intuition.
  exists x1; exists (x2 * x0)%heap; intuition.
  eapply split_splice'; eauto.
  exists x2; exists x0; intuition.
  eapply split_self; eauto.
Qed.

Theorem himp_assoc_prem2 : forall p q r s,
  q * (p * r) ==> s
  -> (p * q) * r ==> s.
  unfold hprop_imp, hprop_sep; intuition.
  apply H; clear H.
  destruct H0.
  destruct H; intuition.
  do 2 destruct H; intuition.
  exists x2; exists (x1 * x0)%heap; intuition.
  eapply split_splice'; eauto.
  apply split_comm; assumption.
  exists x1; exists x0; intuition.
  eapply split_self; eauto.
  apply split_comm; eassumption.
Qed.

Theorem himp_comm_conc : forall p q r,
  r ==> q * p
  -> r ==> p * q.
  unfold hprop_imp, hprop_sep; intuition.
  generalize (H _ H0); clear H H0; intuition.
  do 2 destruct H; intuition.
  exists x0; exists x; intuition.
  apply split_comm; assumption.
Qed.

Theorem himp_assoc_conc1 : forall p q r s,
  s ==> p * (q * r)
  -> s ==> (p * q) * r.
  unfold hprop_imp, hprop_sep; intuition.
  generalize (H _ H0); clear H H0; intuition.
  do 2 destruct H; intuition.
  destruct H2.
  destruct H1; intuition.
  exists (x * x1)%heap; exists x2; intuition.
  eapply split_splice''; eauto.
  exists x; exists x1; intuition.
  eapply split_self'; eauto.
Qed.

Theorem himp_assoc_conc2 : forall p q r s,
  s ==> q * (p * r)
  -> s ==> (p * q) * r.
  unfold hprop_imp, hprop_sep; intuition.
  generalize (H _ H0); clear H H0; intuition.
  do 2 destruct H; intuition.
  destruct H2.
  destruct H1; intuition.
  exists (x1 * x)%heap; exists x2; intuition.
  eapply split_splice'''; eauto.
  exists x1; exists x; intuition.
  eapply split_self''; eauto.
Qed.

Definition isExistential T (x : T) := True.

Lemma isExistential_any : forall T (x : T), isExistential x.
  constructor.
Qed.

Theorem himp_ex_prem : forall T (p1 : T -> _) p2 p,
  (forall v, isExistential v -> p1 v * p2 ==> p)
  -> hprop_ex p1 * p2 ==> p.
  Hint Immediate isExistential_any.

  unfold hprop_imp, hprop_ex, hprop_sep; simpl; intuition.
  do 2 destruct H0; intuition.
  destruct H0.
  eauto 6.
Qed.

Theorem himp_ex_conc : forall p T (p1 : T -> _) p2,
  (exists v, p ==> p1 v * p2)
  -> p ==> hprop_ex p1 * p2.
  unfold hprop_imp, hprop_ex, hprop_sep; firstorder.
  generalize (H _ H0); clear H H0.
  firstorder.
Qed.

Theorem himp_ex_conc_trivial : forall T p p1 p2,
  p ==> p1 * p2
  -> T
  -> p ==> hprop_ex (fun _ : T => p1) * p2.
  unfold hprop_imp, hprop_ex, hprop_sep; firstorder.
  generalize (H _ H0); clear H H0.
  firstorder.
Qed.

Theorem himp_unpack_prem : forall T (x : T) p1 p2 p,
  p1 x * p2 ==> p
  -> hprop_unpack [x] p1 * p2 ==> p.
  unfold hprop_imp, hprop_unpack, hprop_sep; firstorder.
  generalize (pack_injective H1); intro; subst; firstorder.
Qed.

Theorem himp_unpack_conc : forall T (x : T) p1 p2 p,
  p ==> p1 x * p2
  -> p ==> hprop_unpack [x] p1 * p2.
  unfold hprop_imp, hprop_unpack, hprop_sep; firstorder.
  generalize (H _ H0).
  firstorder.
Qed.

Theorem himp_split : forall p1 p2 q1 q2,
  p1 ==> q1
  -> p2 ==> q2
  -> p1 * p2 ==> q1 * q2.
  unfold hprop_imp, hprop_sep; firstorder.
Qed.

Theorem himp_inj_prem : forall (P : Prop) p q,
  (P -> p ==> q)
  -> [P] * p ==> q.
  unfold hprop_imp, hprop_inj, hprop_sep; firstorder.
  subst.
  autorewrite with Ynot.
  eauto.
Qed.

Theorem himp_inj_conc : forall (P : Prop) p q,
  P
  -> p ==> q
  -> p ==> [P] * q.
  unfold hprop_imp, hprop_inj, hprop_sep; firstorder.
  exists empty; exists h; intuition.
Qed.

Theorem himp_frame : forall p q1 q2,
  q1 ==> q2
  -> p * q1 ==> p * q2.
  intros.
  apply himp_split; [apply himp_refl | assumption].
Qed.

Theorem himp_frame_cell : forall n T (v1 v2 : T) q1 q2,
  v1 = v2
  -> q1 ==> q2
  -> n --> v1 * q1 ==> n --> v2 * q2.
  intros; subst.
  apply himp_frame; assumption.
Qed.

Ltac search_prem tac :=
  let rec search p :=
    tac
    || (apply himp_empty_prem'; tac)
    || match p with
         | (?p1 * ?p2)%hprop =>
           (apply himp_assoc_prem1; search p1)
           || (apply himp_assoc_prem2; search p2)
       end
    in match goal with
         | [ |- ?p * _ ==> _ ] => search p
         | [ |- _ * ?p ==> _ ] => apply himp_comm_prem; search p
         | [ |- _ ==> _ ] => progress (tac || (apply himp_empty_prem'; tac))
       end.

Ltac search_conc tac :=
  let rec search p :=
    tac
    || (apply himp_empty_conc'; tac)
    || match p with
         | (?p1 * ?p2)%hprop =>
           (apply himp_assoc_conc1; search p1)
           || (apply himp_assoc_conc2; search p2)
       end
    in match goal with
         | [ |- _ ==> ?p * _ ] => search p
         | [ |- _ ==> _ * ?p ] => apply himp_comm_conc; search p
         | [ |- _ ==> _ ] => progress (tac || (apply himp_empty_conc'; tac))
       end.

Ltac finisher := apply himp_refl
  || apply himp_any_conc.

Ltac premer := apply himp_empty_prem
  || (apply himp_ex_prem; do 2 intro)
    || (apply himp_inj_prem; intro)
      || apply himp_unpack_prem.

Ltac simpler := repeat progress (intuition; subst; simpl in * ).

Ltac deExist P :=
  let F := fresh "F" in
    pose (F := P);
      repeat match goal with
               | [ _ : isExistential ?X |- _ ] =>
                 let y := eval cbv delta [F] in F in
                   match y with
                     | context[X] =>
                       pattern X in F;
                         let y := eval cbv delta [F] in F in
                           match y with
                             | ?F' _ => pose (F2 := hprop_ex F'); clear F; rename F2 into F
                           end
                   end
             end;
      let y := eval cbv delta [F] in F in
        clear F; y.

Ltac equater :=
  match goal with
    | [ |- ?p ==> ?q ] => equate p q || let q := deExist q in equate p q
    | [ |- ?p ==> (?q * __)%hprop ] => equate p q || let q := deExist q in equate p q
    | [ |- (?p * __)%hprop ==> ?q ] => equate p q || let q := deExist q in equate p q
    | [ |- ?U ?X ==> ?p ] =>
      let H := fresh in
        (pose (H := p); pattern X in H;
          assert (H' : H = H); [
            cbv delta [H]; match goal with
                             | [ |- ?F _ = _ ] => equate U F
                           end; reflexivity
            | idtac
          ]; clear H H')
    | [ |- ?p ==> ?U ?X ] =>
      let H := fresh in
        (pose (H := p); pattern X in H;
          assert (H' : H = H); [
            cbv delta [H]; match goal with
                             | [ |- ?F _ = _ ] => equate U F
                           end; reflexivity
            | idtac
          ]; clear H H')
  end.

Theorem unpack : forall T (h : [T]) (P : Prop),
  (forall x, h = [x]%inhabited -> P)
  -> P.
  dependent inversion h; eauto.
Qed.

Theorem himp_unpack_prem_eq : forall T h (x : T) p1 p2 p,
  h = [x]%inhabited
  -> p1 x * p2 ==> p
  -> hprop_unpack h p1 * p2 ==> p.
  intros; subst.
  apply himp_unpack_prem; assumption.
Qed.

Theorem himp_unpack_prem_alone : forall T h (x : T) p1 p,
  h = [x]%inhabited
  -> p1 x ==> p
  -> hprop_unpack h p1 ==> p.
  intros.
  apply himp_empty_prem'.
  rewrite H.
  apply himp_unpack_prem.
  apply himp_comm_prem.
  apply himp_empty_prem.
  assumption.
Qed.

Ltac findContents ptr P :=
  match P with
    | (ptr --> ?V)%hprop => constr:(V, __)%hprop
    | (?P1 * ?P2)%hprop =>
      match findContents ptr P1 with
        | (?V, ?P1) => constr:(V, P1 * P2)%hprop
        | _ =>
          match findContents ptr P2 with
            | (?V, ?P2) => constr:(V, P1 * P2)%hprop
          end
      end
    | _ => tt
  end.

Ltac inhabiter :=
  repeat match goal with
           | [ x : [_] |- _ ] =>
             match goal with
               | [ _ : x = [_]%inhabited |- _ ] => fail 1
               | _ => apply (unpack (h := x)); do 2 intro
             end
         end;

  repeat search_prem ltac:((eapply himp_unpack_prem_eq; [eassumption |])
    || (apply himp_ex_prem; do 2 intro)).

Ltac specFinder :=
  inhabiter;
    
  try match goal with
        | [ |- ?P ==> Exists v :@ ?T, (?ptr --> v * ?Q v)%hprop ] =>
          match findContents ptr P with
            | (?V, ?P) =>
              apply himp_empty_conc';
                apply himp_ex_conc; exists V;
                  let Px := fresh "P" in
                    pose (Px := P);
                      pattern V in Px;
                        let x := eval cbv delta [Px] in Px in
                          clear Px;
                            match x with
                              | ?F' _ =>
                                let F := fresh "F" with F2 := fresh "F2" in
                                  pose (F := (fun x => [x = V] * F' x)%hprop);
                                    repeat match goal with
                                             | [ H : ?x = [?v]%inhabited |- _ ] =>
                                               let y := eval cbv delta [F] in F in
                                                 match y with
                                                 | context[v] =>
                                                   pattern v in F;
                                                     let y := eval cbv delta [F] in F in
                                                       match y with
                                                         | ?F' _ =>
                                                           pose (F2 := fun y => hprop_unpack x (fun x => F' x y));
                                                             unfold F in F2; clear F; rename F2 into F
                                                       end
                                               end
                                           end;
                                    repeat match goal with
                                             | [ _ : isExistential ?X |- _ ] =>
                                               let y := eval cbv delta [F] in F in
                                                 match y with
                                                   | context[X] =>
                                                     pattern X in F;
                                                       let y := eval cbv delta [F] in F in
                                                         match y with
                                                           | ?F' _ =>
                                                             pose (F2 := fun y => hprop_ex (fun x => F' x y));
                                                             clear F; rename F2 into F
                                                         end
                                                 end
                                           end;
                                    try (let y := eval cbv delta [F] in F in
                                      match y with
                                        | context[V] =>
                                          pattern V in F;
                                            let y := eval cbv delta [F] in F in
                                              match y with
                                                | ?F' _ => pose (F2 := fun x => F' x x);
                                                  clear F; rename F2 into F; simpl in F
                                              end
                                      end);
                                    let y := eval cbv delta [F] in F in
                                      clear F;
                                        equate Q y
                            end
          end

        | [ |- ?P ==> ?Q * Exists v :@ _, (?ptr --> v)%hprop ] =>
          match findContents ptr P with
            | (?V, ?P) =>
              let F := fresh "F" with F2 := fresh "F2" in
                pose (F := P);
                  repeat match goal with
                           | [ H : ?x = [?v]%inhabited |- _ ] =>
                             let y := eval cbv delta [F] in F in
                               match y with
                                 | context[v] =>
                                   pattern v in F;
                                     let y := eval cbv delta [F] in F in
                                       match y with
                                         | ?F' _ =>
                                           pose (F2 := hprop_unpack x F');
                                             clear F; rename F2 into F
                                       end
                               end
                         end;
                  repeat match goal with
                           | [ _ : isExistential ?X |- _ ] =>
                             let y := eval cbv delta [F] in F in
                               match y with
                                 | context[X] =>
                                   pattern X in F;
                                     let y := eval cbv delta [F] in F in
                                       match y with
                                         | ?F' _ => pose (F2 := hprop_ex F'); clear F; rename F2 into F
                                       end
                               end
                         end;
                  let y := eval cbv delta [F] in F in
                    clear F;
                      equate Q y
          end
      end.

Ltac unfold_local :=
  repeat match goal with
           | [ x : _ |- _ ] => unfold x in *; clear x
         end.

Open Local Scope hprop_scope.

Ltac focus x :=
  let F := fresh "F" with F2 := fresh "F2" in
    match goal with
      | [ |- ?P ==> ?Q ] =>
        pose (F := P);
          repeat match goal with
                   | [ H : ?V = [?f ?T ?arg1 ?arg2]%inhabited |- _ ] =>
                     match type of T with
                       | Set =>
                         let doit :=
                           pattern arg1, arg2 in F;
                             let y := eval cbv delta [F] in F in
                               match y with
                                 | ?F' _ _ =>
                                   pose (F2 := V ~~ Exists arg1 :@ _, Exists arg2 :@ _,
                                     [V = f T arg1 arg2] * F' arg1 arg2);
                                   clear F; rename F2 into F
                               end in

                               let y := eval cbv delta [F] in F in
                                 match y with
                                   | context[arg1] => doit
                                   | context[arg2] => doit
                                 end
                     end
                 end;
          repeat match goal with
                   | [ H : isExistential ?v |- _ ] =>
                     let y := eval cbv delta [F] in F in
                       match y with
                         | context[v] =>
                           pattern v in F;
                             let y := eval cbv delta [F] in F in
                               match y with
                                 | ?F' _ =>
                                   pose (F2 := Exists v :@ _, F' v)
                               end;
                               clear F; rename F2 into F
                       end
                 end;
          let y := eval cbv delta [F] in F in
            equate Q y
    end.

Ltac sep tac :=
  let s := repeat progress (simpler; tac; try search_prem premer) in
    let concer := apply himp_empty_conc
      || apply himp_ex_conc_trivial
        || (apply himp_ex_conc; econstructor)
          || apply himp_unpack_conc
            || (apply himp_inj_conc; [s; fail | idtac]) in
              (intros; equater || specFinder; tac;
                repeat match goal with
                         | [ x : inhabited _ |- _ ] => dependent inversion x; clear x
                       end;
                intros; s;
                  repeat ((search_conc concer
                    || search_prem ltac:(idtac;
                      search_conc ltac:(apply himp_frame || (apply himp_frame_cell; trivial))));
                  s);
                  try finisher).

