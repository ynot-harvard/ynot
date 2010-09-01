Require Import Qcanon.
Require Import Ynot.Axioms.
Require Import Ynot.Util.
Require Import Ynot.PermModel.
Require Import Ynot.Heap.
Require Import Ynot.Hprop.
Require Import Ynot.Separation.

Set Implicit Arguments.

Ltac search_prem tac :=
  let rec search p :=
    let p := eval simpl in p in
      tac
      || (apply himp_empty_prem'; tac)
        || match p with
             | (?p1 * ?p2)%hprop =>
               (apply himp_assoc_prem1; search p1)
               || (apply himp_assoc_prem2; search p2)
           end
    in cbv beta;
    match goal with
      | [ |- ?p * _ ==> _ ] => search p
      | [ |- _ * ?p ==> _ ] => apply himp_comm_prem; search p
      | [ |- _ ] => progress (tac || (apply himp_empty_prem'; tac))
    end.
    (*in match goal with
         | [ |- ?p * _ ==> _ ] => search p
         | [ |- _ * ?p ==> _ ] => apply himp_comm_prem; search p
         | [ |- ?p ] =>
           let p := eval simpl in p in
           match p with
             | ?p' * _ => search p'
             | _ * ?p' => apply himp_comm_prem; search p
             | _ => progress (tac || (apply himp_empty_prem'; tac))
           end
       end.*)
    (*in match goal with
         | [ |- ?p ==> _ ] =>
           let p := (*eval cbv beta in*) p in
             match p with
               | ?p * _ => search p
               | _ * ?p => apply himp_comm_prem; search p
               | _ => progress (tac || (apply himp_empty_prem'; tac))
             end
       end.*)

Ltac search_conc tac :=
  let rec search p :=
    let p := eval simpl in p in
      tac
      || (apply himp_empty_conc'; tac)
        || match p with
             | (?p1 * ?p2)%hprop =>
               (apply himp_assoc_conc1; search p1)
               || (apply himp_assoc_conc2; search p2)
           end
    in cbv beta;
    match goal with
         | [ |- _ ==> ?p * _ ] => search p
         | [ |- _ ==> _ * ?p ] => apply himp_comm_conc; search p
         | [ |- _ ] => progress (tac || (apply himp_empty_conc'; tac))
      end.
    (*in match goal with
         | [ |- _ ==> ?p ] =>
           let p := (*eval cbv beta in*) p in
             match p with
               | ?p * _ => search p
               | _ * ?p => apply himp_comm_conc; search p
               | _ => progress (tac || (apply himp_empty_conc'; tac))
             end
       end.*)


Ltac simpl_prem t := search_prem ltac:(
  match goal with [ |- (_ * _) ==> _ ] => eapply himp_frame_prem end; [ t | ]).

Ltac simpl_conc t := search_conc ltac:(match goal with [|- _ ==> _ * _] => eapply himp_frame_conc end; [ t | ]).

Ltac simpl_cancel t := search_prem ltac:(search_conc ltac:(
  match goal with [|- _ * _ ==> _ * _] => apply himp_split end; [ t | ])).

Ltac finisher := apply himp_refl.
(*  || apply himp_any_conc. *)

Ltac premer := idtac;
  match goal with
    | [ |- __ * _ ==> _ ] => apply himp_empty_prem
    | [ |- hprop_ex _ * _ ==> _ ] => apply himp_ex_prem; do 2 intro
    | [ |- [_] * _ ==> _ ] => apply himp_inj_prem; intro
    | [ |- hprop_unpack [_]%inhabited _ * _ ==> _ ] => apply himp_unpack_prem
  end.

Ltac subst_inh := repeat
  match goal with
    | [H:[_]%inhabited = [_]%inhabited |- _] => generalize (pack_injective H); clear H; intro H
    | [H1:?x = [?y1]%inhabited, H2:?x = [?y2]%inhabited |- _]
      => match y1 with
           | y2 => fail 1
           | _ => rewrite H1 in H2
         end
  end.

Ltac simpler :=
  repeat progress (intuition auto with bool arith datatypes Ynot; subst_inh; subst; simpl in *).

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

Ltac findContents ptr P :=
  let P := eval simpl in P in
  match P with
    | (ptr -[ ?q ]-> ?V)%hprop => constr:(V, __)%hprop
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

Ltac unpack_conc := repeat search_conc ltac:(idtac;
  match goal with
    | [ |- _ ==> hprop_unpack ?M _ * _ ] =>
      match M with
        | M => eapply himp_unpack_conc; [eassumption || reflexivity | ]
        | _ => match M with 
                 | M => fail 2
                 | _ => eapply himp_unpack_conc_meta
               end
      end
  end).

Ltac inhabiter :=
  repeat match goal with
           | [ x : [_] |- _ ] =>
             match goal with
               | [ _ : x = [_]%inhabited |- _ ] => fail 1
               | _ => apply (unpack (h := x)); do 2 intro
             end
           | [|- context [hprop_unpack ?x _]] =>
             meta_fail x;
             match goal with
               | [ _ : x = [_]%inhabited |- _ ] => fail 1
               | _ => apply (unpack (h := x)); do 2 intro
             end
         end;

  repeat search_prem ltac:(
    (match goal with [|- hprop_unpack _ _ * _ ==> _] => eapply himp_unpack_prem_eq ; [eassumption |] end) ||
      (match goal with [|- hprop_ex _ * _ ==> _] => apply himp_ex_prem; do 2 intro end)).

Ltac canceler :=
  cbv zeta;
  repeat search_conc ltac:(idtac; (** Eliminate the empty heaps on the RHS **)
    match goal with
      [ |- _ ==> __ * _ ] => apply himp_empty_conc
    end);
  repeat search_prem ltac:(idtac;
    apply himp_empty_prem || (** Eliminate empty heaps on LHS **)
    search_conc ltac:(idtac; 
      (** Eliminate common heaps. The match prevents capturing existentials **)
      match goal with
        | [ |- ?p * _ ==> ?p * _ ] => apply himp_frame
          (* beef this up to handle different fractions? *)
        | [ |- ?p -[ ?q ]-> _ * _ ==> ?p -[ ?q ]-> _ * _ ] => apply himp_frame_cell; trivial
      end)). 

Ltac specFinder stac :=
  inhabiter; try (stac; inhabiter);
    
  try match goal with
        | [ |- ?P ==> Exists v :@ ?T, (hprop_unpack _ (fun _ => ?ptr -[ _ ]-> v * ?Q v))%hprop ] =>
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
        | [ |- ?P ==> Exists v :@ ?T, (?ptr -[ _ ]-> v * ?Q v)%hprop ] =>
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

        | [ |- ?P ==> ?Q * Exists v :@ _, (hprop_unpack _ (fun _ => ?ptr -[ _ ]-> v))%hprop ] =>
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

        | [ |- ?P ==> ?Q * Exists v :@ _, (?ptr -[ _ ]-> v)%hprop ] =>
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

        | [ |- ?P ==> ?Q ] =>
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
      end.

Ltac unfold_local :=
  repeat match goal with
           | [ x : _ |- _ ] => unfold x in *; clear x
         end.

Ltac sep stac tac :=
  let s := repeat progress (simpler; tac; try search_prem premer) in
  let concer := idtac;
    match goal with
      | [ |- _ ==> __ * _ ] => apply himp_empty_conc
      | [ |- _ ==> hprop_ex _ * _ ] => apply himp_ex_conc_trivial
        || (apply himp_ex_conc; econstructor)
      | [ |- _ ==> hprop_unpack _ _ * _ ] =>
        eapply himp_unpack_conc; [eassumption || reflexivity |]
      | [ |- _ ==> [_] * _ ] => apply himp_inj_conc; [s; fail | ]
    end
    in
  (intros; equater || specFinder stac; tac;
   repeat match goal with
            | [ x : inhabited _ |- _ ] => dependent inversion x; clear x
          end;
   intros; s; tac;
     repeat ((
       search_prem ltac:(idtac;
         search_conc ltac:(idtac;
           match goal with
             | [ |- ?p * _ ==> ?p * _ ] => apply himp_frame
             | [ |- ?p -[ ?q ]-> _ * _ ==> ?p -[ ?q ]-> _ * _ ] => apply himp_frame_cell; trivial
           end)) || search_conc concer
       || search_prem ltac:(idtac;
         search_conc ltac:(idtac;
           match goal with
             | [ |- _ * _ ==> _ * _ ] => apply himp_frame
             | [ |- _ -[ ?q ]-> _ * _ ==> _ -[ ?q ]-> _ * _ ] =>
               apply himp_frame_cell; trivial
           end)));
     s);
     try finisher).

Ltac intro_pure :=
  repeat search_prem ltac:(idtac;
    match goal with
      | [ |- [?P] * _ ==> _ ] =>
        match goal with
          | [ H : P |- _ ] => fail 1
          | _ => apply himp_inj_prem_keep; intro
        end
    end).

Ltac unintro_pure :=
  repeat match goal with
           | [ |- context[[?P]%hprop] ] =>
             match goal with
               | [ H : P |- _ ] => clear H
             end
         end.

Ltac sep_change2 F :=
  match goal with
    | [ |- context[F ?X1 ?Y1] ] =>
      match goal with
        | [ |- context[F ?X2 ?Y2] ] =>
          match constr:(X1, Y1) with
            | (X2, Y2) => fail 1
            | _ =>
              intro_pure;
              let H' := fresh "H" in
                assert (H' : X1 = X2 \/ Y1 = Y2); [ tauto | ];
                  clear H';
                    replace (F X1 Y1) with (F X2 Y2); [
                      | subst; simpl in *;
                        repeat match goal with
                                 | [ H : [_]%inhabited = [_]%inhabited |- _ ] =>
                                   generalize (pack_injective H); clear H
                               end;
                        congruence ]
          end
      end
  end.

Lemma himp_prop_imp : forall (P Q : Prop) H, 
  (P -> Q)
  -> H * [P] ==> H * [Q].
  sep fail auto.
Qed.

Lemma himp_prop_conc : forall (P : Prop) H1 H2,
  P -> (H1 ==> H2) -> (H1 ==> [P] * H2).
  sep fail auto.
Qed.

Theorem himp_disjoint' : forall  h (S T : Set) p (a1:S) (a2:T), 
  (p -[0]-> a1 * p -[0]-> a2)%hprop h -> False.
  intros; unfold hprop_imp; intros. 
  repeat (destruct H). 
  intuition. red in H2, H3. intuition.
  generalize (H p).
  rewrite H0, H2. intuition.
Qed.

Theorem himp_disjoint : forall (S T : Set) p1 p2 (a1:S) (a2:T), 
  p1 -[0]-> a1 * p2 -[0]-> a2 ==> p1 -[0]-> a1 * p2 -[0]-> a2 * [p1 <> p2].
  intros. unfold hprop_imp. intros; repeat (destruct H). destruct H0.
  exists ((x * x0)%heap). exists empty. subst. sep fail auto.
  exists x. exists x0. sep fail auto.
  compute; intuition. subst.
  eapply himp_disjoint'.
  exists x. exists x0. intuition; eauto.
Qed.

Theorem himp_split_any : ?? * ?? ==> ??.
  unfold hprop_any, hprop_imp; trivial.
Qed.

(* useful tactics for debugging sep *)
Ltac print_goal := idtac;
  match goal with
    | [|- ?H] => idtac H; idtac ""
  end.

Ltac print_all := idtac;
  match goal with
    | [H: ?X |- _] => idtac H ":" X; fail 0
    | [|- ?H] => idtac "============================"; idtac H
      ; idtac ""; idtac "-----------------------------------------"; idtac ""
  end.
