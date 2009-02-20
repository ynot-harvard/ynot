(* Copyright (c) 2008, Harvard University
 * All rights reserved.
 *
 * Authors: Adam Chlipala, Gregory Malecha
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

Ltac mark_existential e := generalize (isExistential_any e); intro.

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

Theorem himp_unpack_conc : forall T x (y:[T]) p1 p2 p,
  y = [x]%inhabited
  -> p ==> p1 x * p2
  -> p ==> hprop_unpack y p1 * p2.
  unfold hprop_imp, hprop_unpack, hprop_sep; subst; firstorder.
  generalize (H0 _ H1).
  firstorder.
Qed.

Theorem himp_unpack_conc_meta : forall T x (y:[T]) p1 p2 p,
  p ==> p1 x * p2
  -> y = [x]%inhabited
  -> p ==> hprop_unpack y p1 * p2.
  unfold hprop_imp, hprop_unpack, hprop_sep; subst; firstorder.
  generalize (H _ H1).
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

Theorem himp_inj_prem_keep : forall (P : Prop) p q,
  (P -> [P] * p ==> q)
  -> [P] * p ==> q.
  unfold hprop_imp, hprop_inj, hprop_sep; firstorder.
Qed.

Theorem himp_inj_prem_add : forall (P : Prop) p q,
  P
  -> [P] * p ==> q
  -> p ==> q.
  unfold hprop_imp, hprop_inj, hprop_sep; firstorder.
  apply H0.
  exists empty.
  exists h.
  intuition.
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

Lemma himp_trans Q P R : P ==> Q -> Q ==> R -> P ==> R.
Proof. firstorder. Qed.

Lemma himp_apply P T : P ==> T -> forall Q, Q ==> P -> Q ==> T.
Proof. repeat intro; auto. Qed.

Theorem add_fact F P Q R : 
  (P ==> [F] * ??) ->
  (F -> (P * Q ==> R)) ->
  (P * Q ==> R).
Proof.
  repeat intro. apply H0; auto. 
  destruct H1 as [? [? [? [Px ?]]]].
  destruct (H _ Px) as [? [? [? [[? ?] ?]]]]; trivial.
Qed.

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

Theorem himp_frame_prem : forall p1 p2 q p1',
  p1 ==> p1'
  -> p1' * p2 ==> q
  -> p1 * p2 ==> q.
  unfold hprop_imp, hprop_sep; firstorder.
Qed.

Ltac simpl_prem t := search_prem ltac:(eapply himp_frame_prem; [ t | ]).

Theorem himp_frame_conc : forall p q1 q2 q1',
  q1' ==> q1
  -> p ==> q1' * q2
  -> p ==> q1 * q2.
  unfold hprop_imp, hprop_sep; firstorder.
Qed.

Ltac simpl_conc t := search_conc ltac:(eapply himp_frame_conc; [ t | ]).

Ltac simpl_cancel t := search_prem ltac:(search_conc ltac:(apply himp_split; [ t | ])).

Ltac finisher := apply himp_refl
  || apply himp_any_conc.

Ltac premer := apply himp_empty_prem
  || (apply himp_ex_prem; do 2 intro)
    || (apply himp_inj_prem; intro)
      || apply himp_unpack_prem.

Ltac subst_inh := repeat
  match goal with
    | [H:[_]%inhabited = [_]%inhabited |- _] => generalize (pack_injective H); clear H; intro H
    | [H1:?x = [?y1]%inhabited, H2:?x = [?y2]%inhabited |- _]
      => match y1 with
           | y2 => fail 1
           | _ => rewrite H1 in H2
         end
  end.

Ltac simpler := repeat progress (intuition; subst_inh; subst; simpl in * ).

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
  let P := eval simpl in P in
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


Ltac meta_fail x :=
  match x with
    | x => idtac
    | _ => fail 1
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

  repeat search_prem ltac:(eapply himp_unpack_prem_eq; [eassumption |]
    || (apply himp_ex_prem; do 2 intro)).

Ltac canceler :=
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
        | [ |- ?p --> _ * _ ==> ?p --> _ * _ ] => apply himp_frame_cell; trivial
      end)). 

Ltac specFinder stac :=
  inhabiter; try (stac; inhabiter);
    
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
  let concer := apply himp_empty_conc
      || apply himp_ex_conc_trivial
      || (apply himp_ex_conc; econstructor)
      || (eapply himp_unpack_conc; [eassumption || reflexivity |])
      || (apply himp_inj_conc; [s; fail | idtac])
  in
  (intros; equater || specFinder stac; tac;
   repeat match goal with
            | [ x : inhabited _ |- _ ] => dependent inversion x; clear x
          end;
   intros; s; tac;
     repeat ((
       search_prem ltac:(idtac;
         search_conc ltac:(apply himp_frame || (apply himp_frame_cell; trivial))) || search_conc concer);
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

Theorem himp_disjoint : forall S T p1 p2 (a1:S) (a2:T), 
  p1 --> a1 * p2 --> a2 ==> p1 --> a1 * p2 --> a2 * [p1 <> p2].
  intros. unfold hprop_imp. intros; repeat (destruct H). destruct H0.
  exists ((x * x0)%heap). exists empty. sep fail auto. exists x. exists x0. sep fail auto. split_prover'. compute.
  split. apply ext_eq. auto. intros. subst.
  compute in H. compute in H2. pose (H p2). pose (H2 p2). destruct H3. destruct H0. compute in H1. compute in H0. rewrite H1 in *. rewrite H0 in *. assumption. 
Qed.

Theorem himp_split_any : ?? * ?? ==> ??.
  unfold hprop_any, hprop_imp; trivial.
Qed.

Theorem himp_disjoint' : forall  h S T p (a1:S) (a2:T), 
  (p --> a1 * p --> a2)%hprop h -> False.
  intros; unfold hprop_imp; intros. repeat (destruct H). destruct H0. destruct H0. destruct H3. unfold disjoint1 in *. pose (H p). rewrite H0 in y. rewrite H3 in y. trivial.
Qed.