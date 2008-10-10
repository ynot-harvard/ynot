Require Import Ynot.

Set Implicit Arguments.


Module Type COUNTER.
  Parameter t : Set.
  Parameter rep : t -> nat -> hprop.

  Parameter new : STsep __ (fun c => rep c 0).
  Parameter free : forall c n, STsep (n ~~ rep c n) (fun _ : unit => __)%hprop.
  Parameter get : forall c n, STsep (n ~~ rep c n) (fun n' => n ~~ rep c n * [n' = n])%hprop.
  Parameter inc : forall c n, STsep (n ~~ rep c n) (fun _ : unit => n ~~ rep c (S n))%hprop.
End COUNTER.

Module Counter : COUNTER.
  Definition t := ptr.
  Definition rep (p : t) (n : nat) := (p --> n)%hprop.

  Ltac t := unfold rep; sep idtac.

  Open Local Scope stsep_scope.

  Definition new : STsep __ (fun c => rep c 0).
    refine {{New 0}}; t.
  Qed.

  Definition free : forall c n, STsep (n ~~ rep c n) (fun _ : unit => __)%hprop.
    intros; refine {{Free c :@ _}}; t.
  Qed.

  Theorem unpack : forall T (h : [T]) (P : Prop),
    (forall x, h = [x]%inhabited -> P)
    -> P.
    dependent inversion h; eauto.
  Qed.

  Axiom cheat : forall T, T.

  Theorem himp_unpack_prem' : forall T h (x : T) p1 p2 p,
    h = [x]%inhabited
    -> p1 x * p2 ==> p
    -> hprop_unpack h p1 * p2 ==> p.
    t.
  Qed.

  Definition done T (x : T) := True.

  Definition get : forall c n, STsep (n ~~ rep c n) (fun n' => n ~~ rep c n * [n' = n])%hprop.
    intros; refine {{c ! _}}.

    Ltac t' n := match goal with
                   | [ |- context[?Q _] ] => equate Q (fun x => n ~~ [x = n])%hprop
                 end.

    unfold rep.

    apply (unpack (h := n)); do 2 intro.

    apply himp_empty_prem'.
    eapply himp_unpack_prem'.
    eassumption.

    match goal with
      | [ |- ?P ==> Exists v :@ _, (?ptr --> v * ?Q v)%hprop ] =>
        let rec findContents P :=
          match P with
            | (ptr --> ?V)%hprop => constr:(V, __)%hprop
            | (?P1 * ?P2)%hprop =>
              match findContents P1 with
                | (?V, ?P1) => constr:(V, P1 * P2)%hprop
                | _ =>
                  match findContents P2 with
                    | (?V, ?P2) => constr:(V, P1 * P2)%hprop
                  end
              end
            | _ => tt
          end
        in match findContents P with
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
                                                match goal with
                                                  | [ _ : done x |- _ ] => fail 1
                                                  | _ =>
                                                    pattern v in F;
                                                      let y := eval cbv delta [F] in F in
                                                        match y with
                                                          | ?F' _ =>
                                                            pose (F2 := fun y => hprop_unpack x (fun x => F' x y));
                                                              unfold F in F2; clear F; rename F2 into F;
                                                                generalize (I : done x); intro
                                                        end
                                                end;
                                                repeat match goal with
                                                         | [ H : done _ |- _ ] => clear H
                                                       end;
                                                let y := eval cbv delta [F] in F in
                                                  clear F;
                                                    equate Q y
                                            end
                             end
           end
    end; t.

    t.
  Qed.

  Definition inc : forall c n, STsep (n ~~ rep c n) (fun _ : unit => n ~~ rep c (S n))%hprop.
    intros; refine (
      n' <- c ! (fun n' => n ~~ [n' = n])%hprop;

      {{c ::= S n' <@> (n ~~ [n' = n])%hprop}}
    ); t.
  Qed.
End Counter.
