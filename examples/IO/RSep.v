Require Import Ynot.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

(** List "normalization" **)
Require Import List.

Theorem cons_app : forall T (a : T) (b c : list T) , (a :: b) ++ c = a :: (b ++ c). 
  reflexivity.
Qed.
Theorem nil_app : forall T (l : list T), nil ++ l = l.
  reflexivity.
Qed.
Theorem map_nil : forall (T U : Type) (f : T -> U), map f nil = nil.
  reflexivity.
Qed.
Theorem map_cons : forall (T U : Type) (f : T -> U) (t : T) (r : list T), map f (t :: r) = (f t) :: map f r.
  reflexivity.
Qed.
Theorem rev_app : forall T (a b : list T), rev (a ++ b) = (rev b) ++ (rev a).
  induction a; intros; simpl;
    [ rewrite  <- app_nil_end; trivial
    | rewrite (IHa b); rewrite app_ass; trivial ].
Qed.
Theorem foldr_cons : forall (T U:Type) (f: U -> T -> T) a b v, fold_right f v (a :: b) = f a (fold_right f v b).
  reflexivity.
Qed.
Theorem nil_cons_app : forall (A : Type) (l2 : list A) (a : A) (l1 : list A),
  (l1 ++ a :: nil) ++ l2 = l1 ++ a :: l2.
  induction l1; auto. simpl. rewrite IHl1. auto.
Qed.

Ltac norm_list :=
  let t := progress ((repeat rewrite <- app_comm_cons);
                     (repeat rewrite app_ass);
                     (repeat rewrite nil_app);
                     (repeat rewrite cons_app);
                     (repeat rewrite <- app_nil_end); 
                     (repeat rewrite map_app);
                     (repeat rewrite map_cons);
                     (repeat rewrite map_nil);
                     (repeat rewrite foldr_cons)) in
    repeat t.
Ltac norm_list_hyp H :=
  let t := progress ((repeat rewrite <- app_comm_cons in H);
                     (repeat rewrite app_ass in H);
                     (repeat rewrite nil_app in H);
                     (repeat rewrite cons_app in H);
                     (repeat rewrite <- app_nil_end in H);
                     (repeat rewrite map_app in H);
                     (repeat rewrite map_cons in H);
                     (repeat rewrite map_nil in H);
                     (repeat rewrite foldr_cons in H)) in
    repeat t.

Theorem list_no_cycle : forall (T : Type) (l1 l2 : list T),
  l2 <> nil -> l1 <> l2 ++ l1.
  induction l1. 
    auto.
    intros. rewrite <- app_nil_end. auto.
    intros. destruct l2. congruence. unfold not in *. intros. inversion H0.
    norm_list_hyp H3. eapply IHl1. instantiate (1 := (l2 ++ t :: nil)). intros. destruct l2; discriminate.
      norm_list; auto.
Qed.

Theorem decideable_in : forall T (dec : forall a b : T, {a = b} + {a <> b}) (a x : T) b,
  In x (a :: b) -> a = x \/ (x <> a /\ In x b).
  intros. destruct (dec x a); auto. 
  right. destruct H. congruence. auto.
Qed.

(** Pair "normalization" **)
Lemma simpl_fst : forall (T U : Type) (a : T) (b : U), fst (a,b) = a.
  auto.
Qed.
Lemma simpl_snd : forall (T U : Type) (a : T) (b : U), snd (a,b) = b.
  auto.
Qed.

Ltac norm_prod :=
  repeat (rewrite simpl_fst in * || rewrite simpl_snd in *).



(** TODO List
 ** - Existentials
 ** - Pure propositions
 ** - Expander
 ** - Fixpoint
 **)

Theorem himp_refl : forall p, p ==> p.
sep fail auto.
Qed.

Theorem himp_empty_prem : forall p q,
  p ==> q
  -> __ * p ==> q.
sep fail auto.
Qed.

Theorem himp_empty_conc : forall p q, 
  p ==> q
  -> p ==> __ * q.
  sep fail auto.
Qed.

Theorem himp_comm_prem : forall p q r,
  q * p ==> r
  -> p * q ==> r.
  unfold hprop_imp, hprop_sep; intuition.
  apply H.
  do 2 destruct H0; intuition.
  exists x0; exists x; intuition.
Qed.

Definition UnpackAs (T : Type) (x : inhabited T) (y : T) : Prop := x = (inhabits y).

Theorem __mark_UnpackAs : forall (T : Type) (x : inhabited T) (y : T), x = (inhabits y) -> UnpackAs _ x y.
  unfold UnpackAs; auto.
Qed.

Ltac print_goal := idtac;
  match goal with
    | [ |- ?G ] => idtac G
  end.

Ltac meta X := 
  match X with
    | _ _ => fail 1
    | _ _ _ => fail 1
    | _ _ _ _ => fail 1
    | _ _ _ _ _ => fail 1
    | _ _ _ _ _ _ => fail 1
    | _ _ _ _ _ _ _ => fail 1
    | _ _ _ _ _ _ _ _ => fail 1
    | _ * _ => fail 1
    | X => fail 1
    | _ => idtac
  end.
Ltac notMeta X :=
  match X with
    | _ _ => idtac
    | _ _ _ => idtac
    | _ _ _ _ => idtac
    | _ _ _ _ _ => idtac
    | _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ => idtac
    | _ * _ => idtac
    | X => idtac
  end.

Ltac var x := idtac;
  match x with
    | _ _ => fail 1
    | _ _ _ => fail 1
    | _ _ _ _ => fail 1
    | _ _ _ _ _ => fail 1
    | _ _ _ _ _ _ => fail 1
    | _ _ _ _ _ _ _ => fail 1
    | _ => idtac
  end.

(** Do NOT call this function, use red_prem or red_conc **)
Ltac hred assoc1 assoc2 comm intro_empty TG tac :=
  let rec search p qc :=
    match p with
      | ((?p1 * ?p2) * ?p3)%hprop =>
           (apply assoc1; search (p1 * (p2 * p3)) qc) 
        || (apply assoc2; search (p2 * (p1 * p3)) qc)
        || (match qc with
              | 1 => apply comm; search (p3 * (p1 * p2)) 0
            end)
        || (fail 1)
      | (?p1 * ?p2) => 
           tac p1 (** p1 is a terminal **) 
        || (match qc with
              | 1 => apply comm; search (p2 * p1) 0
            end)
    end
  in
  match TG with
    | (_ * _)%hprop => search TG 1 || fail 1
    | __ => fail 1
    | ?p => apply intro_empty; tac p
  end.

Ltac red_prem tac := idtac;
  match goal with
    | [ |- ?P ==> _ ] => 
      hred himp_assoc_prem1 himp_assoc_prem2 himp_comm_prem himp_empty_prem' P tac
  end.
Ltac red_conc tac := idtac;
  match goal with
    | [ |- _ ==> ?P ] => 
      hred himp_assoc_conc1 himp_assoc_conc2 himp_comm_conc himp_empty_conc' P tac
  end.

Lemma himp_trivial_prem : forall T (x:T) P Q,
  P ==> Q -> [x = x] * P ==> Q.
  sep fail auto.
Qed.

(** clean is an idempotent function which always succeeds. It takes a goal of the form
 **   P ==> Q, and
 ** - Eliminates all toplevel __ in P and Q
 **)
Ltac clean :=
  let rem_prem _ := idtac;
    match goal with 
      | [ |- __ * _ ==> _ ] => apply himp_empty_prem
      | [ |- [?X = ?X] * _ ==> _ ] => apply himp_trivial_prem
    end
  in
  let rem_conc _ := idtac;
    match goal with
      | [ |- _ ==> __ * _ ] => apply himp_empty_conc
    end
  in
  (repeat match goal with 
            | [ H : ?X = ?X |- _ ] => clear H
          end);
  match goal with 
    | [ |- _ ==> __ ] => repeat red_prem rem_prem
    | [ |- __ ==> _ ] => repeat red_conc rem_conc
    | [ |- _ ==> _ ]  => repeat red_prem rem_prem; repeat red_conc rem_conc
    | [ |- ?X ] => idtac "ERROR: Malformed goal to 'clean'" X
  end.

Ltac rwpack v :=
  let ty := type of v in
  match ty with 
    | [_]%type =>
      match v with
        | [_]%inhabited => idtac
        | _ => 
          match goal with
            | [ H : [_]%inhabited = v |- _ ] => rewrite <- H
            | [ H : v = [_]%inhabited |- _ ] => rewrite -> H
            | [ H : v = inhabit_unpack _ _ |- _ ] => unfold inhabit_unpack in H; rewrite -> H
            | [ H : inhabit_unpack _ _ = v |- _ ] => unfold inhabit_unpack in H; rewrite <- H
            | [ H : v = ?X |- _ ] => idtac "non-simple rewrite" X; fail 6
            | [ H : ?X = v |- _ ] => idtac "non-simple rewrite" X; fail 6
            | _ => (** there isn't an equation **)
              let H := fresh "H" in 
              pose (H := pack_type_inv v); destruct H;
              match goal with 
                | [ H' : v = [_]%inhabited |- _ ] => rewrite H'
              end
          end
      end
    | _ => idtac "ERROR: rwpack called on non inhabited term" v; fail
  end.

Ltac rwpack_hyp Hy v :=
  let ty := type of v in
  match ty with 
    | [_]%type =>
      match v with
        | [_]%inhabited => idtac
        | _ => 
          match goal with
            | [ H : [_]%inhabited = v |- _ ] => rewrite <- H in Hy
            | [ H : v = [_]%inhabited |- _ ] => rewrite -> H in Hy
            | [ H : v = inhabit_unpack _ _ |- _ ] => unfold inhabit_unpack in H; rewrite -> H in Hy
            | [ H : inhabit_unpack _ _ = v |- _ ] => unfold inhabit_unpack in H; rewrite <- H in Hy
            | [ H : v = ?X |- _ ] => idtac "non-simple rewrite" X; fail 6
            | [ H : ?X = v |- _ ] => idtac "non-simple rewrite" X; fail 6
            | _ => (** there isn't an equation **)
              let H := fresh "H" in 
(** TODO: 
 ** Need to do something here to solve the extra meta-variable instantiation
 **)
              pose (H := pack_type_inv v); destruct H;
              match goal with 
                | [ H' : v = [_]%inhabited |- _ ] => rewrite H' in Hy
              end
          end
      end
    | _ => idtac "ERROR: rwpack called on non inhabited term" v; fail
  end.

Ltac unpack_hypothesis := idtac;
  repeat match goal with
           | [ H : inhabit_unpack ?X _ = _ |- _ ] =>
             rwpack_hyp H X; unfold inhabit_unpack in H
           | [ H : _ = inhabit_unpack ?X _ |- _ ] =>
             rwpack_hyp H X; unfold inhabit_unpack in H

           | [ H : _ = inhabit_unpack2 ?X ?Y _ |- _ ] =>
             rwpack_hyp H X; rwpack_hyp H Y; unfold inhabit_unpack2 in H
           | [ H : inhabit_unpack2 ?X ?Y _ = _ |- _ ] =>
             rwpack_hyp H X; rwpack_hyp H Y; unfold inhabit_unpack2 in H

           | [ H : _ = inhabit_unpack3 ?X ?Y ?Z _ |- _ ] =>
             rwpack_hyp H X; rwpack_hyp H Y; rwpack_hyp H Z; unfold inhabit_unpack3 in H
           | [ H : inhabit_unpack3 ?X ?Y ?Z _ = _ |- _ ] =>
             rwpack_hyp H X; rwpack_hyp H Y; rwpack_hyp H Z; unfold inhabit_unpack3 in H

           | [ H : _ = inhabit_unpack4 ?X ?Y ?Z ?A _ |- _ ] =>
             rwpack_hyp H X; rwpack_hyp H Y; rwpack_hyp H Z; rwpack_hyp H A; unfold inhabit_unpack4 in H
           | [ H : inhabit_unpack4 ?X ?Y ?Z ?A _ = _ |- _ ] =>
             rwpack_hyp H X; rwpack_hyp H Y; rwpack_hyp H Z; rwpack_hyp H A; unfold inhabit_unpack4 in H
         end.

Ltac rewrite_inhabits := idtac;
  repeat match goal with
           | [ H : [?L]%inhabited = [?R]%inhabited |- _ ] => 
             var R; rewrite <- (pack_injective H)
           | [ H : [?L]%inhabited = [?R]%inhabited |- _ ] =>
             (var R; fail 2) || (var L; rewrite -> (pack_injective H))
         end.


(** unpack_premise is an idempotent function which succeeds only if it makes progress.
 ** It takes a goal of the form 
 **   P ==> Q, and
 ** - Eliminates all hprop_unpack constructs in P.
 ** - Introduced variables are given by equations constructed as follows:
 **     hprop_unpack [X] (fun Y => ...)
 **   becomes
 **     [X]%inhabited = [Y]%inhabited
 **   Equations of this form should, subsequently be substituted and eliminated if possible
 **)
Ltac unpack_premise :=
  let label X := idtac;
    match goal with
      | [ H : ?Y = [X]%inhabited |- _ ] =>
        let H' := fresh "UP" in assert (H' := @__mark_UnpackAs _ Y X H)
      | [ H : [X]%inhabited = ?Y |- _ ] => 
        let H' := fresh "UP" in symmetry in H; assert (H' := @__mark_UnpackAs _ Y X H); symmetry in H
    end
  in
  let handle _ := idtac;
    match goal with 
      | [ |- hprop_unpack [?X] _ * _ ==> _ ] => apply himp_unpack_prem; try label X       
      | [ H : ?X = [?Y] |- hprop_unpack ?X _ * _ ==> _ ] => rewrite H; apply himp_unpack_prem; try label Y
      | [ H : [?Y] = ?X |- hprop_unpack ?X _ * _ ==> _ ] => rewrite <- H; apply himp_unpack_prem; try label Y
      | [ |- hprop_unpack ?X _ * _ ==> _ ] => rwpack X;
        (try match goal with
               | [ H : X = [?Y]%inhabited |- _ ] => label Y
               | [ H : [?Y]%inhabited = X |- _ ] => label Y
             end); apply himp_unpack_prem
      | [ |- _ ] => fail
    end
  in match goal with 
       | [ |- _ ==> _ ] => repeat red_prem handle
       | [ |- ?X ] => idtac "ERROR: Malformed goal to 'unpack_premise'" X; fail
     end.

Theorem himp_unpack_conc_meta : forall T x (y:[T]) p1 p2 p,
  p ==> p1 x * p2
  -> y = [x]%inhabited
  -> p ==> hprop_unpack y p1 * p2.
  unfold hprop_imp, hprop_unpack, hprop_sep; subst; firstorder.
  generalize (H _ H1).
  firstorder.
Qed.

Theorem himp_unpack_conc_imm : forall (T:Set) (x : T) p1 p2 p,
  p ==> p1 x * p2
  -> p ==> hprop_unpack [x] p1 * p2.
  sep fail auto.
Qed.

(** unpack_conc is an idempotent function which succeeds only if it makes progress.
 ** It takes a goal of the form 
 **   P ==> Q, and
 ** - Eliminates all occurances of hprop_unpack in Q by beta reduction.
 **)
Ltac unpack_conclusion :=
  let handle _ := idtac;
    match goal with 
      | [ |- _ ==> hprop_unpack [?X] _ * _ ] => apply himp_unpack_conc_imm
      | [ H : ?X = [_] |- _ ==> hprop_unpack ?X _ * _ ] => rewrite H; apply himp_unpack_conc_imm
      | [ H : [_] = ?X |- _ ==> hprop_unpack ?X _ * _ ] => rewrite <- H; apply himp_unpack_conc_imm
      | [ |- _ ==> hprop_unpack ?X _ * _ ] => meta X; eapply himp_unpack_conc_meta
      | [ |- _ ==> hprop_unpack ?X _ * _ ] => rwpack X; apply himp_unpack_conc_imm
      | [ |- _ ==> hprop_unpack ?B _ * _ ] => 
        let ty' := type of B in
        let H := fresh "H" in 
        let ty := match ty' with 
                    | [?X]%type => X
                    | _ => idtac "no match" ty'
                  end
        in match B with 
             | (inhabit_unpack2 [?X] [?Y] ?Z) => 
               assert (H : B = [Z X Y]%inhabited); [ reflexivity | ]; rewrite H; clear H
             | (inhabit_unpack [?X] ?Z) =>
               assert (H : B = [Z X]%inhabited); [ reflexivity | ]; rewrite H; clear H
             | (inhabit_unpack2 ?X ?Y ?Z) => 
               rwpack X; rwpack Y
(* ; assert (H : B = [Z X Y]%inhabited); [ reflexivity | ]; rewrite H; clear H *)
             | (inhabit_unpack ?X ?Z) =>
               rwpack X
(*; assert (H : B = [Z X]%inhabited); [ reflexivity | ]; rewrite H; clear H *)
           end
    end
  in match goal with 
       | [ |- _ ==> _ ] => repeat red_conc handle
       | [ |- ?X ] => idtac "ERROR: Malformed goal to 'unpack_conclusion'" X; fail
     end.

Ltac expose :=
  intros; cbv beta.

Ltac instantiate_meta :=
  let requantify := idtac;
    match goal with
      | [ |- ?P ==> ?Q ] => 
        let Q1 := fresh "QUANTIFY" in
        pose (Q1 := P);
        repeat match goal with
                 | [ H' : UnpackAs _ ?X ?Y |- _ ] =>
                   let y := eval cbv delta [Q1] in Q1 in
                   match y with 
                     | context [ Y ] =>
                       pattern Y in Q1;
                       let y := eval cbv delta [Q1] in Q1 in
                       match y with
                         | ?F _ => 
                           let Q2 := fresh "QUANTIFY" in
                           pose (Q2 := hprop_unpack X F); clear Q1; rename Q2 into Q1
                       end
                   end
               end;
        (** This part shouldn't be needed but Coq is being really strange... **)
        match goal with
          | [ |- _ ==> ?Q ] => assert (Q = Q1); [ unfold Q1;
            (repeat match goal with 
                      | [ H : ?X = [?Y]%inhabited, H' : UnpackAs _ ?X ?Y |- _ ] => rewrite <- H
                    end); reflexivity | ]
        end
      | [ |- _ ==> _ ] => idtac
    end
  in
  requantify.

(** reducer
 **)

Theorem himp_frame_eq : forall T p Q R (v v' : T),
  v = v' -> Q ==> R
  -> p --> v * Q ==> p --> v' * R.
  intros. rewrite H. sep fail auto.
Qed.

Ltac extension P HD solver := 
(**  let break := apply himp_split; [ (solver; fail) | ] in **)
  let split_solve := (apply himp_frame) in
  match HD with
    (** Unary functions **)
    | ?A ?B => notMeta A; meta B;
      match P with
        | context H [ A _ ] =>
          match context H [__] with
            | context [ A _ ] => fail 4 (** Occurs multiple times, don't try anything **)
            | _ =>
              let r HD' :=
                match HD' with 
                  | A _ => split_solve
                end
                in red_prem r
          end
      end
    (** Binary functions **)
    | ?A ?B ?C => notMeta A; notMeta B; meta C;
      match P with 
        | context H [ A B _ ] =>
          match context H [__] with
            | context [ A B _ ] => fail 4 (** Occurs multiple times, don't try anything **)
            | _ => 
              let r HD' :=
                match HD' with 
                  | A B _ => split_solve
                end
                in red_prem r
          end
      end
    | ?A ?B ?C => notMeta A; meta B; notMeta C;
      match P with 
        | context H [ A _ C ] =>
          match context H [__] with
            | context [ A _ C ] => fail 4 (** Occurs multiple times, don't try anything **)
            | _ => 
              let r HD' :=
                match HD' with 
                  | A B _ => split_solve
                end
                in red_prem r
          end
      end
    | ?A ?B ?C => notMeta A; meta B; meta C;
      match P with 
        | context H [ A _ _ ] =>
          match context H [__] with
            | context [ A _ _ ] => fail 4 (** Occurs multiple times, don't try anything **)
            | _ => 
              let r HD' :=
                match HD' with 
                           | A B _ => split_solve
                end
                in red_prem r
          end
      end
    (** Ternary functions **)
    | ?A ?B ?C ?D => notMeta A; notMeta B; notMeta C; meta D; 
      match P with 
        | context H [ A B C _ ] =>
          match context H [__] with
            | context [ A B C _ ] => fail 4 (** Occurs multiple times, don't try anything **)
            | _ => 
              let r HD' :=
                match HD' with 
                  | A B C _ => split_solve
                end
                in red_prem r
          end
      end
    | ?A ?B ?C ?D => notMeta A; notMeta B; meta C; notMeta D; 
      match P with 
        | context H [ A B _ D ] =>
          match context H [__] with
            | context [ A B _ D ] => fail 4 (** Occurs multiple times, don't try anything **)
            | _ => 
              let r HD' :=
                match HD' with 
                  | A B _ D => split_solve
                end
                in red_prem r
          end
      end
    | ?A ?B ?C ?D => notMeta A; meta B; notMeta C; notMeta D; 
      match P with 
        | context H [ A _ C D ] =>
          match context H [__] with
            | context [ A _ C D ] => fail 4 (** Occurs multiple times, don't try anything **)
            | _ => 
              let r HD' :=
                match HD' with 
                  | A _ C D => split_solve
                end
                in red_prem r
          end
      end
    | ?A ?B ?C ?D => notMeta A; meta B; meta C; notMeta D; 
      match P with 
        | context H [ A _ _ D ] =>
          match context H [__] with
            | context [ A _ _ D ] => fail 4 (** Occurs multiple times, don't try anything **)
            | _ => 
              let r HD' :=
                match HD' with 
                  | A _ _ D => split_solve
                end
                in red_prem r
          end
      end
    | ?A ?B ?C ?D => notMeta A; meta B; notMeta C; meta D; 
      match P with 
        | context H [ A _ C _ ] =>
          match context H [__] with
            | context [ A _ C _ ] => fail 4 (** Occurs multiple times, don't try anything **)
            | _ => 
              let r HD' :=
                match HD' with 
                  | A _ C _ => split_solve
                end
                in red_prem r
          end
      end
    | ?A ?B ?C ?D => notMeta A; notMeta B; meta C; meta D; 
      match P with 
        | context H [ A B _ _ ] =>
          match context H [__] with
            | context [ A B _ _ ] => fail 4 (** Occurs multiple times, don't try anything **)
            | _ => 
              let r HD' :=
                match HD' with 
                  | A B _ _ => split_solve
                end
                in red_prem r
          end
      end
    | ?A ?B ?C ?D => notMeta A; meta B; meta C; meta D; 
      match P with 
        | context H [ A _ _ _ ] =>
          match context H [__] with
            | context [ A _ _ _ ] => fail 4 (** Occurs multiple times, don't try anything **)
            | _ => 
              let r HD' :=
                match HD' with 
                  | A _ _ _ => split_solve
                end
                in red_prem r
          end
      end
  end.

Ltac reducer solver :=
  let handle HD := notMeta HD; (** We're not reducing toplevel meta variables **)
    match goal with 
      | [ |- ?P ==> _ ] =>
           let r HD' :=
             match HD with 
               | HD' => apply himp_frame
             end
           in red_prem r
        || match HD with
             | [?G] => assert (G); [ solve [ solver ] | ]; apply himp_inj_conc
               (** TODO : temporary **)
             (** Heap **)
             | ?P --> ?V => notMeta P;
               let r HD' :=
                 match HD with 
                   | P --> ?V' => apply himp_frame_eq; [ solve [ assumption | solver ] | ]
                 end
               in red_prem r
           end
        || extension P HD solver
    end
  in red_conc handle.

Ltac finish_trivial solver :=
  let requantify_meta := (instantiate_meta; unpack_conclusion; (repeat reducer auto); clean; apply himp_refl) in
  let trymeta := solve [ requantify_meta ] in
  rewrite_inhabits;
  match goal with
    | [ |- __ ==> __ ] => apply himp_refl
    | [ |- _ ==> ?M ] => meta M; trymeta
    | [ |- ?P ==> __ ] =>
      let forget H :=
        match H with
          | [_] => idtac "Warning: Forgetting Pure Information!!!" H; print_goal;
                   apply himp_empty_conc'; apply himp_inj_prem; [ intro ]
        end
      in solve [ clean; simpl; repeat red_prem forget; clean; simpl; trymeta ]
    | _ => solver; try solve [ apply himp_refl ]
  end.

Ltac rsep expander solver :=
  let delegate := (repeat progress expander); solver in
  expose; clean; 
     (equater; apply himp_refl)
  || (unpack_premise; intro_pure; unpack_conclusion; unpack_hypothesis; 
      rewrite_inhabits; (repeat progress expander);
      rewrite_inhabits; repeat reducer delegate; finish_trivial solver).

Theorem himp_inj_conc' : forall h1 (P:Prop), h1 ==> __ -> P -> h1 ==> [P].
  intros. apply himp_empty_conc'. apply himp_inj_conc; auto.
Qed. 

Ltac cut_pure := 
  let rec handle solver := idtac;
    match goal with
      | [ |- _ ==> [?P] ] => cut (P); [ intro; apply himp_inj_conc'; [ finish_trivial solver | assumption ] | ]
      | [ |- _ ==> [?P] * _ ] => cut (P); [ intro; apply himp_inj_conc; [ assumption | handle solver ] | ]
    end
  in clean; handle ltac:(idtac).

(** Rewriting with ==> **)
Ltac seprw H' := 
      let H := fresh "H" in
      pose (H := H'); 
      match goal with
        | [ H'' : ?L ==> ?R |- ?P ==> ?Q ] =>
          match H'' with
            | H => 
              match P with 
                | context P' [ L ] =>
                  let Q' := context P' [ R ] in
                  apply (@himp_trans Q' P Q H); clear H
              end
            | _ ==> _ => clear H; fail 2 "Nothing to rewrite"
          end
        | [ H' : ?Z |- _ ==> _ ] => 
          match H' with
            | H => clear H; fail 2 "Must rewrite with ==>: " Z
          end
        | _ => clear H; fail 1 "Must rewrite over ==>"
      end.
