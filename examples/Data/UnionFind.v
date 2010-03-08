Require Setoid.
Require Import Equivalence.
Require Import Program.Equality.
Require Import Ynot.

Definition ptsto_any_tot (p : ptr) :=
  ptsto_any p (Qcanon.Q2Qc (QArith_base.Qmake BinInt.Z0 BinPos.xH)).

Require Import Array.
Require Import List.
Require Import Relations.
Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.
Require Import Arith.

Generalizable All Variables.
Set Automatic Introduction.
Unset Implicit Arguments.

Ltac t := sep fail simpl.

Ltac dest_unpack f :=
  case_eq f; intros; rewrite <- ! hiff_unpack.

Ltac move_one_pure := 
  match goal with
    | |- hprop_inj _ * _ ==> _ => apply himp_inj_prem; intro
    | |- _ * ?Q ==> _ => 
      match Q with 
        context [ hprop_inj _ ] => 
        rewrite hstar_comm; rewrite <- ! hstar_assoc
      end
  end.

Ltac move_one_pure_concl := 
  match goal with
    | |- ?p ==> hprop_inj ?P * ?q => 
      match goal with
        | H' : P |- _ => apply (himp_inj_conc H'); try move_one_pure_concl
        | _ => 
          let H := fresh in
            cut P; [intro H; apply (himp_inj_conc H); try move_one_pure_concl|idtac]
      end
    | |- _ ==>  ?P * ?Q => 
      match Q with 
        context [ hprop_inj _ ] => 
        rewrite (hstar_comm P Q); rewrite <- ! hstar_assoc
      end
  end.

Ltac move_pure := rewrite <- ! hstar_assoc; repeat move_one_pure;
  try move_one_pure_concl.

Ltac safe_injection H :=
  revert H; progress (intro H ; injection H ; clear H; intros).

Ltac discriminates :=
  match goal with 
    | H : ?n <> ?n |- _ => elim H; reflexivity 
    | H : ?n = ?n |- _ => clear H
    | H : ?x = ?y |- _ => (subst x || subst y ||
      (safe_injection H ; intros))
    | |- ?n <> ?n => elimtype False
    | |- _ <> _ => intro
  end.

Ltac contradictions := contradiction ||
  match goal with 
    H : ?x = ?y |- _ => symmetry in H; contradiction
  end.

Create HintDb dest discriminated.

Ltac simplify_goal := 
  autounfold with dest in *;
  repeat dest_conj;
  try discriminates;
  try contradictions;
  try congruence.

Definition block {A} (a : A) : A := a.
Ltac block H := let T := type of H in change (block T) in H.
Ltac unblock := unfold block in *.  

Ltac myauto := simplify_goal; try typeclasses eauto with dest.
Set Firstorder Solver myauto.

Lemma pair_equal {A B} (x x' : A) (y y' : B) : (x, y) = (x', y') -> x = x' /\ y = y'.
Proof. intros. injection H. intuition. Qed.

Ltac pack_injections := repeat
  match goal with
    H : [_]%inhabited = [_]%inhabited |- _ => 
      apply pack_injective in H
  end. 

Definition hprop_or (P Q : hprop) : hprop :=
  fun h => P h \/ Q h.

Lemma hprop_or_prem p q r : (p ==> r) /\ (q ==> r) -> hprop_or p q ==> r.
Proof. firstorder. Qed.

Lemma hprop_or_left p q r : p ==> q -> p ==> hprop_or q r.
Proof. firstorder. Qed.
  
Lemma hprop_or_right p q r : p ==> r -> p ==> hprop_or q r.
Proof. firstorder. Qed.
  
Theorem himp_ex_conc : forall p T (p1 : T -> _),
  (exists v, p ==> p1 v)
  -> p ==> hprop_ex p1. 
Proof. red.
  intros. destruct H. 
  generalize (H _ H0); clear H H0. simp_heap. eauto 7 with Ynot.
Qed.

Theorem himp_pure2 (P Q : Prop) : [P] * [Q] <==> [P /\ Q].
Proof. reduce. simp_heap. split; simp_heap. red in Hrl, Hrr. subst.
  red. intuition. subst. myauto. myauto. auto. destruct H. do 2 econstructor. intuition.
Qed.
  
Definition hprop_all {A} (p : A -> hprop) : hprop := 
  fun h => forall x : A, p x h.

Notation "'Forall' v :@ T , p" := (hprop_all (fun v : T => p)) (at level 90, T at next level) : hprop_scope.
Lemma hprop_all_conc {A} (P : A -> hprop) p : (forall x : A, p ==> P x) -> p ==> Forall x :@ A, P x.
Proof. intros. red. intros. intro. apply (H x). apply H0. Qed.

Section Make.
  Context {A : Set}.

  Definition valid_array a start len points_to :=
    iter_sep (fun i => p :~~ array_plus a i in points_to p i) start len.

  Definition points_f (f : nat -> A) := 
    fun p i => p --> f i.

  Definition rep_array a n (f : nat -> A) :=
    [array_length a = n] *  
    valid_array a 0 n (points_f f).
  
  Section Init.
    Variable init : nat -> A.
  
    Definition initialize_pre(f:array)(n:nat) := 
      valid_array f (array_length f - n) n (fun p _ => ptsto_any_tot p).
    
    Definition initialize_post(f:array)(n:nat)(_:unit) := 
      valid_array f (array_length f - n) n (points_f init).
    
    Definition initialize_array_spec (f:array)(n:nat) := (n <= array_length f)%nat -> 
      STsep (initialize_pre f n) (initialize_post f n).
  
    Definition initialize_array_aux (a : array) (n : nat) : initialize_array_spec a n.
    Proof. revert n.
      refine(fix make(n:nat) : initialize_array_spec a n :=
        IfZero n
        Then fun _ => {{Return tt}}
        Else fun _ => 
          upd_array a (array_length a - S n) (init (array_length a - S n)) <@> (initialize_pre a n) ;;
          {{make n _ <@> _}}); clear make;
      unfold initialize_post, initialize_pre, initialize_array_spec, ptsto_any_tot, valid_array, points_f,
        ptsto_any; t;
        assert(Hi : (S (array_length a - S n0) = array_length a - n0)%nat) by omega; try rewrite Hi; t.
    Defined.
  
    Definition initialize_array (a : array) :
      STsep (valid_array a 0 (array_length a) (fun p i => ptsto_any_tot p))
      (fun (_ : unit) => rep_array a (array_length a) init).
    Proof. intros. unfold rep_array.
      refine {{@initialize_array_aux a (array_length a) (le_n (array_length a))}}; 
        unfold initialize_pre, initialize_post, points_f; rewrite minus_diag; t.
    Qed.

    Definition make_array : forall (n : nat), STsep emp
      (fun a : array => rep_array a n init).
    Proof. 
      refine (fun n => 
        a <- new_array n <@> _;
        @initialize_array a <@> ([array_length a = n]) ;;
        {{Return a}}); t.
    Qed.
  End Init.

  Definition get_array (n : nat) (a : array)
    (f : [nat -> A]) : (n < array_length a)%nat ->
    STsep (f ~~ rep_array a (array_length a) f)
    (fun r : A => f ~~ rep_array a (array_length a) f * [r = f n]).
  Proof.
    intros. 
    refine (x <- sub_array a n (fun v => f ~~ [v = f n]) 
      <@> (f ~~ valid_array a 0 n (fun p i => p --> f i) * valid_array a (S n) (array_length a - n - 1) (fun p i => p --> f i)) ;
      {{Return x}}).
    unfold rep_array, valid_array. t.
    rewrite hstar_assoc. setoid_rewrite hstar_comm at 2.
    rewrite (split_index_sep _ 0 H). t. 
    t. t. t.

    unfold rep_array. t.
    rewrite hstar_assoc. setoid_rewrite hstar_comm at 2.
    unfold valid_array.
    assert (x1 --> x2 n <==> hprop_unpack (array_plus a n) (fun p => p --> x2 n)). 
    rewrite H0. rewrite <- hiff_unpack. reflexivity.
    rewrite H1.
    rewrite join_index_sep; auto.
  Qed.

  Lemma model_array_split_at (a : array) (f : nat -> A) (i : nat) : (i < array_length a)%nat ->
    forall p : ptr, array_plus a i = [p]%inhabited ->
      rep_array a (array_length a) f ==> 
    (valid_array a 0 i (points_f f) *
      points_f f p i * 
      valid_array a (S i) (array_length a - i - 1) (points_f f))%hprop.
  Proof.
    intros. unfold rep_array, valid_array, points_f. 
    rewrite (split_index_sep (fun i =>
      hprop_unpack (array_plus a i) (fun p0 : ptr => p0 --> f i)) 0 H). t.
  Qed.

  Definition upd_model (f : nat -> A) (n : nat) (v : A) := 
    fun i => if eq_nat_dec i n then v else f i.

  Lemma valid_array_update a start len f n v : 
    (n < start \/ len + start <= n)%nat ->
    valid_array a start len (points_f f) ==>
    valid_array a start len (points_f (upd_model f n v)).
  Proof. intros.
    unfold valid_array. apply iter_imp. intros.
    dest_unpack (array_plus a i). 
    unfold upd_model, points_f.
    case_eq (eq_nat_dec i n). intros. subst.
    destruct H; elimtype False; omega. myauto.
  Qed.

  Definition set_array (a : array) (n : nat) (v : A) (f : [nat -> A]) : (n < array_length a)%nat ->
    STsep (f ~~ rep_array a (array_length a) f)
    (fun _ : unit => f ~~ rep_array a (array_length a) (upd_model f n v)).
  Proof. intros.
    refine {{upd_array a n v <@> (f ~~
      valid_array a 0 n (points_f f) * valid_array a (S n) (array_length a - n - 1) 
      (points_f f))%hprop}}.
    unfold rep_array; t.
    setoid_rewrite hstar_comm at 1.
    setoid_rewrite <- hstar_assoc.
    setoid_rewrite hstar_comm at 2.
    setoid_rewrite hstar_assoc.
    Existential 1 := A. Existential 1 := (x n). instantiate. 
    change (x0 --> x n) with (points_f x x0 n).
    rewrite <- model_array_split_at; auto. unfold rep_array. t.

    t. rewrite <- hstar_assoc. setoid_rewrite hstar_comm at 2. rewrite hstar_assoc.
        
    unfold rep_array.
    dest_unpack (array_plus a n).
    rewrite (@valid_array_update a 0 n x n v); try omega.
    rewrite (@valid_array_update a (S n) (array_length a - n - 1) x n v); try omega.
    change (p --> v) with ((fun p => p --> v) p).
    rewrite (hiff_unpack p). rewrite <- H0.
    assert (hprop_unpack (array_plus a n) (fun p => p --> v) <==> (p :~~ array_plus a n in points_f (upd_model x n v) p n))%hprop.
    unfold points_f, upd_model. dest_unpack (array_plus a n). 
    case_eq (eq_nat_dec n n); intros; subst. reflexivity. intuition.
    rewrite H1. clear H0 H1.
    t. apply join_index_sep. auto.
  Qed.

  Lemma valid_array_model a start len f : valid_array a start len (points_f f) <==> 
    {@ p :~~ array_plus a i in p --> f i | i <- start + len}.
  Proof. unfold valid_array. reflexivity. Qed.

End Make.

Section Fin.

  Definition fin size := sig (fun n : nat => n < size).
  
  Definition fin_eq {size} (x y : fin size) := proj1_sig x = proj1_sig y.
  Definition fin_neq {size} (x y : fin size) := not (fin_eq x y).
  
  Definition eq_fin_dec {n} (x y : fin n) : { x = y } + { x <> y }.
  Proof. intros. destruct x; destruct y. 
    case (eq_nat_dec x x0). intros. subst. left. 
    f_equal.
    apply proof_irrelevance.
    intros. right.
    intro. apply n0. injection H. auto.
  Defined.

  Definition build_fin {size} (i : nat) : option (fin size) :=
    match lt_dec i size with
      | left prf => Some (exist _ i prf)
      | right _ => None
    end.

End Fin.

Definition upd_model_fin {A : Set} {size} (f : fin size -> A) (n : fin size) (v : A) := 
  fun i => if eq_fin_dec i n then v else f i.

Section ArrayFin.
  Context {A : Set}.
  
  Definition repr_fn {size} a (points_to : fin size -> A) :=
    iter_sep (fun i => p :~~ array_plus a i in 
      Exists prf :@ i < size,
      p --> points_to (exist (fun i => i < size) i prf)) 0 size.

  Definition repr_array {size} a (f : fin size -> A) :=
    ([array_length a = size] * repr_fn a f)%hprop.

  Definition make_array_fin (n : nat) (f : fin n -> A) : STsep emp 
    (fun a => repr_array a f)%hprop.
  Proof. destruct n. 
    refine {{new_array 0}}; t.
    assert(prf : 0 < S n) by omega.
    refine {{make_array (fun i : nat => match build_fin i return A with
                                    | Some prf => f prf 
                                    | None => f (exist _ 0 prf)
                                  end) (S n)}}.
    t. t. unfold repr_array, repr_fn, rep_array, valid_array.
    apply himp_split. t. apply iter_imp. intros.
    dest_unpack (array_plus v i). apply himp_ex_conc. 
    assert(Hi:i < S n) by omega. exists Hi. unfold points_f.
    unfold build_fin. destruct lt_dec. t. f_equal. f_equal. apply proof_irrelevance.
    contradiction.
  Qed.

  Lemma upd_model_refl {size} f (i : fin size) : f i = i ->
    Morphisms.pointwise_relation (fin size) eq (upd_model_fin f i i) f.
  Proof. intros. red; intros. unfold upd_model_fin. case eq_fin_dec; myauto. Qed.
  
  Context {size : nat}.

  Definition get_array_fin (a : array) (n : fin size)
    (f : [fin size -> A]) : array_length a = size ->
    STsep (f ~~ repr_array a f)
    (fun r : A => f ~~ repr_array a f * [r = f n])%hprop.
  Proof.
    destruct size. depelim n. exfalso; inversion l.
    destruct n. intros. assert(x < array_length a) by omega.
    assert(0 < S n0) by omega.
    refine (x <- get_array x a 
      (f ~~~ fun i => match build_fin i return A with
                       | Some prf => f prf 
                       | None => f (exist _ 0 H1) end)
      H0 <@> [array_length a = S n0] ;
    {{Return x}}); t.

    unfold repr_array, repr_fn, rep_array. 
    unfold valid_array. apply himp_split. t. rewrite H. apply iter_imp. intros.
    unfold points_f, build_fin. t.
    case lt_dec. intros. f_equal. f_equal. apply proof_irrelevance.
    myauto.
    unfold repr_array, repr_fn, rep_array.
    setoid_rewrite <- hstar_assoc. 
    apply himp_split; [t|].
    setoid_rewrite hstar_comm. 
    unfold valid_array. apply himp_inj_conc. 
    unfold build_fin. case lt_dec.
    intros. f_equal. f_equal. apply proof_irrelevance.
    myauto.

    rewrite H.
    apply iter_imp. intros.
    dest_unpack (array_plus a i).
    unfold points_f, build_fin.
    case lt_dec. intros. t.
    intros. elimtype False; omega.
  Qed.

  Definition set_array_fin (a : array) (n : fin size) (v : A)
    (f : [fin size -> A]) : array_length a = size ->
    STsep (f ~~ repr_array a f)
    (fun r : unit => f ~~ repr_array a (upd_model_fin f n v))%hprop.
  Proof. destruct n. destruct size. exfalso; depelim l.
    intro Hlen. assert(x < array_length a) by omega.
    assert(Hs:0 < S n) by omega.
    refine (x <- set_array a x v
      (f ~~~ fun i => match build_fin i return A with
                       | Some prf => f prf 
                       | None => f (exist _ 0 Hs) end)
      H <@> [array_length a = S n] ;
    {{Return x}}); unfold repr_array; t. 

    unfold repr_fn, rep_array. apply himp_inj_conc. auto.
    unfold valid_array. rewrite Hlen.

    apply iter_imp. intros.
    dest_unpack (array_plus a i).
    unfold points_f. unfold build_fin. t.
    case lt_dec. intros. do 2 f_equal. apply proof_irrelevance.
    intros. elimtype False; omega.
    
    unfold rep_array. t. unfold valid_array, repr_fn.
    rewrite <- H0 at 1.
    apply iter_imp. intros.
    dest_unpack (array_plus a i).
    unfold points_f, build_fin. apply himp_ex_conc.
    assert(His:i < S n) by omega. exists His.
    t.
    unfold upd_model, upd_model_fin.
    unfold eq_fin_dec. simpl. case eq_nat_dec.
    intros. subst x. unfold eq_rec_r, eq_rec, eq_rect, eq_sym. reflexivity.
    intros.
    case lt_dec. intros. do 2 f_equal. apply proof_irrelevance.
    intros. elimtype False; omega.
  Qed.

End ArrayFin.

Module Type ArrayF.

  Parameter t : Set -> nat -> Set.

  Parameter repr : forall {A size}, t A size -> (fin size -> A) -> hprop.
  
  Parameter create : Π {A : Set} (size : nat) (f : fin size -> A), STsep emp (fun x : t A size => repr x f).

  Parameter get : Π {A : Set} {size : nat} (a : t A size) (f : [fin size -> A]) (n : fin size),
    STsep (f ~~ repr a f) (fun x : A => f ~~ repr a f * [x = f n]).

  Parameter set : Π {A : Set} {size : nat} (a : t A size) 
    (f : [fin size -> A]) (n : fin size) (v : A),
    STsep (f ~~ repr a f) (fun _ : unit => f ~~ repr a (upd_model_fin f n v)).

End ArrayF.

Axiom get_prf : Π {P : Prop} {p}, STsep ([P] * p) (fun _ : P => [P] * p).

(** It is safe as the variable is irrelevant, right?
   Otherwise you lose the ability to hide model updates.
 *)

Axiom get_irr : Π (T : Set) (p : T -> hprop),
  STsep (@hprop_ex T p) (fun x : [T] => x ~~ p x).

Module Array_fin <: ArrayF.

  Definition t (A : Set) (n : nat) := sig (fun a : array => array_length a = n).

  Definition repr {A size} (a : t A size) (f : fin size -> A) :=
    let (a, p) := a in
      repr_array a f.

  Definition create {A : Set} {size} (f : fin size -> A) :
    STsep emp (fun x : t A size => repr x f).
  Proof. refine (x <- make_array_fin size f;
    prf <- get_prf ;
    {{Return (exist _ x prf)}}); 
    unfold repr_array; t.
    unfold repr_array; t.
  Qed.

  Definition get {A : Set} {size : nat} (a : t A size) (f : [fin size -> A]) (n : fin size) :
    STsep (f ~~ repr a f) (fun x : A => f ~~ repr a f * [x = f n]) :=
    let 'exist a p := a in get_array_fin a n f p.

  Definition set {A : Set} {size : nat} (a : t A size) 
    (f : [fin size -> A]) (n : fin size) (v : A) :
    STsep (f ~~ repr a f) (fun _ : unit => f ~~ repr a (upd_model_fin f n v)) :=
    let 'exist a p := a in set_array_fin a n v f p.

End Array_fin.

Module Array : ArrayF := Array_fin.

Section UnionFind.

  Definition partition size := fin size -> fin size.

  Definition partition_eq {size} (p q : partition size) : Prop :=
    forall i j : fin size, p i = p j <-> q i = q j.
  
  Instance: Reflexive (@partition_eq size).
  Proof. intros size p i j. reflexivity. Qed.
    
  Instance: Symmetric (@partition_eq size).
  Proof. intros size p p' H i j. red in H. rewrite H. reflexivity. Qed.
    
  Instance: Transitive (@partition_eq size).
  Proof. intros size p p' p'' H H' i j. red in H, H'. etransitivity; eauto. Qed.

  Definition representation size := fin size -> fin size.

  Record uf {size} : Set := {
    parent : Array.t (fin size) size;
    rank : Array.t nat size
  }.

  Definition t (size : nat) := @uf size. 

  Open Local Scope nat_scope.

  Inductive repr {size} (p : partition size) : fin size -> fin size -> Prop :=
    repr_zero : forall i, p i = i -> repr p i i
  | repr_succ : forall i j, p i = j -> i <> j ->
    forall r, repr p j r -> repr p i r.
  
  Hint Constructors repr : repr.

  Definition models_partition {size} (f : representation size) (p : partition size) :=
    forall x, repr f x (p x).

  Definition repr_partition {size} (a : Array.t (fin size) size) (f : representation size) (p : partition size) :=
    (Array.repr a f * [models_partition f p])%hprop.

  Notation "'Exists' v :@ T , p" := (hprop_ex (fun v : T => p%hprop)) (at level 90, T at next level) : hprop_scope.

  Definition repr_uf {size} uf (p : partition size) :=
    Exists pmodel :@ representation size,
    Exists rmodel :@ fin size -> nat,
      repr_partition uf.(parent) pmodel p * 
      Array.repr uf.(rank) rmodel.

  Definition repr_t {size} (x : t size) (p : partition size) : hprop :=
    repr_uf x p.

  Hint Extern 4 => intro : dest.
  Ltac myauto ::= 
    autounfold with repr dest in *; intros;
    simplify_goal; try typeclasses eauto with repr dest.

  Typeclasses eauto :=.

  Hint Extern 4 (exists _ : _, _) => econstructor : dest.
  Hint Constructors and or : dest.
  Hint Extern 0 (_ = _) => reflexivity : dest.
  Hint Extern 0 (_ <-> _) => reflexivity : dest.
  Hint Extern 0 (_ ==> _) => reflexivity : dest.
  Hint Extern 0 (_ <==> _) => reflexivity : dest.
  Lemma empty_split : empty ~> empty * empty.
  Proof. t. Qed.
  Hint Resolve empty_split : dest.

  Hint Unfold hprop_inj : dest.

  Hint Constructors repr : Ynot.
  Set Firstorder Solver auto.

  Definition make {size} : STsep __ (fun x : t size => repr_t x (fun i : fin size => i))%hprop.
  Proof. intros. refine (
    parents <- Array.create size (fun i => i) ;
    ranks <- Array.create size (fun i => 0%nat) <@> (Array.repr parents (fun i => i)) ;    
    {{Return {| parent := parents; rank := ranks |}}});
      unfold ptsto_any_tot, ptsto_any; t.

    unfold repr_t, repr_uf, repr_partition. t. 
    apply himp_pure'. intro. constructor; auto.
  Qed.

  Definition repr_eq {size} (f g : partition size) :=
    forall n : fin size, forall c, repr f n c <-> repr g n c.

  Instance repr_equiv size : Equivalence (@repr_eq size).
  Proof. constructor; reduce. 
    
    reflexivity. 
    
    symmetry. red in H. auto. 
    
    red in H, H0. rewrite H; auto.
  Qed.

  Context {size : nat}.

(* unfold model_partition, model_array, models_partition. t. *)
  
  Lemma repr_inj {x n c} : repr (size:=size) x n c -> forall {c'}, repr x n c' -> c = c'.
  Proof. induction 1; intros. depelim H0. myauto.
    rewrite H0 in H. myauto.

    depelim H2. rewrite H2 in H. myauto.
    rewrite H2 in H. myauto.
  Qed.

  Hint Unfold models_partition : repr.

  Lemma models_partition_repr {f p : partition size} : models_partition f p -> 
    forall i : fin size, repr f i (p i).
  Proof. myauto. Qed.
  Hint Resolve @models_partition_repr : repr.

  Lemma models_partition_f (f p : partition size) :
    models_partition f p -> forall i : fin size, p i = p (f i).
  Proof. 
    intros. pose (models_partition_repr H i).
    apply (repr_inj r).
    case (eq_fin_dec i (f i)). intros. rewrite e at 1. apply H. 
    intros. econstructor 2 with (f i); myauto. 
  Qed.
  Hint Resolve @models_partition_f : repr.

  Lemma repr_f_fi_not_i (f : partition size) (i : fin size) : 
    forall v, repr f i v -> repr f (f i) v.
  Proof. intros. induction H.

    rewrite H; myauto. myauto.
  Qed.

  Lemma repr_f_fi {f : representation size} {p : partition size} {i : fin size} : models_partition f p ->
    forall {v}, repr f (f i) v -> repr f i v.
  Proof. intros rfp v rfv. depind rfv.
    case (eq_fin_dec (f i) i) ; intros; auto.
    rewrite e. myauto. 
    econstructor 2 with (f i); myauto. 
    econstructor 2 with (f i); myauto.
  Qed. 

  Lemma repr_f_fi_eq {f : representation size} {i : fin size} : 
    forall {v}, repr f i v -> f v = v.
  Proof. intros. induction H. auto.
    subst j. auto.
  Qed.

  Ltac inst H :=
    match type of H with
      ?X -> _ => let H' := fresh in assert (H':X) by typeclasses eauto with repr; specialize (H H')
    end.

  Lemma repr_f_fi_eq' {f : representation size} {p : partition size} {i : fin size} : 
    models_partition f p ->
    repr f (f i) i -> f i = i.
  Proof. intros rfp rfi. 
    apply (repr_f_fi rfp) in rfi. depind rfi. auto.
    generalize (models_partition_repr rfp (f i)). intros.
    assert (Hi:=repr_inj rfi H). 
    pose (repr_f_fi_eq H). rewrite <- Hi in e. myauto.
  Qed.

  Lemma models_partition_f' {f : representation size} {p : partition size} : 
    models_partition f p -> forall {i : fin size}, f (p i) = p i.
  Proof.
    intros.
    red in H. apply (repr_f_fi_eq (i:=i)). myauto. 
  Qed.

  Infix "===>" := Morphisms.respectful (at level 90, right associativity).

  Class Have (P : Prop) := have : P.
  Hint Extern 0 (Have _) => unfold Have; auto with repr : typeclass_instances.

  Definition subset_eq {A} (R : relation A) (P : A -> Prop) : relation A :=
    fun x y => R x y /\ P x /\ P y.

  Instance subset_proper {A} (R : relation A) `(Reflexive A R) (P : A -> Prop) (x : A) (p : Have (P x)) : 
    Morphisms.Proper (subset_eq R P) x.
  Proof. reduce. intuition. Qed.

  Instance subset_proper_proxy {A} (R : relation A) `(Reflexive A R) (P : A -> Prop) (x : A) (p : Have (P x)) : 
    Morphisms.ProperProxy (subset_eq R P) x.
  Proof. reduce. intuition. Qed.

  Instance: Morphisms.Proper (repr_eq ===> eq ===> eq ===> iff) (@repr size).
  Proof. reduce. red in H. subst. apply H. Qed.
  
  Instance: Morphisms.Proper (repr_eq ===> 
    Morphisms.pointwise_relation (fin size) eq ===> iff) models_partition.
  Proof. reduce. red in H. unfold models_partition.
    split; intros. rewrite <- H0.
    now rewrite <- H. 

    rewrite H0. now rewrite H.
  Qed.

  Instance: RelationClasses.subrelation (Morphisms.pointwise_relation (fin size) eq) repr_eq.
  Proof. intros f g Hfg x y. 
    split. intros rf. induction rf. setoid_rewrite Hfg in H. constructor; auto.
    setoid_rewrite Hfg in H. constructor 2 with (g i) ; subst j; auto. 

    induction 1. setoid_rewrite <- Hfg in H. constructor; auto.
    setoid_rewrite <- Hfg in H. constructor 2 with (f i) ; subst j; auto.
  Qed. 

  Require Import Logic.FunctionalExtensionality.
  Lemma repr_model_refl f (i : fin size) : f i = i -> upd_model_fin f i i = f.
  Proof. intros. extensionality a. apply upd_model_refl; auto. Qed.

  Lemma repr_f_refl {f p} {i : fin size} : models_partition f p -> (f i = i <-> p i = i).
  Proof. intros rfp. split; intros H. 
    assert (H':=models_partition_repr rfp i). depelim H'; myauto.
    
    assert (H':=models_partition_repr rfp i). depelim H'; myauto. 
    rewrite <- H. apply models_partition_f'; auto.
  Qed.

  Lemma repr_f_refl_left {f p} : models_partition f p -> forall {i : fin size}, f i = i -> p i = i.
  Proof. intros. now rewrite <- (repr_f_refl H). Qed.

  Lemma repr_f_refl_right {f p} : models_partition f p -> forall {i : fin size}, p i = i -> f i = i.
  Proof. intros. now rewrite (repr_f_refl H). Qed.

  Lemma repr_eq_refl (i : fin size) x y : repr_eq x y -> x i = i -> y i = i.
  Proof. intros rxy xi. red in rxy. apply repr_zero in xi.
    rewrite rxy in xi. eapply repr_f_fi_eq; myauto. 
  Qed.
  
  Lemma repr_eq_succ {x y p} {i c : fin size} : models_partition x p -> repr_eq x y -> 
    repr x i c -> repr y i c.
  Proof. intros rfp rxy H. rewrite <- rxy. assumption. Qed.

  Lemma repr_canon {f} {i : fin size} {c p} : models_partition f p -> (repr f i c <-> p i = c).
  Proof. intros rfp. split; intros H. 
    apply (repr_inj (models_partition_repr rfp i) H). 
    pose (H':=models_partition_repr rfp i).
    now rewrite H in H'.
  Qed.

  Lemma repr_canon_right {x} {i : fin size} {c p} : models_partition x p -> repr x i c -> p i = c.
  Proof. intros. rewrite <- @repr_canon; eauto. Qed.

  Lemma repr_f_invol {f p} {i : fin size} : models_partition f p ->
    f i = i -> repr f i (f i).
  Proof. intros rfp fii. rewrite <- fii at 1. eapply repr_f_fi_not_i. rewrite fii. myauto. Qed.

  Hint Resolve @repr_f_fi_not_i : repr.
  Hint Resolve @repr_canon_right : repr.

  Lemma repr_elim {f p} (H : models_partition f p) 
    (P : forall n i, Prop)
    (Pzero : forall i : fin size, f i = i -> i = p i -> P i (p i))
    (Psucc : forall i : fin size, f i <> i -> i <> p i -> P (f i) (p i) -> P i (p i)) : 
    forall i c, repr f i c -> P i c.
  Proof.
    intros i c rf. assert (ri:=repr_inj (models_partition_repr H i) rf).
    rewrite <- ri in rf |- *. clear ri c.
    depind rf.
    apply Pzero; auto.
    apply Psucc; auto.
    pose (repr_f_refl (i:=i) H). destruct i0.
    intro. symmetry in H3. intuition.
    specialize (IHrf p H P Pzero Psucc).
    assert(Hpi:p i = p (f i)). apply models_partition_f; auto.
    specialize (IHrf Hpi).
    rewrite <- Hpi in IHrf.
    auto.
  Qed.

  Lemma models_partition_invol {f} {p : partition size} : models_partition f p -> forall {i}, p (p i) = p i.
  Proof. intros rfp i.
    assert (ri:=models_partition_repr rfp i). depind ri.
    rewrite <- x. auto.
    specialize (IHri p rfp).
    assert(Hpi:p i = p (f i)). apply models_partition_f; auto.
    specialize (IHri Hpi). rewrite <- Hpi in IHri. auto.
  Qed.

  Ltac upd_model_simpl :=
    unfold upd_model_fin; case eq_fin_dec; auto; intros; try discriminates; try contradictions.
  Hint Resolve @models_partition_f' : repr.

  Lemma models_partition_upd {f : representation size} {p : partition size} {n v} : 
    models_partition f p -> n <> f n -> repr f (f n) v -> models_partition (upd_model_fin f n v) p.
  Proof.
    intros fp nfn rfv. intro.
    eapply repr_f_fi in rfv; eauto.
    assert (hi:=repr_inj rfv (models_partition_repr fp n)). subst v.
    assert (r:=models_partition_repr fp x). remember (p x) as px. revert Heqpx.
    elim r using (repr_elim fp); auto with repr. 

    intros i fii ipi _.
    rewrite <- ipi. constructor; auto. 
    upd_model_simpl.

    intros i fii ipi H _.
    assert (Hpi:p i = p (f i)). auto with repr. specialize (H Hpi).
    case (eq_fin_dec i n). intros <-. 
    econstructor 2 with (p i); auto. upd_model_simpl.
    constructor; auto. upd_model_simpl. auto with repr. 

    intros.
    econstructor 2 with (f i); auto.
    upd_model_simpl. myauto.
  Qed.

  Lemma repr_upd_model (f : representation size) (p : partition size) (n v : fin size) : 
    models_partition f p -> 
    n <> f n ->
    repr f (f n) v -> 
    repr_eq f (upd_model_fin f n v).
  Proof. intros rfp nfn rfv. red; intros x c. 
    assert (rx':=models_partition_upd rfp nfn rfv x).
    split; intro H.
    assert(Hcp:=repr_inj (c':=c) (models_partition_repr rfp x) H). subst c. apply rx'.

    assert(Hcp:=repr_inj rx' H). subst c. auto with repr.
  Qed.

  Hint Resolve @models_partition_upd repr_upd_model : repr.

  Definition cast A (a : A) : A := a.

  Notation array := (Array.t (fin size) size).

  Definition find_post (a : array) (i : fin size) (f : fin size -> fin size) (p : partition size) (c : fin size) :=
    (repr_partition a f p * [p i = c])%hprop.

  Definition dest_pair {A B C : Type} (p : A * B) (cont : forall (a : A) (b : B), p = (a, b) -> C) : C.
  Proof. destruct p. eapply cont; auto. Defined.

  
  Definition find_aux (a : array) (i : fin size) (f : [representation size]) (p : [partition size]) : 
    STsep (f ~~ p ~~ repr_partition a f p) 
    (fun (res : fin size * [partition size]) => let (c, g) := res in
      f ~~ p ~~ g ~~ repr_partition a g p * [p i = c] * [repr_eq f g])%hprop.
  Proof. revert i f. 
    refine (Fix2
      (fun i f => f ~~ p ~~ repr_partition a f p)
      (fun i f (res : fin size * [partition size]) =>
        let (c, g) := res in f ~~ p ~~ g ~~ repr_partition a g p * [p i = c] * [repr_eq f g])%hprop
      (fun self i (f : [representation size]) =>
        pi <- Array.get a f i
        <@> (f ~~ p ~~ [models_partition f p]) ;
        if eq_fin_dec pi i then {{Return (i, f)}}
        else 
          res <- self pi f <@> (f ~~ p ~~ [f i = pi /\ pi <> i])%hprop ;
          let '(ci, g) := res in
            Array.set a g i ci <@> (f ~~ p ~~ g ~~ 
              [f i = pi /\ pi <> i /\ 
                repr f pi ci /\ models_partition f p /\ repr_eq f g])%hprop ;;
            {{Return (ci, (g ~~~ upd_model_fin g i ci))}}
          ));
    unfold find_post, repr_partition, models_partition; clear self; t. t.
    subst b.
    apply pair_equal in H0. destruct H0. subst a0.
    pack_injections. subst x1. t. apply himp_pure'.
    eauto with repr.

    apply himp_pure'. intuition auto. rewrite H0 at 1. apply H.
    rewrite H0. apply H.

    rename H3 into Hrepr. rename H5 into req. rename H2 into rci.
    apply pair_equal in H. destruct H; subst a1 b0.
    rewrite <- ! hiff_unpack. t. rewrite ! himp_pure2. apply himp_pure'.
    rewrite req at 1.
    change (models_partition x0 x1) in Hrepr.

    assert(x i <> i).
    intro.
    apply (repr_eq_refl i _ _ (symmetry req)) in H. congruence.
    assert(repr x (x i) ci).
    eapply repr_f_fi_not_i. rewrite <- req. eauto with repr.

    intuition auto with repr.

    rewrite req in Hrepr.
    intuition auto with repr.
    eapply repr_canon_right; eauto with repr.
    rewrite req in Hrepr.
    eapply repr_upd_model; eauto.
  Qed.

  Notation "inh ~~ p" := (hprop_unpack inh (fun inh => p%hprop)) (at level 91, right associativity) : hprop_scope.

  Axiom get_irr' : Π (T : Set) (p : T -> hprop),
  STsep (Exists x :@ T, p x) (fun x : [T] => x ~~ p x).

  Definition find (x : @t size) (p : [partition size]) (i : fin size) : 
    STsep (p ~~ repr_t x p) 
    (fun c : fin size => p ~~ repr_t x p * [p i = c]).
  Proof. unfold repr_t, repr_uf.
    refine 
      (pmodel <- get_irr' (representation size) _ ;
       rmodel <- get_irr' (fin size -> nat) _ ;
       x <- find_aux x.(parent) i pmodel p <@> (rmodel ~~ Array.repr x.(rank) rmodel) ;
       {{Return (fst x)}}); try solve [t]. intuition t.
  Qed.

  (* Definition find (a : array) (i : fin size) (f : [representation size]) (p : [partition size]) :  *)
  (*   STsep (f ~~ p ~~ repr_partition a f p)  *)
  (*   (fun res : (fin size * [representation size]), *)
  (*     let (c, g) := res in *)
  (*     (p ~~ g ~~ f ~~ repr_partition a g p * [p i = c /\ repr_eq f g]))%hprop. *)
  (* Proof. intros. refine ({{find_aux a i f p}}); t. t. Qed. *)
    
  Definition partition_union (p : partition size) (i j : fin size) (r : fin size) : partition size :=
    fun x => 
      if eq_fin_dec (p x) (p i) then r
      else if eq_fin_dec (p x) (p j) then r
      else p x.
 
  Lemma models_partition_union {f p} (i j : fin size) : models_partition f p -> p i <> p j ->
    models_partition (upd_model_fin f (p j) (p i)) (partition_union p i j (p i)).
  Proof.
    intros. red in H. intro. 
    generalize (H x). intros Hx.
    unfold upd_model_fin. unfold partition_union.
    depind Hx.
    case eq_fin_dec. intros. 
    case (eq_fin_dec i0 (p j)); intros. subst i0.
    rewrite <- e in H0. contradictions. rewrite <- e. 
    rewrite x at 1. constructor. case eq_fin_dec; auto. intros.
    auto with repr.
    
    intros. case eq_fin_dec. intros. rewrite <- x in e. subst i0.
    econstructor 2 with (p i); auto. case eq_fin_dec; auto.
    intros. discriminates. 
    constructor; auto. case eq_fin_dec. auto. intros. 
    auto with repr.
    
    intros. rewrite <- x. constructor. case eq_fin_dec; auto. intros.
    rewrite x in e. congruence.
    specialize (IHHx p i j H H0). 
    assert(p i0 = p (f i0)). auto with repr. specialize (IHHx H1).
    rewrite <- H1 in IHHx.
    case eq_fin_dec. intros. 
    econstructor 2 with (f i0). case eq_fin_dec. intros. subst i0.
    rewrite <- e. rewrite (models_partition_invol H). symmetry. auto with repr.
    intros. auto. auto.
    
    generalize IHHx. case eq_fin_dec. intros. auto. intros. contradictions.
    
    intros. revert IHHx.
    case eq_fin_dec. intros. contradictions.
    intros. revert IHHx. case eq_fin_dec. intros. 
    econstructor 2 with (f i0); auto. case eq_fin_dec; auto. intros.
    subst i0. 
    elim H2. symmetry. auto with repr.
    
    intros.
    econstructor 2 with (f i0); auto. 
    case eq_fin_dec. intros. subst i0. 
    elim n1. rewrite (models_partition_invol H). auto.
    intros.
    auto.
  Qed.

  Require Import Compare_dec.

  Lemma partition_union_sym (p : partition size) (i j : fin size) (c : fin size) : 
    Morphisms.pointwise_relation (fin size) eq (partition_union p i j c) (partition_union p j i c).
  Proof.
    unfold partition_union. intro. repeat case eq_fin_dec; intros; congruence.
  Qed.

  Lemma partition_union_idem (p : partition size) (i j : fin size) : p i = p j ->
    Morphisms.pointwise_relation (fin size) eq p (partition_union p i j (p i)).
  Proof. 
    unfold partition_union. intros H x. repeat case eq_fin_dec; intros; congruence.
  Qed.

  Lemma partition_eq_union (p : partition size) (i j : fin size) : p i = p j ->
    partition_eq p (partition_union p i j (p i)).
  Proof.
    intros. unfold partition_union. red.
    intros. repeat case eq_fin_dec; simpl_dep_elim; split; congruence.
  Qed.

  Lemma partition_eq_union_union (p : partition size) (i j : fin size) : 
    partition_eq (partition_union p i j (p j)) (partition_union p i j (p i)).
  Proof.
    intros. unfold partition_union. red.
    intros. repeat case eq_fin_dec; simpl_dep_elim; split; congruence.
  Qed.

  Definition union_aux (x : @t size) (i j : fin size) (f : [representation size]) (r : [fin size -> nat])
    (p : [partition size]) :
    STsep (f ~~ r ~~ p ~~ repr_partition x.(parent) f p * Array.repr x.(rank) r)
    (fun res : ([representation size * partition size * (fin size -> nat)])%type =>
      res ~~ let 'pair (pair g p') r' := res in
        p ~~ 
        repr_partition x.(parent) g p' * 
        Array.repr x.(rank) r' *
        [partition_eq p' (partition_union p i j (p i))]).
  Proof.
    destruct x as [pars ranks]. simpl.
    refine (cip <- find_aux pars i f p <@> (r ~~ Array.repr ranks r) ;
      dest_pair cip (fun ci g prf =>
      cjp <- find_aux pars j g p <@> (p ~~ r ~~ [p i = ci] * Array.repr ranks r) ;
      dest_pair cjp (fun cj g' prf' =>
        if eq_fin_dec ci cj then {{Return (inhabit_unpack3 g' p r (fun g' p r => (g', p, r)))}}
        else (
          rci <- Array.get ranks r ci <@> 
          (g' ~~ p ~~ Array.repr pars g' * [models_partition g' p /\ p i = ci /\ p j = cj /\ ci <> cj]) ;
          rcj <- Array.get ranks r cj <@> (g' ~~ p ~~ r ~~
            Array.repr pars g' * [rci = r ci /\ models_partition g' p /\ p i = ci /\ p j = cj /\ ci <> cj]) ;
          match nat_compare rci rcj as comp return comp = nat_compare rci rcj -> _ with
          | Lt => fun prf =>
            (Array.set pars g' cj ci <@> 
              (g' ~~ p ~~ r ~~
                Array.repr ranks r * [rci = r ci /\ rcj = r cj /\
                  models_partition g' p /\ p i = ci /\ p j = cj /\ ci <> cj]) ;;
            {{Return (inhabit_unpack3 g' p r (fun g' p r => 
              (upd_model_fin g' cj ci, (partition_union p i j (p i)), r)))}})
          | Gt => fun prf =>
            (Array.set pars g' ci cj <@>
              (g' ~~ p ~~ r ~~
                Array.repr ranks r * [rci = r ci /\ rcj = r cj /\ 
                  models_partition g' p /\ p i = ci /\ p j = cj /\ ci <> cj]) ;;
              {{Return (inhabit_unpack3 g' p r (fun g' p r =>
                (upd_model_fin g' ci cj, (partition_union p i j (p j)), r)))}})
          | Eq => fun prf =>
            (Array.set ranks r ci (S rci) <@> 
              (g' ~~ p ~~ r ~~
                Array.repr pars g' * [rci = r ci /\ rcj = r cj /\ 
                  models_partition g' p /\ p i = ci /\ p j = cj /\ ci <> cj]) ;;
            Array.set pars g' cj ci <@> 
              (g' ~~ p ~~ r ~~
                Array.repr ranks (upd_model_fin r ci (S rci)) * [rci = r ci /\ rcj = r cj /\ 
                  models_partition g' p /\ p i = ci /\ p j = cj /\ ci <> cj]) ;;
            {{Return (inhabit_unpack3 g' p r (fun g' p r =>
              (upd_model_fin g' cj ci, (partition_union p i j (p i)), upd_model_fin r ci (S rci))))}})
          end eq_refl
          )))); unfold repr_partition; t;
    repeat match goal with 
      H : (_, _) = (_, _) |- _ => apply pair_equal in H; destruct H
    end;
    sep ltac:fail ltac:(auto using @partition_eq_union, @models_partition_union).

    rewrite himp_pure2.
    apply himp_pure'. split.  
    rewrite partition_union_sym.
    apply models_partition_union; auto.
    apply partition_eq_union_union.
  Qed.

  Definition union (x : @t size) (p : [partition size]) (i j : fin size) : 
    STsep (p ~~ repr_t x p) 
    (fun p' : [partition size] => p' ~~ p ~~ 
      repr_t x p' * [partition_eq p' (partition_union p i j (p i))]).
  Proof. intros. unfold repr_t. unfold repr_uf.
    refine (pmodel <- get_irr' _ _ ;
      rmodel <- get_irr' _ _ ;
      x <- union_aux x i j pmodel rmodel p <@> _ ;
      {{Return (x ~~~ let 'pair (pair p'model p') r' := x in
        p')}}); t.
  Qed.

End UnionFind.

Module Type UF.
  Parameter t : nat -> Type.
  Parameter repr : forall {size}, t size -> partition size -> hprop.
  
  Parameter create : Π size : nat, STsep emp (fun x : t size => repr x (fun i => i)).

  Parameter union : Π {size : nat} (x : t size) (p : [partition size]) (i j : fin size),
    STsep (p ~~ repr x p) 
      (fun p' : [partition size] => 
        p ~~ p' ~~ repr x p' * [partition_eq p' (partition_union p i j (p i))]).

  Parameter find : Π {size : nat} (x : t size) (p : [partition size]) (i : fin size),
    STsep (p ~~ repr x p) 
      (fun ci => p ~~ repr x p * [ci = p i]).

End UF.
  
Module UFArray <: UF.

  Definition t (n : nat) := @t n.

  Definition repr {size} (uf : t size) (p : partition size) : hprop :=
    repr_t uf p.
  
  Definition create : Π size : nat, STsep emp (fun x : t size => repr x (fun i => i)).
  Proof. intros. refine make. Defined.

  Definition union : Π {size : nat} (x : t size) (p : [partition size]) (i j : fin size),
    STsep (p ~~ repr x p) 
      (fun p' : [partition size] => p ~~ p' ~~
        repr x p' * [partition_eq p' (partition_union p i j (p i))]).
  Proof. intros. refine {{union x p i j}}; t. Qed.
    
  Definition find : Π {size : nat} (x : t size) (p : [partition size]) (i : fin size),
    STsep (p ~~ repr x p) 
      (fun ci => p ~~ repr x p * [ci = p i]).
  Proof. intros. refine {{find x p i}}; t. Qed.

End UFArray.
