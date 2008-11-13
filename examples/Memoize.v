Require Import Ynot.

Set Implicit Arguments.

Open Scope hprop_scope.
Open Scope stsepi_scope.

Module Type COMPARABLE.
  Parameter T : Set.
  Parameter eq_dec : forall (x y : T), {x = y} + {x <> y}.
End COMPARABLE.

Module Type MEMO.
  Parameter T : Set.

  Parameter t : forall (T' : T -> Set),
    hprop
    -> (forall x, T' x -> Prop)
    -> Set.

  Implicit Arguments t [T'].

  Parameter rep : forall (T' : T -> Set)
    (inv : hprop) (fpost : forall x, T' x -> Prop),
    t inv fpost -> hprop.

  Parameter create : forall (T' : T -> Set) (inv : hprop)
    (fpost : forall x, T' x -> Prop),
    (forall x, STsep inv (fun y : T' x => [fpost _ y] * inv))
    -> STsep __ (fun m : t inv fpost => rep m).

  Parameter funcOf : forall (T' : T -> Set) (inv : hprop)
    (fpost : forall x, T' x -> Prop)
    (m : t inv fpost),
    forall (x : T), STsep (rep m * inv) (fun y : T' x => [fpost _ y] * inv * rep m).
End MEMO.

Module Make (C : COMPARABLE) : MEMO with Definition T := C.T.
  Definition T := C.T.

  Section memo.
    Variable T' : T -> Set.

    Variable inv : hprop.
    Variable fpost : forall x, T' x -> Prop.

    Record table : Set := Table {
      cached : ptr;
      func : forall x, STsep inv (fun y : T' x => [fpost y] * inv)
    }.

    Definition rep (tab : table) :=
      Exists o :@ option (sigT T'),
      cached tab --> o
      * [match o with
           | None => True
           | Some p => fpost (projT2 p)
         end].

    Ltac t := unfold rep; unfold_local; inhabiter; canceler; sep fail ltac:(eauto).

    Definition create : (forall x, STsep inv (fun y : T' x => [fpost y] * inv))
      -> STsep __ (fun m : table => rep m).
      intro f; refine (o <- New None;
        {{Return (Table o f)}}); t.
    Qed.

    Lemma finish : forall (P : Prop),
      P
      -> __ ==> [P].
      t.
    Qed.

    Hint Resolve finish.

    Definition funcOf (m : table) (x : T)
      : STsep (rep m * inv) (fun y : T' x => [fpost y] * inv * rep m).
      intros; refine (cache <- !(cached m);
        IfNull cache Then
          y <- func m x <@> _;
          cached m ::= Some (existT _ x y);;
          {{Return y}}
        Else
          Assert (cached m --> Some cache * [fpost (projT2 cache)] * inv);;
          match C.eq_dec (projT1 cache) x with
            | left pf => match pf in (_ = x) return STsep _ (fun y : T' x => [fpost y] * inv * rep m) with
                           | refl_equal => {{Return (projT2 cache)}}
                         end
            | right _ =>
              y <- func m x <@> _;
              cached m ::= Some (existT _ x y);;
              {{Return y}}
          end); t.
    Qed.

  End memo.

  Definition t := table.
End Make.
