Require Import List.

Require Import Ynot.

Set Implicit Arguments.

Open Local Scope hprop_scope.


Module Type STACK.
  Parameter t : Set -> Set.
  Parameter rep : forall T, t T -> list T -> hprop.

  Parameter new : forall T,
    STsep __ (fun s : t T => rep s nil).
  Parameter free : forall T (s : t T),
    STsep (rep s nil) (fun _ : unit => __).

  Parameter push : forall T (s : t T) (x : T) (ls : [list T]),
    STsep (ls ~~ rep s ls) (fun _ : unit => ls ~~ rep s (x :: ls)).
  Parameter pop : forall T (s : t T) (ls : [list T]),
    STsep (ls ~~ rep s ls) (fun xo => ls ~~ match xo with
                                              | None => [ls = nil] * rep s ls
                                              | Some x => Exists ls' :@ list T, [ls = x :: ls'] * rep s ls'
                                            end).
End STACK.

Module Stack : STACK.
  Section Stack.
    Variable T : Set.

    Record node : Set := Node {
      data : T;
      next : option ptr
    }.
    
    Fixpoint listRep (ls : list T) (hd : option ptr) {struct ls} : hprop :=
      match ls with
        | nil => [hd = None]
        | h :: t => match hd with
                      | None => [False]
                      | Some hd => Exists p :@ option ptr, hd --> Node h p * listRep t p
                    end
      end%hprop.

    Definition stack := ptr.

    Definition rep q ls := (Exists po :@ option ptr, q --> po * listRep ls po)%hprop.

    Ltac simplr := try discriminate.

    Ltac t := unfold rep; sep simplr.
    
    Open Scope stsepi_scope.

    Definition new : STsep __ (fun s => rep s nil).
      refine {{New (@None ptr)}}; t.
    Qed.

    Definition free : forall s, STsep (rep s nil) (fun _ : unit => __).
      intros; refine {{Free s}}; t.
    Qed.

    Definition push : forall s x ls, STsep (ls ~~ rep s ls) (fun _ : unit => ls ~~ rep s (x :: ls)).
      intros; refine (hd <- !s;

        nd <- New (Node x hd);

        {{s ::= Some nd}}
      ); t.
    Qed.

    Definition pop : forall s ls,
      STsep (ls ~~ rep s ls) (fun xo => ls ~~ match xo with
                                                | None => [ls = nil] * rep s ls
                                                | Some x => Exists ls' :@ list T, [ls = x :: ls'] * rep s ls'
                                              end).
      intros; refine (hd <- !s;

        IfNull hd Then
          {{Return None}}
        Else
          Assert (ls ~~ Exists nd :@ node, hd --> nd
            * Exists ls' :@ list T, [ls = data nd :: ls']
            * s --> Some hd * listRep ls' (next nd));;

          nd <- !hd;

          Free hd;;

          s ::= next nd;;

          {{Return (Some (data nd))}});
      solve [ t | hdestruct ls; t].
    Qed.
  End Stack.

  Definition t (_ : Set) := stack.
End Stack.
