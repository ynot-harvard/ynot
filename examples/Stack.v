Require Import List.

Require Import Ynot.

Set Implicit Arguments.


Module Type STACK.
  Parameter t : Set -> Set.
  Parameter rep : forall T, t T -> list T -> hprop.

  Parameter new : forall T,
    STsep __ (fun s : t T => rep s nil).
  Parameter free : forall T (s : t T),
    STsep (rep s nil) (fun _ : unit => __)%hprop.

  Parameter push : forall T (s : t T) (x : T) (ls : [list T]),
    STsep (ls ~~ rep s ls) (fun _ : unit => ls ~~ rep s (x :: ls))%hprop.
  Parameter pop : forall T (s : t T) (ls : [list T]),
    STsep (ls ~~ rep s ls) (fun xo => ls ~~ match xo with
                                              | None => [ls = nil] * rep s ls
                                              | Some x => Exists ls' :@ list T, [ls = x :: ls'] * rep s ls'
                                            end)%hprop.
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
    
    Open Local Scope stsep_scope.

    Definition new : STsep __ (fun s => rep s nil).
      refine {{New (@None ptr)}}; t.
    Qed.

    Definition free : forall s, STsep (rep s nil) (fun _ : unit => __)%hprop.
      intros; refine {{Free s :@ _}}; t.
    Qed.

    Definition push : forall s x ls, STsep (ls ~~ rep s ls) (fun _ : unit => ls ~~ rep s (x :: ls))%hprop.
      intros; refine (hd <- s ! _;

        nd <- New (Node x hd) <@> _;

        {{s ::= Some nd <@> _}}
      ); t.
    Qed.

    Definition pop : forall s ls,
      STsep (ls ~~ rep s ls) (fun xo => ls ~~ match xo with
                                                | None => [ls = nil] * rep s ls
                                                | Some x => Exists ls' :@ list T, [ls = x :: ls'] * rep s ls'
                                              end)%hprop.
      intros; refine (hd <- s ! (fun hd => ls ~~ listRep ls hd)%hprop;

        match hd return STsep (ls ~~ s --> hd * listRep ls hd)%hprop
          (fun xo => ls ~~ match xo with
                             | None => [ls = nil] * rep s ls
                             | Some x => Exists ls' :@ list T, [ls = x :: ls'] * rep s ls'
                           end)%hprop with
          | None =>
            {{Return None <@> (ls ~~ s --> None * listRep ls None)%hprop}}

          | Some hd' =>
            nd <- hd' ! (fun nd => ls ~~ Exists ls' :@ list T, [ls = data nd :: ls']
              * s --> Some hd' * listRep ls' (next nd))%hprop;

            Free hd' :@ node <@> (ls ~~ Exists ls' :@ list T, [ls = data nd :: ls']
              * s --> Some hd' * listRep ls' (next nd))%hprop;;

            s ::= next nd <@> (ls ~~ Exists ls' :@ list T, [ls = data nd :: ls']
              * listRep ls' (next nd))%hprop;;

            {{Return (Some (data nd)) <@> (ls ~~ Exists ls' :@ list T, [ls = data nd :: ls']
              * s --> next nd * listRep ls' (next nd))}}%hprop
        end); solve [ t | hdestruct ls; t ].
    Qed.
  End Stack.

  Definition t (_ : Set) := stack.
End Stack.
