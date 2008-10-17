Require Import List.

Require Import Ynot.

Set Implicit Arguments.

Open Local Scope hprop_scope.


Module Type QUEUE.
  Parameter t : Set -> Set.
  Parameter rep : forall T, t T -> list T -> hprop.

  Parameter new : forall T,
    STsep __ (fun q : t T => rep q nil).
  Parameter free : forall T (q : t T),
    STsep (rep q nil) (fun _ : unit => __).

  Parameter enqueue : forall T (q : t T) (x : T) (ls : [list T]),
    STsep (ls ~~ rep q ls) (fun _ : unit => ls ~~ rep q (ls ++ x :: nil)).
  Parameter dequeue : forall T (q : t T) (ls : [list T]),
    STsep (ls ~~ rep q ls) (fun xo => ls ~~ match xo with
                                              | None => [ls = nil] * rep q ls
                                              | Some x =>
                                                match ls with
                                                  | nil => [False]
                                                  | x' :: ls' => [x' = x] * rep q ls'
                                                end
                                            end).
End QUEUE.

Module Queue : QUEUE.
  Section Queue.
    Variable T : Set.

    Record node : Set := Node {
      data : T;
      next : option ptr
    }.
    
    Fixpoint listRep (ls : list T) (hd tl : ptr) {struct ls} : hprop :=
      match ls with
        | nil => [hd = tl]
        | h :: t => Exists p :@ ptr, hd --> Node h (Some p) * listRep t p tl
      end.

    Record queue : Set := Queue {
      front : ptr;
      back : ptr
    }.

    Definition rep' ls fr ba :=
      match fr, ba with
        | None, None => [ls = nil]
        | Some fr, Some ba => Exists ls' :@ list T, Exists x :@ T,
          [ls = ls' ++ x :: nil] * listRep ls' fr ba * ba --> Node x None
        | _, _ => [False]
      end.
          
    Definition rep q ls := (Exists fr :@ option ptr, Exists ba :@ option ptr,
      front q --> fr * back q --> ba * rep' ls fr ba).

    Ltac simplr := repeat (try congruence;
      match goal with
        | [ x : option ptr |- _ ] => destruct x
        | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intro; subst
        | [ H : next _ = _ |- _ ] => rewrite H
        | [ H : nil = ?ls ++ _ :: nil |- _ ] => destruct ls; discriminate
          
        | [ |- __ ==> match ?O with
                        | Some _ => [False]
                        | None => [nil = nil]
                      end ] => equate O (@None ptr)

        | [ |- _ ==> match ?O with
                       | Some _ => _
                       | None => match ?O' with
                                   | Some _ => _
                                   | None => [nil = nil]
                                 end
                     end ] => equate O (@None ptr); equate O' (@None ptr)
      end);
    try match goal with
          | [ ls' : list T |- _ ] =>
            match goal with
              | [ |- context[ ([_ :: _ = ls' ++ _ :: nil] * listRep ls' _ _) ] ] => destruct ls'
            end
        end.

    Ltac t := unfold rep, rep'; sep simplr.
    
    Open Scope stsepi_scope.

    Definition new : STsep __ (fun q => rep q nil).
      refine (fr <- New (@None ptr);
        
        ba <- New (@None ptr);
          
        {{Return (Queue fr ba)}}); t.
    Qed.

    Definition free : forall q, STsep (rep q nil) (fun _ : unit => __).
      intros; refine (Free (front q);;
        
        {{Free (back q)}}); t.
    Qed.

    Lemma push_listRep : forall ba x nd ls fr,
      ba --> Node x (Some nd) * listRep ls fr ba ==> listRep (ls ++ x :: nil) fr nd.
      Hint Resolve himp_comm_prem.

      induction ls; t.
    Qed.

    Hint Immediate push_listRep.

    Lemma push_nil : forall (x : T) nd,
      __ ==> [x :: nil = nil ++ x :: nil] * listRep nil nd nd.
      t.
    Qed.

    Hint Immediate push_nil.

    Definition enqueue : forall q x ls, STsep (ls ~~ rep q ls) (fun _ : unit => ls ~~ rep q (ls ++ x :: nil)).
      intros; refine (ba <- !back q;
      nd <- New (Node x None);
      back q ::= Some nd;;

      IfNull ba Then
        {{front q ::= Some nd}}
      Else    
        Assert (ls ~~ nd --> Node x None * back q --> Some nd
          * Exists ban :@ node, ba --> ban
            * Exists fr :@ ptr, front q --> Some fr
              * Exists ls' :@ list T, [ls = ls' ++ data ban :: nil]
                * listRep ls' fr ba * [next ban = None]);;

        ban <- !ba;
        ba ::= Node (data ban) (Some nd);;
        {{Return tt}}); t.
    Qed.

    Lemma add_empty : forall p,
      p ==> p * __.
      t.
    Qed.

    Hint Immediate add_empty.

    Definition dequeue : forall q ls,
      STsep (ls ~~ rep q ls) (fun xo => ls ~~ match xo with
                                                | None => [ls = nil] * rep q ls
                                                | Some x =>
                                                  match ls with
                                                    | nil => [False]
                                                    | x' :: ls' => [x' = x] * rep q ls'
                                                  end
                                              end).
      intros; refine (fr <- !front q;

        IfNull fr Then
          {{Return None}}
        Else
          Assert (ls ~~ front q --> Some fr
            * Exists nd :@ node, fr --> nd
              * Exists ba :@ ptr, back q --> Some ba
                * Exists ls' :@ list T, [ls = data nd :: ls']
                * match next nd with
                    | None => [ls' = nil]
                    | Some nnd' => Exists ls'' :@ list T, Exists l :@ T,
                      [ls' = ls'' ++ l :: nil] * listRep ls'' nnd' ba * ba --> Node l None
                  end);;

          nd <- !fr;
          Free fr;;
          front q ::= next nd;;

          IfNull next nd As nnd Then
            back q ::= None;;
            {{Return (Some (data nd))}}
          Else    
            {{Return (Some (data nd))}});
      solve [ t | hdestruct ls; t ].
    Qed.
  End Queue.

  Definition t (_ : Set) := queue.
End Queue.
