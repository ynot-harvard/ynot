Require Import List.

Require Import Ynot.

Set Implicit Arguments.


Module Type QUEUE.
  Parameter t : Set -> Set.
  Parameter rep : forall T, t T -> list T -> hprop.

  Parameter new : forall T,
    STsep __ (fun q : t T => rep q nil).
  Parameter free : forall T (q : t T),
    STsep (rep q nil) (fun _ : unit => __)%hprop.

  Parameter enqueue : forall T (q : t T) (x : T) (ls : [list T]),
    STsep (ls ~~ rep q ls) (fun _ : unit => ls ~~ rep q (ls ++ x :: nil))%hprop.
  Parameter dequeue : forall T (q : t T) (ls : [list T]),
    STsep (ls ~~ rep q ls) (fun xo => ls ~~ match xo with
                                              | None => [ls = nil] * rep q ls
                                              | Some x =>
                                                match ls with
                                                  | nil => [False]
                                                  | x' :: ls' => [x' = x] * rep q ls'
                                                end
                                            end)%hprop.
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
      end%hprop.

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
      end%hprop.
          
    Definition rep q ls := (Exists fr :@ option ptr, Exists ba :@ option ptr,
      front q --> fr * back q --> ba * rep' ls fr ba)%hprop.

    Ltac simplr := repeat (try congruence;
      match goal with
        | [ x : option ptr |- _ ] => destruct x
        | [ H : nil = ?ls ++ _ :: nil |- _ ] => destruct ls; discriminate
          
        | [ |- __ ==> match ?O with
                        | Some _ => [False]
                        | None => [nil = nil]
                      end ] => equate O (@None ptr)
      end);
    try match goal with
          | [ ls' : list T |- _ ] =>
            match goal with
              | [ |- context[ ([_ :: _ = ls' ++ _ :: nil] * listRep ls' _ _)%hprop ] ] => destruct ls'
            end
        end.

    Ltac t := unfold rep, rep'; sep simplr.
    
    Open Scope stsepi_scope.

    Definition new : STsep __ (fun q => rep q nil).
      refine (fr <- New (@None ptr);
        
        ba <- New (@None ptr);
          
        {{Return (Queue fr ba)}}); t.
    Qed.

    Definition free : forall q, STsep (rep q nil) (fun _ : unit => __)%hprop.
      intros; refine (Free (front q) :@ _;;
        
        (Free (back q) :@ _ @> _)%stsep); t.
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

    Definition enqueue : forall q x ls, STsep (ls ~~ rep q ls) (fun _ : unit => ls ~~ rep q (ls ++ x :: nil))%hprop.
      intros; refine (ba <- back q ! _;
      
      nd <- New (Node x None);
        
      back q ::= Some nd;;

      match ba return STsep (ls ~~ Exists fr :@ option ptr,
          nd --> Node x None * front q --> fr * back q --> Some nd * rep' ls fr ba)%hprop
          _ with
        | None =>
          {{front q ::= Some nd}}%hprop
      
        | Some ba =>
          ban <- ba ! (fun ban => ls ~~ Exists fr :@ ptr,
            nd --> Node x None * front q --> Some fr * back q --> Some nd
            * Exists ls' :@ list T,
            [ls = ls' ++ data ban :: nil] * listRep ls' fr ba * [next ban = None])%hprop;
          
          ba ::= Node (data ban) (Some nd);;

          {{Return tt}}%hprop
       end); t.
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
                                              end)%hprop.
      intros; refine (fr <- front q ! _;

        match fr return STsep (ls ~~ Exists ba :@ option ptr,
          front q --> fr * back q --> ba * rep' ls fr ba)%hprop
        _ with
          | None => {{Return None}}%hprop
          | Some fr =>
            let spec frnt nd nnd := 
              (ls ~~ Exists ba :@ ptr,
                front q --> frnt * back q --> Some ba
                * Exists ls' :@ list T, [ls = data nd :: ls']
                  * match nnd with
                      | None => [ls' = nil]
                      | Some nnd' => Exists ls'' :@ list T, Exists l :@ T,
                        [ls' = ls'' ++ l :: nil] * listRep ls'' nnd' ba * ba --> Node l None
                    end)%hprop in

            nd <- fr ! (fun nd => spec (Some fr) nd (next nd));

            Free fr :@ _;;

            front q ::= next nd;;

            match next nd as nnd return STsep (spec nnd nd nnd) _ with
              | None =>
                back q ::= None;;

                {{Return (Some (data nd))}}
                
              | Some nnd =>
                {{Return (Some (data nd))}}
            end
        end); unfold_local; solve [ t | hdestruct ls; t ].
    Qed.
  End Queue.

  Definition t (_ : Set) := queue.
End Queue.
