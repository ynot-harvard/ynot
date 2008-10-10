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
    
    Open Local Scope stsep_scope.

    Definition new : STsep __ (fun q => rep q nil).
      refine (fr <- New (@None ptr);
        
        ba <- New (@None ptr) <@> _;
          
        {{Return (Queue fr ba) <@> _}}); t.
    Qed.

    Definition free : forall q, STsep (rep q nil) (fun _ : unit => __)%hprop.
      intros; refine (Free (front q) :@ _ <@> _;;
        
        {{Free (back q) :@ _}}); t.
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
      
      nd <- New (Node x None) <@> (ls ~~ Exists fr :@ option ptr,
        front q --> fr * back q --> ba * rep' ls fr ba)%hprop;
        
      back q ::= Some nd <@> (ls ~~ Exists fr :@ option ptr,
        nd --> Node x None * front q --> fr * rep' ls fr ba)%hprop;;

      match ba return STsep (ls ~~ Exists fr :@ option ptr,
          nd --> Node x None * front q --> fr * back q --> Some nd * rep' ls fr ba)%hprop
          (fun _ : unit => ls ~~ rep q (ls ++ x :: nil))%hprop with
        | None =>
          {{front q ::= Some nd <@> (ls ~~ Exists fr :@ option ptr,
            nd --> Node x None * back q --> Some nd * rep' ls fr None)}}%hprop
      
        | Some ba =>
          ban <- ba ! (fun ban => ls ~~ Exists fr :@ ptr,
            nd --> Node x None * front q --> Some fr * back q --> Some nd
            * Exists ls' :@ list T,
            [ls = ls' ++ data ban :: nil] * listRep ls' fr ba * [next ban = None])%hprop;
          
          ba ::= Node (data ban) (Some nd) <@> (ls ~~ Exists fr :@ ptr,
            nd --> Node x None * front q --> Some fr * back q --> Some nd
            * Exists ls' :@ list T,
            [ls = ls' ++ data ban :: nil] * listRep ls' fr ba * [next ban = None])%hprop;;

          {{Return tt <@> (ls ~~ Exists fr :@ ptr,
            front q --> Some fr * nd --> Node x None * back q --> Some nd * ba --> Node (data ban) (Some nd)
            * Exists ls' :@ list T,
            [ls = ls' ++ data ban :: nil] * listRep ls' fr ba * [next ban = None])}}%hprop
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
      intros; refine (fr <- front q ! (fun fr => ls ~~ Exists ba :@ option ptr,
        back q --> ba * rep' ls fr ba)%hprop;

        match fr return STsep (ls ~~ Exists ba :@ option ptr,
          front q --> fr * back q --> ba * rep' ls fr ba)%hprop
          (fun xo => ls ~~ match xo with
                             | None => [ls = nil] * rep q ls
                             | Some x =>
                               match ls with
                                 | nil => [False]
                                 | x' :: ls' => [x' = x] * rep q ls'
                               end
                           end)%hprop with
          | None => {{Return None <@>
            (ls ~~ [ls = nil] * front q --> None * back q --> None)}}%hprop
          | Some fr =>
            nd <- fr ! (fun nd => ls ~~ Exists ba :@ ptr,
              front q --> Some fr * back q --> Some ba
              * match ls with
                  | nil => [False]
                  | x :: ls' => [data nd = x]
                    * match next nd with
                        | None => [ls' = nil]
                        | Some nnd => Exists ls'' :@ list T, Exists l :@ T,
                          [ls' = ls'' ++ l :: nil] * listRep ls'' nnd ba * ba --> Node l None
                      end
                end)%hprop;

            Free fr :@ _ <@> (ls ~~ Exists ba :@ ptr,
              front q --> Some fr * back q --> Some ba
              * match ls with
                  | nil => [False]
                  | x :: ls' => [data nd = x]
                    * match next nd with
                        | None => [ls' = nil]
                        | Some nnd => Exists ls'' :@ list T, Exists l :@ T,
                          [ls' = ls'' ++ l :: nil] * listRep ls'' nnd ba * ba --> Node l None
                      end
                end)%hprop;;

            front q ::= next nd <@> (ls ~~ Exists ba :@ ptr,
              back q --> Some ba
              * match ls with
                  | nil => [False]
                  | x :: ls' => [data nd = x]
                    * match next nd with
                        | None => [ls' = nil]
                        | Some nnd => Exists ls'' :@ list T, Exists l :@ T,
                          [ls' = ls'' ++ l :: nil] * listRep ls'' nnd ba * ba --> Node l None
                      end
                end)%hprop;;

            match next nd as nnd return STsep (ls ~~ Exists ba :@ ptr,
              front q --> nnd * back q --> Some ba
              * match ls with
                  | nil => [False]
                  | x :: ls' => [data nd = x]
                    * match nnd with
                        | None => [ls' = nil]
                        | Some nnd' => Exists ls'' :@ list T, Exists l :@ T,
                          [ls' = ls'' ++ l :: nil] * listRep ls'' nnd' ba * ba --> Node l None
                      end
                end)%hprop
              (fun xo => ls ~~ match xo with
                                 | None => [ls = nil] * rep q ls
                                 | Some x =>
                                   match ls with
                                     | nil => [False]
                                     | x' :: ls' => [x' = x] * rep q ls'
                                   end
                               end)%hprop with
              | None =>
                back q ::= None <@> (ls ~~ [ls = data nd :: nil] * front q --> None)%hprop;;

                {{Return (Some (data nd)) <@> (ls ~~ [ls = data nd :: nil] * front q --> None * back q --> None)%hprop}}
                
              | Some nnd =>
                {{Return (Some (data nd)) <@> (ls ~~ Exists ba :@ ptr,
                  front q --> Some nnd * back q --> Some ba
                  * match ls with
                      | nil => [False]
                      | x :: ls' => [data nd = x] * Exists ls'' :@ list T, Exists l :@ T,
                          [ls' = ls'' ++ l :: nil] * listRep ls'' nnd ba * ba --> Node l None
                    end)}}%hprop
            end
        end); solve [ t | hdestruct ls; t ].
    Qed.
  End Queue.

  Definition t (_ : Set) := queue.
End Queue.
