

Require Import List.
Require Import Ynot.

Set Implicit Arguments.

Module Type LIST.
  Variable value_t : Set.
End LIST.


(*********************************************)
(* The functional model -- linked lists      *)
(*********************************************)
Module LinkedList(L : LIST).

  Definition list_t := list L.value_t.

  Definition tail(l : list_t) : list_t :=
    match l with
      | nil => nil
      | _ :: l => l
    end.
      

End LinkedList.

(*********************************************)
(* The interface -- linked lists             *)
(*********************************************)


(***************************************************)
(* The implementation -- encapsulated linked lists *)
(***************************************************)
Module RefLinkedList(List:LIST).
  Module L  := List.
  Module LL := LinkedList(L).

  Definition llist_t := ptr.

  Open Local Scope stsep_scope.
  Open Local Scope hprop_scope.

  Definition rep (l : llist_t) (l' : LL.list_t) : hprop  := (l --> l').

  (** new :: () -> LinkedList T
   ** Create a new linked list.
   **)
  Definition new : STsep __ (fun (ans:llist_t) => rep ans nil) :=
    New nil.

  (** free :: LinkedList T -> ()
   ** Delete the linked list.
   **)
  Definition free(this : llist_t) :
      STsep (Exists l :@ LL.list_t, rep this l) (fun (_:unit) => __) :=
    FreeT this :@ LL.list_t.

  (** cons :: LinkedList T -> T -> ?? -> ()
   ** Add an element to the beginning of the list.
   **)
  Definition cons(this : llist_t) (v : L.value_t) (P : LL.list_t -> hprop) :
      STsep (Exists l :@ LL.list_t, rep this l * P l) 
            (fun (_:unit) => Exists l :@ LL.list_t, rep this (v :: l) * P l).
    intros.
    refine (l <- this !! P ;
            this ::= (v :: l) <@> (P l) @> _); sep auto.
    Defined.

  (** tail :: LinkedList T -> ?? -> ()
   ** Remove the first element in the list.
   **)
  Definition tail(this : llist_t) (P : LL.list_t -> hprop) :
    STsep (Exists l :@ LL.list_t, rep this l * P l)
          (fun (_:unit) => Exists l :@ LL.list_t, rep this (LL.tail l) * P l).
    intros;
    refine (l <- this !! P ;
            this ::= LL.tail l <@> (P l) @> _); sep auto.
    Defined.

End RefLinkedList.


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-R" "../src" "Ynot" "-R" "/Users/greg/Devel/ynot/coq/adam/examples" "Examples") ***
*** End: ***
*).