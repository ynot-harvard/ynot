Require Import List.
Require Import Ynot.
Require Import Ascii.
Require Import Omega.
Require Import Eqdep.
Set Implicit Arguments.


(* The following section defines a type for generic, input streams with
 * operations for looking at the next character in the stream, advancing
 * the stream, getting the current position (relative to the start of the
 * stream), and seeking to a particular position in the stream.  The
 * intention is that parsers should be parameterized by a stream object
 * which could be the result of opening a file, or as shown below, could 
 * be a stream constructed from a string. *)
Section INSTREAM.
  Open Local Scope hprop_scope.

  (* get next element from the stream, but don't advance the stream *)
  Definition peek_t(elt:Set)(stream_elts : [list elt])(rep:nat -> hprop) := 
    forall (offset:[nat]),
       STsep (offset ~~ rep offset)
             (fun (eopt:Exc elt) => stream_elts ~~ offset ~~
               rep offset * [eopt = nth_error stream_elts offset]).

  (* get next element from the stream and advance *)
  Definition next_t(elt:Set)(stream_elts : [list elt])(rep:nat->hprop) := 
    forall (offset:[nat]),
      STsep (offset ~~ rep offset)
            (fun (eopt:Exc elt) => 
               stream_elts ~~ offset ~~
               rep (1 + offset) * [eopt = nth_error stream_elts offset]).

  (* return current position of the stream *)
  Definition position_t(elt:Set)(stream_elts : [list elt])(rep:nat->hprop) := 
    forall (offset:[nat]),
      STsep (offset ~~ rep offset)
            (fun (n:nat) => 
              offset ~~ rep offset * [n = offset]).

  (* seek to a particular position in the stream *)
  Definition seek_t(elt:Set)(stream_elts : [list elt])(rep:nat->hprop) := 
    forall (n:nat),
      STsep (Exists m :@ nat, rep m)%hprop
            (fun (_:unit) => rep n).

  (* destroy a stream -- or rather, the state backing it *)
  Definition close_t(elt:Set)(stream_elts : [list elt])(rep:nat->hprop) := 
      STsep (Exists m :@ nat, rep m)%hprop
            (fun (_:unit) => __).

  (* Notice that the stream is defined in an object style so that it
   * encapsulates any hidden state with a local "rep" predicate.
   * Notice also that we treat streams as being invariant with respect to
   * the list of elements they produce, and thus the stream_elts 
   * component, which is computationally irrelevant, is used to establish
   * the relationship between the values returned by the operations and
   * the underlying real list of elements. *)
  Record instream_t(elt:Set) : Type := mkInstream {
    stream_elts : [list elt] ;
    rep         : nat -> hprop ;
    peek        : peek_t stream_elts rep ; 
    next        : next_t stream_elts rep ; 
    position    : position_t stream_elts rep ;
    seek        : seek_t stream_elts rep ;
    close       : close_t stream_elts rep
  }.
End INSTREAM.

(* The following section shows how an instream_t object can be constructed
 * from a string.  The only (mutable) state we need for the object is a 
 * ref to hold the current offset in the string.  A better implementation
 * would be to blast the string into an array/vector and then we could index
 * into the array/vector using the ref.
 *)
Section STRING_INSTREAM.
  Require Import String.
  Open Local Scope stsep_scope.
  Open Local Scope hprop_scope.

  (* For string-streams, the internal state is just a ref to the current offset *)
  Definition string_rep(s:list ascii)(x:ptr)(n:nat) : hprop := (x --> n)%hprop.

  (* Question: why won't this repeat on all of the sub goals that are produced by 
   * sep auto? *)
  Ltac str := unfold string_rep ; repeat (progress (sep auto)).

  Definition string_peek(s:list ascii)(x:ptr) : peek_t (inhabits s)(string_rep s x).
    unfold peek_t.
    intros.
    refine (n <- (x !! (fun n => offset ~~ [n = offset]))%stsep;
            Return (nth_error s n) <@> (offset ~~ [n = offset] * string_rep s x n) @> _).
    str. str. str.
  Defined.

  Definition string_position(s:list ascii)(x:ptr) : position_t (inhabits s)(string_rep s x).
    unfold position_t.
    intros.
    refine (n <- x !! (fun n => offset ~~ [n = offset]);
            Return n <@> (offset ~~ [n = offset] * string_rep s x n) @> _).
    str. str. str.
  Defined.

  Definition string_seek(s:list ascii)(x:ptr) : seek_t (inhabits s)(string_rep s x).
    unfold seek_t.
    intros.
    refine ({{x ::= n}}).
    str. str.
  Defined.

  Definition string_next(s:list ascii)(x:ptr) : next_t (inhabits s)(string_rep s x).
    unfold next_t.
    intros.
    refine (n <- x !! (fun n => offset ~~ [n = offset]) ;
            x ::= 1 + n <@> (offset ~~ [n = offset]) ;;
            Return (nth_error s n) <@> (offset ~~ [n=offset] * string_rep s x (1+n)) @> _).
    str. str. str. str. str.
  Defined.

  Definition string_close(s:list ascii)(x:ptr) : close_t (inhabits s)(string_rep s x).
    unfold close_t.
    intros.
    refine ({{FreeT x :@ nat}}).
    str. str.
  Defined.

  (* Notice that this not only returns an instream_t object, with initial offset of 0,
   * but also establishes the connection between the real list of characters (s) and
   * the phantom list in the answer object (stream_elts ans).  So one should be able
   * to reason about the actions performed on the actual string.
   *)
  Definition instream_of_list_ascii(s:list ascii) : 
    STsep __ (fun ans:instream_t ascii =>
                rep ans 0 * 
                (hprop_unpack (stream_elts ans) (fun elts => [elts = s]))).
    intro s.
    refine (x <- New 0  ;
            Return (mkInstream (string_peek s x)
                               (string_next s x)
                               (string_position s x)
                               (string_seek s x)
                               (string_close s x)) <@> (x --> 0)%hprop @> _) ;
    str.
  Defined.

  Fixpoint string_to_list(s:string) : list ascii := 
    match s with
    | EmptyString => nil
    | String c cs => c :: (string_to_list cs)
    end.

  Definition instream_of_string(s:string) := instream_of_list_ascii(string_to_list s).
End STRING_INSTREAM.
