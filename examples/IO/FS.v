Require Import Ynot Basis.
Require Import IO.
Require Import List Ascii String.
Require Import RSep.

Set Implicit Arguments.

Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.

Inductive mode : Set := R | W.

Axiom axiom_fd_model : Set.
Definition fd_model := axiom_fd_model.

(** File Descriptors **)
Axiom axiom_File : fd_model -> list mode -> Set.
Definition File := axiom_File.

(** TODO: Should avoid this being an axiom **)
Axiom axiom_handle : forall (fm : fd_model) (ms : list mode),  File fm ms -> hprop.
Definition handle := axiom_handle.

(** TTY **)
Axiom axiom_TtyModel : fd_model.
Definition TtyModel := axiom_TtyModel.

Axiom axiom_stdout : File TtyModel (W :: nil).
Definition stdout := axiom_stdout.

Axiom axiom_stdin : File TtyModel (R :: nil).
Definition stdin := axiom_stdin.

(** Actions **)
Axiom axiom_Read : forall (fm : fd_model) (ms : list mode),  File fm ms -> option ascii -> Action.
Definition Read := axiom_Read.

Axiom axiom_Write : forall (fm : fd_model) (ms : list mode),  File fm ms -> ascii -> Action.
Definition Write := axiom_Write.

Axiom axiom_Flush : forall (fm : fd_model) (ms : list mode),  File fm ms -> Action.
Definition Flush := axiom_Flush.

Axiom axiom_Close : forall (fm : fd_model) (ms : list mode), File fm ms -> Action.
Definition Close := axiom_Close.

Theorem ro_readable : In R (R :: nil).
  simpl; tauto.
Qed.

Theorem wo_writeable : In W (W :: nil).
  simpl; tauto.
Qed.

Theorem rw_readable : In R (R :: W :: nil).
  simpl; tauto.
Qed.
Theorem rw_writeable : In W (R :: W :: nil).
  simpl; tauto.
Qed.

Theorem wr_readable : In R (W :: R :: nil).
  simpl; tauto.
Qed.
Theorem wr_writeable : In W (W :: R :: nil).
  simpl; tauto.
Qed.

(** Functions **)
Axiom axiom_read : forall (m : fd_model) (ms : list mode) (fd : File m ms) (tr : [Trace])
  (allow : In R ms),
  STsep (tr ~~ traced tr * handle fd)
        (fun chr:option ascii => tr ~~ traced (Read fd chr :: tr) * handle fd).
Definition read := axiom_read.

Axiom axiom_write : forall (m : fd_model) (ms : list mode) (fd : File m ms) (chr : ascii)
  (tr : [Trace]) (allow : In W ms),
  STsep (tr ~~ traced tr * handle fd)
        (fun _:unit => tr ~~ traced (Write fd chr :: tr) * handle fd).
Definition write := axiom_write.

Axiom axiom_flush : forall (m : fd_model) (ms : list mode) (fd : File m ms) (tr :[Trace])
  (allow : In W ms),
  STsep (tr ~~ traced tr * handle fd)
        (fun _:unit => tr ~~ traced (Flush fd :: tr) * handle fd).
Definition flush := axiom_flush.

Axiom axiom_close : forall (m : fd_model) (ms : list mode) (fd : File m ms),
  STsep (handle fd)
        (fun _:unit => __).
Definition close := axiom_close.

Axiom axiom_FileModel : string -> fd_model.
Definition FileModel := axiom_FileModel.

Axiom axiom_AccessibleFile : string -> Prop.
Definition AccessibleFile := axiom_AccessibleFile.

Axiom axiom_open : forall (ms : list mode) (path : string),
  STsep (__)
        (fun ofd:option (File (FileModel path) ms) => match ofd with
                                  | None => [~AccessibleFile path]
                                  | Some fd => handle fd * [AccessibleFile path]
                                end).
Definition open := axiom_open.

(** Derived Equations **)
Definition WroteString (m : fd_model) (ms : list mode) (fd : File m ms)
  (str : list ascii) : Trace :=
  map (fun c => Write fd c) (rev str).

Definition ReadString (m : fd_model) (ms : list mode) (fd : File m ms)
  (str : list ascii) (sentinal : ascii) : Trace :=
  match rev str with 
    | nil => Read fd None :: nil
    | a :: b => 
      if ascii_dec a sentinal then 
        map (fun c => Read fd (Some c)) (rev str)
      else
        Read fd None :: map (fun c => Read fd (Some c)) (rev str)
  end.

Definition ReadLine (m : fd_model) (ms : list mode) (fd : File m ms)
  (str : list ascii) : Trace := ReadString fd str "010"%char.  

Lemma ReadLine_Next : forall fm ms (fd : File fm ms) rm c rest,
  c <> "010"%char -> (ReadLine fd rm ++ Read fd (Some c) :: rest = ReadLine fd (c :: rm) ++ rest).
  unfold ReadLine, ReadString; simpl; intros.
  destruct (rev rm); simpl;
    match goal with
      | [ |- context [ascii_dec ?X "010"] ] => destruct (ascii_dec X "010"); try congruence; norm_list; auto
    end.
Qed.

(** TODO: Can make this type stronger **)
Definition readline : forall (fm : fd_model) (ms : list mode) (fd : File fm ms) (pf : In R ms)
  (tr : [Trace]),
  STsep (tr ~~ traced tr * handle fd)
        (fun str:list ascii => tr ~~ traced (ReadLine fd str ++ tr) * handle fd).
  intros; refine (
  Fix
    (fun tr => tr ~~ traced tr * handle fd)
    (fun tr r => tr ~~ traced (ReadLine fd r ++ tr) * handle fd)
    (fun self tr => 
      c' <- read fd _ _;
      match c' as c'' return c'' = c' -> _ with
        | None => fun _ => {{Return nil}}
        | Some c => fun _ =>
          if ascii_dec c "010" then
            {{Return (c :: nil)}}
          else
            rm <- self (tr ~~~ Read fd (Some c) :: tr) <@> _;
            {{Return (c :: rm)}}
      end (refl_equal _))
    tr); try clear self;
  solve [ assumption
        | rsep ltac:(subst; simpl; try rewrite ReadLine_Next) auto ].
Qed.

Definition writeline : forall (fm : fd_model) (ms : list mode) (fd : File fm ms) (str : list ascii)
  (pf : In W ms) (tr : [Trace]),
  STsep (tr ~~ traced tr * handle fd)
        (fun _:unit => tr ~~ traced (WroteString fd str ++ tr) * handle fd).
  intros; refine (
    Fix2 (fun str tr => tr ~~ traced tr * handle fd)
         (fun str tr (_:unit) => tr ~~ traced (WroteString fd str ++ tr) * handle fd)
         (fun self str tr =>
           match str as str 
             return STsep (tr ~~ traced tr * handle fd)
                          (fun (_:unit) => tr ~~ traced ((map (fun c => Write fd c) (rev str)) ++ tr) * handle fd) with
             | nil => {{Return tt}}
             | c :: cs => 
               write fd c tr pf;;
               {{self cs (tr ~~~ Write fd c :: tr)}}
           end)
         str tr);
  solve [ sep fail auto
        | sep fail auto; rewrite map_app; sep fail auto; norm_list; sep fail idtac ].
Qed.

(** ReadContents **)
Fixpoint ReadFile (fm : fd_model) (ms : list mode) (fd : File fm ms) (str : string) {struct str} : Trace :=
  match str with
    | EmptyString => Read fd None :: nil
    | String a b => (ReadFile fd b) ++ (Read fd (Some a) :: nil)
  end.

Definition readFile (fm : fd_model) (ms : list mode) (fd : File fm ms) (pf : In R ms) (tr : [Trace]) :
  STsep (tr ~~ traced tr * handle fd)
        (fun rt:string  => tr ~~ traced (ReadFile fd rt ++ tr) * handle fd).
  intros. refine (
    Fix (fun tr => tr ~~ traced tr * handle fd)
        (fun tr r => tr ~~ traced (ReadFile fd r ++ tr) * handle fd)
        (fun self tr => 
          c' <- read fd _ _;
          match c' as c'' return c'' = c' -> _ with
            | None => fun _ => {{ Return EmptyString }}
            | Some c => fun _ =>
              rm <- self (tr ~~~ Read fd (Some c) :: tr) <@> _;
              {{Return (String c rm)}}
          end (refl_equal _))
        tr); try clear self;
  solve [ assumption
        | rsep ltac:(subst; simpl) ltac:(norm_list; auto); rsep fail auto ].
Qed.

(**
Definition pipe (sfm tfm : fd_model) (sms tms : list mode) (src : File sfm sms) (trg : File tfm tms)
  (pfR : In R sms) (pfW : In W tms) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun 
**)

Definition ReadAll (fp : list mode) (fm : fd_model) (fd : File fm fp) strs :=
  ReadLine fd nil ++ (List.fold_right (fun str l => ReadLine fd (str2la str) ++ l) nil strs).

Definition ReadAs str strs : Prop := 
  str = List.fold_right (fun a b => String.append a b) EmptyString (rev strs).


Definition is_nil (T : Type) (l : list T) : {l = nil} + {l <> nil}.
destruct l. auto. pose (List.nil_cons). auto.
Qed.  

Lemma append_empty : forall s, s = append s "".
  induction s; simpl; auto. rewrite <- IHs. auto.
Qed.
Lemma sappend_comm : forall (a b c : string), (a ++ (b ++ c) = (a ++ b) ++ c)%string.
  intros; induction a; auto. simpl. rewrite IHa. auto.
Qed.

Lemma fold_append : forall l x,
  (fold_right (fun a b : string => a ++ b) "" l ++ x)%string =
  fold_right (fun a b : string => (a ++ b)%string) 
  (x ++ "")%string l.
  intros; induction l.
  simpl; rewrite <- append_empty; auto.
  rewrite <- append_empty in *. simpl. rewrite <- sappend_comm. rewrite IHl. trivial.
Qed.

Require Import RSep.

Definition readAll' (fp : list mode) (fm : fd_model) (fd : File fm fp) (pf : In R fp) (tr : [Trace]) :
  STsep (tr ~~ traced tr * handle fd)
        (fun res : (string * [list string]) =>
          tr ~~ hprop_unpack (snd res) (fun strs =>
            traced (ReadLine fd nil ++ (List.fold_right (fun str l => ReadLine fd (str2la str) ++ l) nil strs) ++ tr) *
            [fst res = List.fold_right (fun a b => String.append a b) EmptyString (rev strs)]) * handle fd).
  Hint Resolve fold_append.
  intros. refine (
    {{Fix2 (fun str strs => tr ~~ strs ~~
               traced ((List.fold_right (fun str l => ReadLine fd (str2la str) ++ l) nil strs) ++ tr) *
                  [str = List.fold_right (fun a b => String.append a b) EmptyString (rev strs)] * handle fd)
            (fun _ _ (res:string * [list string]) =>
              tr ~~ hprop_unpack (snd res) (fun strs =>
                traced (ReadLine fd nil ++ (List.fold_right (fun str l => ReadLine fd (str2la str) ++ l) nil strs) ++ tr) *
                  [fst res = List.fold_right (fun a b => String.append a b) EmptyString (rev strs)]) * handle fd)
            (fun self str strs =>
              x <- readline fd pf (inhabit_unpack2 strs tr (fun strs tr => (List.fold_right (fun str l => ReadLine fd (str2la str) ++ l) nil strs) ++ tr)) <@>  _;
              if is_nil x then
                {{Return (str,strs)}}
              else
                {{self (String.append str (la2str x)) (strs ~~~ (la2str x) :: strs)}}
            )
            ""%string [nil]%inhabited}}); try clear self;
  solve [ rsep fail auto
        | rsep fail auto; subst; norm_prod; rsep fail auto; simpl; norm_list; rewrite la2str_inv_str2la; rewrite fold_right_app; norm_list; rsep fail auto ].
Qed.

Definition readAll (fp : list mode) (fm : fd_model) (fd : File fm fp) (pf : In R fp) (tr : [Trace]) :
  STsep (tr ~~ traced tr * handle fd)
        (fun res : (string * [list string]) =>
          tr ~~ hprop_unpack (snd res) (fun strs =>
            traced (ReadAll fd strs ++ tr) * [ReadAs (fst res) strs]) * handle fd).
  refine readAll'.
Qed.

Require Export List.