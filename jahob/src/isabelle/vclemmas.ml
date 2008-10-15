(** Lemma caching for {!Isabelle} module.
    Enables reading previously proved lemmas from files.
    Implements some lemma matching that allows using
    stronger lemmas to prove weaker ones. *)

open Form

let known_facts = ref ([] : (string * form) list)
let add_fact s = 
  known_facts := s :: !known_facts

let get_content fname =
  if Sys.file_exists fname then
    let chn = open_in fname in
    let len = in_channel_length chn in
    let str = String.make len ' ' in
    let _ = really_input chn str 0 len in
    (close_in chn; str)
  else
    (Debug.msg ("No lemma file " ^ fname);
    "")

let init mod_name = 
  let lemma_file_name = mod_name ^ "-lemmas" ^ ".thy" in
  let str = get_content lemma_file_name in
  let lemmaKW = Str.regexp_string "lemma" in
  let quote = Str.regexp_string "\"" in
  let pos = ref 0 in
  let skip_to descr r =
    let oldpos = !pos in
    try pos := Str.search_forward r str !pos + 1
    with Not_found -> 
      (Util.msg (Printf.sprintf "End of file while searching for %s at position %d.\n" descr oldpos); raise Not_found)
  in 
  let skip_one () = pos := !pos + 1 in
  begin
    (try
      skip_to "lemma keyword" lemmaKW; (* the file name ;) *)
      while true do
        skip_to "lemma keyword" lemmaKW;        
        skip_to "openning quote" quote;
        let pos1 = !pos in
        skip_to "closing quote" quote;
        (let s1 = String.sub str pos1 (!pos-pos1-1) in
         add_fact (s1, ParseForm.parse_formula s1))
      done
    with Not_found -> ());
    Util.msg (Printf.sprintf "Retrieved %d lemmas from lemma file %s.\n" (List.length !known_facts) lemma_file_name);
    (* List.iter (fun s -> print_string (s ^ "\n\n")) !known_facts *)
  end

let buzzneq (f,g) =
  (Debug.msg "\nNOTE:\n";
   Debug.msg (PrintForm.string_of_form f);
   Debug.msg "\n    APPARENTLY NOT SAME AS:    \n";
   Debug.msg (PrintForm.string_of_form g ^ "\n");
   false)

let rec same f g = match (f,g) with
| (App(Const Comment, [Const (StringConst c);f1]),g) -> same f1 g
| (f, App(Const Comment, [Const (StringConst c);g1])) -> same f g1
| (TypedForm(f1,t1),g) -> same f1 g
| (f,TypedForm(g1,t1)) -> same f g1
| (_,_) when impl f g && impl g f -> true
| (App(Const Eq,[f1;f2]),App(Const Eq,[g1;g2])) ->
    (same f1 g1 && same f2 g2) ||
    (same f1 g2 && same f2 g1)
| (App(f1,fs),App(g1,gs)) -> same f1 g1 && same_all fs gs
| (Binder(bf,_,f1),Binder(bg,_,g1)) when bf=bg -> same f1 g1
| (f1,g1) when f1=g1 -> true
| _ -> buzzneq(f,g)
and same_all fs gs = match (fs,gs) with
| ([],[]) -> true
| (f1::fs1,g1::gs1) -> same f1 g1 && same_all fs1 gs1
| _ -> false
and impl f g = begin
match (f,g) with
| (App(Const MetaImpl,[f1;f2]),App(Const MetaImpl,[g1;g2])) ->
   impl f2 g2 && impl g1 f1
| (f,App(Const MetaImpl,[g1;g2])) -> impl f g2
| (f,App(Const MetaAnd,gs)) -> List.for_all (impl f) gs
| (f,App(Const And,gs)) -> List.for_all (impl f) gs
| (App(Const Or,fs),g) -> List.for_all (fun f0 -> impl f0 g) fs
| (App(Const MetaAnd,fs),g) -> List.exists (fun f0 -> impl f0 g) fs 
| (App(Const And,fs),g) -> List.exists (fun f0 -> impl f0 g) fs 
| (f,App(Const Or,gs)) -> List.exists (impl f) gs
| (App(Const Comment, [Const (StringConst c);f1]),g) -> impl f1 g
| (f, App(Const Comment, [Const (StringConst c);g1])) -> impl f g1
| (TypedForm(f1,t1),g) -> impl f1 g
| (f,TypedForm(g1,t1)) -> impl f g1
| (Binder(bf,_,f1),Binder(bg,_,g1)) when bf=bg -> impl f1 g1
      (* all binders assumed monotonic, although lambda is not used *)
| (App(Const Eq,[f1;f2]),App(Const Eq,[g1;g2])) ->
    (same f1 g1 && same f2 g2) ||
    (same f1 g2 && same f2 g1)
| (App(f1,fs),App(g1,gs)) -> same f1 g1 && same_all fs gs
| (f1,g1) when f1=g1 -> true
| (_,_) -> buzzneq(f,g)
end

let implied (lemma_str, lemma) (assumption_str, assumption) = 
  begin
(*
  Util.msg "VERIFYING IMPLICATION:\n";
  Util.msg ("\"" ^ assumption_str ^ "\"\n");
  Util.msg "    ==>?    \n";  
  Util.msg ("\"" ^ lemma_str ^ "\"\n");
*)
    let res_sem = impl assumption lemma in
(*
    let _ = if res_sem then Util.msg "YES, implied!\n\n"
                       else Util.msg "NO, NOT implied!\n" in
*)
    let res_syn = (lemma_str = assumption_str) in
(*
    let _ = if res_syn then Util.msg "SYNTACTICALLY IDENTICAL.\n\n"
                       else Util.msg "SYNTACTICALLY NOT IDENTICAL.\n\n" in
    let _ = if res_syn && (not res_sem) then 
               Util.msg "ALAS, SEMANTIC LOSES TO SYNTAX!\n" 
            else () in
*)
    (res_syn || res_sem)
  end  

let known_fact ((lemma_str,lemma) : string * form) : bool = 
  try
    let (cached_str, _) = 
      List.find (implied (lemma_str,lemma)) !known_facts in
    Util.msg ("\nMatched known lemma:\n" ^ cached_str ^ "\n\n");
    true
  with Not_found ->
    false
