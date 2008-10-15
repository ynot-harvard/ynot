(**
Interface to Omega decision procedure:
   - Defining data types for Presburger formulae
   - Pretty print them to format that the Omega Calculator understands
   - Call Omega and get back results.
*)

(* Arithmetic expression *)

open List
open Util

type ident = string

let liftQuantifiers = ref true
let removeUniQuants = ref false

type presForm = 
    Less of aExp * aExp
  | Leq of aExp * aExp
  | Eq of aExp * aExp
  | And of presForm * presForm
  | Or of presForm * presForm
  | Not of presForm
  | Forall of ident * presForm
  | Exists of ident * presForm

and aExp = 
    Const of int
  | Var of ident
  | Mult of int * aExp
  | Add of aExp * aExp    
  | Minus of aExp * aExp

and bKind = 
  | F
  | E

let flipQuant q = match q with
  | F -> E
  | E -> F

let flipQuants qs = List.map (fun (q, i) -> (flipQuant q, i)) qs

let rec aExpToString (ae : aExp) : string = match ae with
  | Const c -> string_of_int c
  | Var v -> Util.replace_dot_with_uscore v
  | Mult (c, ae1) ->  (string_of_int c) ^ (aExpToString ae1)
  | Add (ae1, ae2) -> (aExpToString ae1) ^ "+" ^ (aExpToString ae2)
  | Minus (ae1, ae2) -> (aExpToString ae1) ^ "-" ^ (aExpToString ae2)


let rec presFormToStringHelper (pe :presForm) : string = match pe with
  | Less (ae1, ae2) -> (aExpToString ae1) ^ "<" ^ (aExpToString ae2)
  | Leq (ae1, ae2) -> (aExpToString ae1) ^ "<=" ^ (aExpToString ae2)
  | Eq (ae1, ae2) -> (aExpToString ae1) ^ "=" ^ (aExpToString ae2)
  | And (pe1, pe2) -> 
      let ps1 = presFormToStringHelper pe1 in
      let ps2 = presFormToStringHelper pe2 in
	"(" ^ ps1 ^ ") and (" ^ ps2 ^ ")"
  | Or (pe1, pe2)  -> 
      let ps1 = presFormToStringHelper pe1 in
      let ps2 = presFormToStringHelper pe2 in
	"(" ^ ps1 ^ ") or (" ^ ps2 ^ ")"
  | Not pe1 -> 
      let ps1 = presFormToStringHelper pe1 in
	"not (" ^ ps1 ^ ")"
  | Forall (v, pe1) -> 
      let ps1 = presFormToStringHelper pe1 in
	"(forall " ^ (Util.replace_dot_with_uscore v) ^ ":" ^ ps1 ^ ")"

  | Exists (v, pe1) -> 
      let ps1 = presFormToStringHelper pe1 in
	"(exists " ^ (Util.replace_dot_with_uscore v) ^ ":" ^ ps1 ^ ")"

(*
  print to Omega Calculator format, with all quantifiers lifted out
*)
let rec presFormToStringHelperLift (pe :presForm) : (string * (bKind * ident) list) = match pe with
  | Less (ae1, ae2) -> ((aExpToString ae1) ^ "<" ^ (aExpToString ae2), [])
  | Leq (ae1, ae2) -> ((aExpToString ae1) ^ "<=" ^ (aExpToString ae2), [])
  | Eq (ae1, ae2) -> ((aExpToString ae1) ^ "=" ^ (aExpToString ae2), [])
  | And (pe1, pe2) -> 
      let (ps1, qvars1) = presFormToStringHelperLift pe1 in
      let (ps2, qvars2) = presFormToStringHelperLift pe2 in
	("(" ^ ps1 ^ ") and (" ^ ps2 ^ ")", qvars1 @ qvars2)
  | Or (pe1, pe2)  -> 
      let (ps1, qvars1) = presFormToStringHelperLift pe1 in
      let (ps2, qvars2) = presFormToStringHelperLift pe2 in
	("(" ^ ps1 ^ ") or (" ^ ps2 ^ ")", qvars1 @ qvars2)
  | Not pe1 -> 
      let (ps1, qvars1) = presFormToStringHelperLift pe1 in
	("not (" ^ ps1 ^ ")", flipQuants qvars1)
  | Forall (v, pe1) -> 
      let (ps1, qvars1) = presFormToStringHelperLift pe1 in
	(ps1, (F, Util.replace_dot_with_uscore v)::qvars1)
  | Exists (v, pe1) -> 
      let (ps1, qvars1) = presFormToStringHelperLift pe1 in
	(ps1, (E, Util.replace_dot_with_uscore v)::qvars1)

let presFormToString (pe : presForm) : string =
  if not !liftQuantifiers then
    presFormToStringHelper pe
  else
    let (ps, qvars) = presFormToStringHelperLift pe in
    let helper (bder, var) s = match bder with
      | F ->
	  if !removeUniQuants then
	    s 
	  else
	    "(forall " ^ var ^ ":" ^ s ^ ")" 
      | E -> "(exists " ^ var ^ ":" ^ s ^ ")" 
    in
      List.fold_right helper qvars ps


let rec getVarsAExp (ae : aExp) = match ae with
  | Const _ -> []
  | Var v -> [v]
  | Mult (c, ae1) -> getVarsAExp ae1
  | Add (ae1, ae2) -> append (getVarsAExp ae1) (getVarsAExp ae2)
  | Minus (ae1, ae2) -> append (getVarsAExp ae1) (getVarsAExp ae2)



let rec getVarsPresForm pe = match pe with
  | Less (ae1, ae2) -> append (getVarsAExp ae1) (getVarsAExp ae2)
  | Leq (ae1, ae2) -> append (getVarsAExp ae1) (getVarsAExp ae2)
  | Eq (ae1, ae2) -> append (getVarsAExp ae1) (getVarsAExp ae2)
  | And (pe1, pe2) -> append (getVarsPresForm pe1) (getVarsPresForm pe2)
  | Or (pe1, pe2) -> append (getVarsPresForm pe1) (getVarsPresForm pe2)
  | Not pe1 -> getVarsPresForm pe1
  | Forall (v, pe1) -> 
      if !liftQuantifiers && !removeUniQuants then
	getVarsPresForm pe1
      else
	filter (fun vv -> vv != v) (getVarsPresForm pe1)
  | Exists (v, pe1) -> filter (fun vv -> vv != v) (getVarsPresForm pe1)


let rec varsToString vars = match vars with
  | [] -> ""
  | [v] -> Util.replace_dot_with_uscore v
  | v :: vs -> (Util.replace_dot_with_uscore v) ^ ", " ^ varsToString vs


let presFormToOmega (pe : presForm) = 
  let fstr = presFormToString pe in
  let vstr = varsToString (remove_dups (getVarsPresForm pe))
  in
  "{[" ^ vstr ^ "] : " ^ fstr ^ "}"


let presFormTrue = Less (Const 0, Const 1)
let presFormFalse = Less (Const 1, Const 0)
let imply pf1 pf2 = Or ( Not pf1, pf2)


(*
   Call Omega Calculator, send input to it
*)

let infilename = "input.oc"
let resultfilename = "result.txt"

(*
let isBreakable c = 
  if (Char.uppercase(c) >= 'A' && Char.uppercase(c) <= 'Z') || (c >= '0' && c <= '9') || c = '_' then
    false
  else
    true
*)

let isBreakable c =  match c with
  | '(' | ')' | ' ' | '+' | ':' -> true
  | _ -> false

let breakLines (input : string) : string =
  let buf = Buffer.create 4096 in
  let i = ref 0 in
  let cnt = ref 0 in
  let l = String.length input in
    while !i < l do
      Buffer.add_char buf input.[!i];
      cnt := !cnt + 1;
      if !cnt > 80 && (isBreakable input.[!i]) then
	begin
	  Buffer.add_char buf '\n';
	  cnt := 0
	end;
      i := !i + 1
    done;
    Buffer.contents buf

let runOmegaCalc (input : string) : unit = 
  begin
    let omegacalc = "oc" in (* expect omega calculator executable 'oc' to be on path *)
    let chn = open_out infilename in
    output_string chn (breakLines input);
    close_out chn;
    ignore (Sys.command (omegacalc ^ " " ^ infilename ^ " > " ^ resultfilename));
  end
  

(*
   Use Omega Calculator to test if a formula is valid -- some other
   tool may probably be used ... 
*)

let omegaIsValid (pe : presForm) : bool =
  begin
    let fstr = presFormToString pe in
    let vstr = varsToString (remove_dups ("MAXC" :: getVarsPresForm pe)) in
    let truestr = "{[" ^ vstr ^ "]: MAXC>=0 }" in
    let fomega =  truestr ^ " subset {[" ^ vstr ^ "] : MAXC>=0 and (" ^ fstr ^ ")}" ^ ";\n" in
    runOmegaCalc fomega;
    let chn = open_in resultfilename in
    let quitloop = ref false in
    let result = ref false in
    while not !quitloop do
      let line = input_line chn in
      if String.length line != 0 then 
	if line.[0] != '#' then
	  begin
	    quitloop := true;
	    if line = "True" || line = "{ TRUE }" then
	      result := true
	    else if line = "False" || line = "{ FALSE }" then
	      result := false
	  end;
    done;
    !result
  end


(*--------------------------------------------------
  LASH
  --------------------------------------------------*)

let specialVar = "zzzz"
let specialVarUsed = ref false

let rec aExpToLash (ae : aExp) : string = match ae with
  | Const c -> string_of_int c
  | Var v -> Util.replace_dot_with_uscore v
  | Mult (c, ae1) ->  (string_of_int c) ^ "*" ^ (aExpToLash ae1)
  | Add (ae1, ae2) -> (aExpToLash ae1) ^ "+" ^ (aExpToLash ae2)
  | Minus (ae1, ae2) -> (aExpToLash ae1) ^ "-" ^ (aExpToLash ae2)


let constFold compfunc ae1 ae2 = match ae1 with
  | Const c1 ->
      begin
	match ae2 with
	  | Const c2 ->
	      if compfunc c1 c2 then
		Some true
	      else
		Some false
	  | _ -> None
      end
  | _ -> None

let aeStr (compfunc : int -> int -> bool) ae1 ae2 (op : string) = match constFold compfunc ae1 ae2 with
  | None -> (aExpToLash ae1) ^ op ^ (aExpToLash ae2)
  | Some b -> 
      if b then
	begin
	  specialVarUsed := true;
	  specialVar ^ "=" ^ specialVar
	end
      else
	begin
	  specialVarUsed := true;
	  specialVar ^ "<" ^ specialVar
	end

let rec presFormToLashHelper (pe :presForm) : (string * (bKind * ident) list) = match pe with
  | Less (ae1, ae2) -> (aeStr (<) ae1 ae2 "<", [])
  | Leq (ae1, ae2) -> (aeStr (<=) ae1 ae2 "<=", [])
  | Eq (ae1, ae2) -> (aeStr (=) ae1 ae2 "=", [])
  | And (pe1, pe2) -> 
      let (ps1, qvars1) = presFormToLashHelper pe1 in
      let (ps2, qvars2) = presFormToLashHelper pe2 in
	("(" ^ ps1 ^ ") AND (" ^ ps2 ^ ")", qvars1 @ qvars2)
  | Or (pe1, pe2)  -> 
      let (ps1, qvars1) = presFormToLashHelper pe1 in
      let (ps2, qvars2) = presFormToLashHelper pe2 in
	("(" ^ ps1 ^ ") OR (" ^ ps2 ^ ")", qvars1 @ qvars2)
  | Not pe1 -> 
      let (ps1, qvars1) = presFormToLashHelper pe1 in
	("NOT (" ^ ps1 ^ ")", qvars1)
  | Forall (v, pe1) -> 
      let (ps1, qvars1) = presFormToLashHelper pe1 in
	(*
	  (ps1, (F, Util.replace_dot_with_uscore v)::qvars1)
	*)
	("(FORALL (" ^ (Util.replace_dot_with_uscore v) ^ ":" ^ ps1, [])
  | Exists (v, pe1) -> 
      let (ps1, qvars1) = presFormToLashHelper pe1 in
	(*
	  (ps1, (E, Util.replace_dot_with_uscore v)::qvars1)
	*)
	("(EXISTS (" ^ (Util.replace_dot_with_uscore v) ^ ":" ^ ps1, [])

let presFormToLash (pe : presForm) : string =
  let (ps, qvars) = presFormToLashHelper pe in
    (*
      ps
    *)
  let helper (bder, var) s = match bder with
    | F -> "(FORALL (" ^ var ^ ":" ^ s ^ "))"
    | E -> "(EXISTS (" ^ var ^ ":" ^ s ^ "))" in
  let ps1 = "( (NOT (MAXC >=0)) OR (" ^ ps ^ "))" in 
    if !specialVarUsed then
      "FORALL (MAXC: (FORALL (" ^ specialVar ^ ":" ^ (List.fold_right helper qvars ps1) ^ ")))"
    else
      "FORALL (MAXC: (" ^ (List.fold_right helper qvars ps1) ^ "))"


let lashinfile = "input.lash"
let lashoutput = "result.lash"

let runLash (input : string) : unit = 
  begin
    let lash = "presburger" in (* expect omega calculator executable 'oc' to be on path *)
    let chn = open_out lashinfile in
      output_string chn (breakLines input);
      close_out chn;
      ignore (Sys.command (lash ^ " " ^ lashinfile ^ " > " ^ lashoutput));
  end


let keystr = "Number of solutions  : 0."
let kstrl = String.length keystr

(* let keystr2 = "Number of NDD states : 1." *)
(* let kstrl2 = String.length keystr2 *)

let lashIsUnsatisfiable (pe : presForm) : bool =
  begin
    let fstr = presFormToLash pe in
    runLash fstr;
    let chn = open_in lashoutput in
      begin
	try
	  let line1 = input_line chn in
	    if String.length line1 >= kstrl && String.sub line1 0 kstrl = keystr then
	      true (* no solution, unsatisfiable *)
	    else
	      false (* satisfiable *)
	with
	  | _ -> failwith "presburger:lashIsUnsatisfiable: can't read output from lash"
      end
  end

(*
let lashIsValid (pe : presForm) : bool = 
  let npe = Not pe in
    if lashIsUnsatisfiable npe then
      true
    else
      false
*)

(* --------------------
   Testing
   -------------------- *)



let ae1 = Add (Mult (3, Var "x"), Mult (5, Var "y"))
let ae2 = Const 10
let ae3 = Const 15

let pe1 = Less (ae1, ae2)
let pe2 = Forall ("x", pe1)
let pe3 = imply (Less (ae1, ae2)) (Less (ae1, ae3))

(*
let _ = print_string (presFormToOmega presFormTrue ^ "\n")
let _ = print_string (presFormToOmega presFormFalse ^ "\n")
*)


let f = imply pe1 pe1

(* let _ = print_string ((string_of_bool (omegaIsValid presFormFalse)) ^ "\n") *)

(* 
let _ = print_string ((string_of_bool (omegaIsValid (imply pe1 pe1))) ^ "\n")
let _ = print_string ((string_of_bool (omegaIsValid (imply pe2 pe2))) ^ "\n")
let _ = print_string ((string_of_bool (omegaIsValid pe3)) ^ "\n")
let _ = print_string ((string_of_bool (omegaIsValid pe2)) ^ "\n")
*)
