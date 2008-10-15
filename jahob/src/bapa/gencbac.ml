
type baForm =
  | Union of baForm * baForm
  | Intersection of baForm * baForm
  | Setvar of int (** variable, given by its index *)
  | SetvarComp of int (** complement of a variable *)

type cbacForm = {
  cf_ba : baForm;  (** BA formula *)
  cf_card : int; (** cardinality of cf_ba, >= 0 *)
}

type solution = 
  | CaseAnalysis of solution * solution
  | Leaf of int

let rec string_of_ba_form (f : baForm) : string =
  match f with
    | Union(f1,f2) -> 
	"(" ^ string_of_ba_form f1 ^ " U " ^
	  string_of_ba_form f2 ^ ")"
    | Intersection(f1,f2) -> 
	"(" ^ string_of_ba_form f1 ^ " I " ^
	  string_of_ba_form f2 ^ ")"
    | Setvar i -> "s" ^ string_of_int i
    | SetvarComp i -> "s" ^ string_of_int i ^ "'"

let string_of_cbac_form (cbac : cbacForm) : string =
  "|" ^ string_of_ba_form cbac.cf_ba ^ "| = " ^ string_of_int cbac.cf_card

let string_of_cbac_forms (cbacs : cbacForm list) : string =
  String.concat "\n" (List.map string_of_cbac_form cbacs)

let rec sol_height (sol : solution) : int =
  match sol with
    | Leaf v -> 0
    | CaseAnalysis(s1,s2) -> 1 + max (sol_height s1) (sol_height s2)

let string_of_solution (sol : solution) : string =
  let rec str_of_path (k : int) (path : bool list) : string =
    match path with
      | [] -> ""
      | b::path1 -> 
	  let s = "s" ^ string_of_int k in
	  let sp = if b then s else s ^ "'" in
	    sp ^ str_of_path (k + 1) path1 in
  let rec str_of (path : bool list) (sol : solution) : string =
    match sol with
      | CaseAnalysis(s1,s2) -> 
	  str_of (false::path) s1 ^ 
	    str_of (true::path) s2
      | Leaf v -> 
	  if v = 0 then "" 
	  else str_of_path 0 path ^ " -> " ^ string_of_int v ^ "\n"
  in
    str_of [] sol

let rec random_solution (size : int) : solution =
  if size = 0 then Leaf (Random.int 2)
  else CaseAnalysis (random_solution (size - 1),
		     random_solution (size - 1))

let random_ba_formula (varno : int) : baForm =
  let rec ba_of_size (k : int) : baForm =
    if k <= 1 then 
      (if Random.int 2 = 0 then Setvar (Random.int varno)
       else SetvarComp (Random.int varno))
    else
      let k' = Random.int k in
      let f1 = ba_of_size k' in
      let f2 = ba_of_size (k - k' - 1) in
	if Random.int 2 = 0 then Union(f1,f2)
	else Intersection(f1,f2)
  in
    ba_of_size varno

let rec sum_of (sol : solution) : int =
  match sol with
    | Leaf v -> v
    | CaseAnalysis(s1, s2) -> sum_of s1 + sum_of s2

type three_valued = TrueBA | FalseBA | UnknownBA
let t_and v1 v2 =
  match v1,v2 with
    | FalseBA,_ -> FalseBA
    | _,FalseBA -> FalseBA
    | TrueBA,_ -> v2
    | _,TrueBA -> v1
    | UnknownBA,UnknownBA -> UnknownBA

let t_or v1 v2 =
  match v1,v2 with
    | TrueBA,_ -> TrueBA
    | _,TrueBA -> TrueBA
    | FalseBA,_ -> v2
    | _,FalseBA -> v1
    | UnknownBA,UnknownBA -> UnknownBA

let rec eval (pa : bool array) (varno : int) (f : baForm) : three_valued =
  match f with
    | Union(f1,f2) ->
	let f1v = eval pa varno f1 in
	  if f1v = TrueBA then TrueBA else (t_or f1v (eval pa varno f2))
    | Intersection(f1,f2) ->
	let f1v = eval pa varno f1 in
	  if f1v = FalseBA then FalseBA else (t_and f1v (eval pa varno f2))
    | Setvar i -> 
	(try match pa.(varno - i - 1) with
	   | true -> TrueBA
	   | false -> FalseBA
	 with Invalid_argument _ -> UnknownBA)
    | SetvarComp i -> 
	(try match pa.(varno - i - 1) with
	   | true -> FalseBA
	   | false -> TrueBA
	 with Invalid_argument _ -> UnknownBA)
	  
(** check if propositional formula is true under partial assignment *)
let evaluate_ba 
    (partial_assignment : bool list) 
    (varno : int) 
    (f : baForm) : three_valued =
  let pa = Array.of_list (List.rev partial_assignment) in
    eval pa varno f

let rec card_for (partial_assignment : bool list) (sol : solution) 
    (f : baForm)
    (varno : int) 
    : int =
  match evaluate_ba partial_assignment varno f with
    | TrueBA -> sum_of sol
    | FalseBA -> 0
    | UnknownBA ->
	(match sol with
	   | Leaf _ -> failwith "full assignment does not determine truth value?"
	   | CaseAnalysis(s1, s2) ->
	       card_for (false::partial_assignment) s1 f varno +
		 card_for (true::partial_assignment) s2 f varno)
      
let cardinality_of (f : baForm) (sol0 : solution) (varno : int) : int =
  card_for [] sol0 f varno

(** ba formulas that consist of each individual set variable, 
    for control purposes *)
let rec mk_control_bas (k : int) : baForm list =
  if k < 0 then []
  else Setvar k :: mk_control_bas (k - 1)

let random_cbac_formula (varno : int) : (cbacForm list * solution) =
  let rec gen_ba_forms (i : int) : baForm list =
    if i = 0 then []
    else random_ba_formula varno :: gen_ba_forms (i-1) in

  let ba_forms = gen_ba_forms varno (* @ mk_control_bas (varno-1) *) in

  let sol = random_solution varno in

  let cbac_rhs (f : baForm) : cbacForm =
    {cf_ba = f;
     cf_card = cardinality_of f sol varno} 
  in
  let cbacs = List.map cbac_rhs ba_forms in
(*
  let _ = print_string (string_of_cbac_forms cbacs ^ "\n") in
  let _ = print_string (string_of_solution sol ^ "\n") in
*)
    (cbacs, sol)

(* ------------------------------------------------------------ *)
(*  Invoking GLPK solver *)
(* ------------------------------------------------------------ *)

let infile k = "generated-" ^ string_of_int k ^ ".mod"
let maxinfile k s = "max-generated-" 
  ^ string_of_int k ^ "-" 
  ^ string_of_int s
  ^ ".mod"
let outfile k = "generated-" ^ string_of_int k ^ ".out"
let maxoutfile k s = "max-generated-" 
  ^ string_of_int k ^ "-"
  ^ string_of_int s 
  ^ ".out"
let solution_string = "Non-zero solutions:"

let rec find_max_rhs (current : int) (cbacs : cbacForm list) : int =
  match cbacs with
    | [] -> 1 + current
    | cbac::cbacs1 -> find_max_rhs (max current cbac.cf_card) cbacs1

let write_glpsol_mod (cbacs : cbacForm list) chn : unit =
  let varno = List.length cbacs in
  let varno1 = varno - 1 in
  let lots = 1 + find_max_rhs 1 cbacs in
  let wr s = output_string chn s 
  in 
  let rec bool_var_sum (base : string) (k : int) = 
    if k < 0 then wr ("b" ^ base)
    else (bool_var_sum (base ^ "0") (k - 1);
	  wr " + ";
	  bool_var_sum (base ^ "1") (k - 1)) 
  in
  let rec declare_vars (base : string) (k : int) = 
    if k < 0 then (wr ("var x" ^ base ^ ", integer, >= 0;\n");
		    wr ("var b" ^ base ^ ", binary;\n");
		    wr ("s.t. bDef" ^ base ^ ": x" ^ base ^ " <= " ^ 
			  string_of_int lots ^ " * b" ^ base ^ ";\n"))
    else (declare_vars (base ^ "0") (k - 1);
	  declare_vars (base ^ "1") (k - 1)) 
  in
  let rec compact_str_of_path (path : bool list) : string =
    match path with
      | [] -> ""
      | b::path1 -> (if b then "1" else "0") ^ compact_str_of_path path1
  in
  let rec wr_sum_of_satisfiables (f : baForm) (k : int) 
      (partial_assignment : bool list) : unit =
    let v = evaluate_ba partial_assignment varno f in
      match v with
      | FalseBA -> ()
      | _ ->
	  if k < 0 then 
	    (if v = UnknownBA then 
	       failwith "Complete assignment did not determine value in wr_sum_of_satisfiables"
	     else
	       wr ("+ x" ^ compact_str_of_path partial_assignment))
	  else (wr_sum_of_satisfiables f (k - 1) (false::partial_assignment);
		wr_sum_of_satisfiables f (k - 1) (true::partial_assignment))
  in
  let write_cbac (cbac : cbacForm) (k : int) : unit =
    wr ("\n /* " ^ string_of_cbac_form cbac ^ "*/\n");
    wr ("s.t. a" ^ string_of_int k ^ ": 0 ");
    wr_sum_of_satisfiables cbac.cf_ba varno1 [];
    wr (" = " ^ string_of_int cbac.cf_card ^ ";\n")
  in
  let rec write_cbacs (cbacs : cbacForm list) (k : int) : unit =
    match cbacs with
      | [] -> ()
      | cbac::cbacs1 ->
	  (write_cbac cbac k;
	   write_cbacs cbacs1 (k + 1))
  in
    begin
      wr ("/* Generated by gencbac to test CBAC formula minimal solution size "
	  ^ "vkuncak 2006/06/18 */");
      wr ("param m, integer, >= 0, default " ^ 
	    Printf.sprintf "%d" (List.length cbacs) ^ ";\n");
      declare_vars "" varno1;
      write_cbacs cbacs 0;
      wr "solve;\n";
      wr ("printf \"" ^ solution_string ^ "\\n\";");
      wr "printf \"%d\", "; 
      bool_var_sum "" varno1; 
      wr ";\n";
      wr "end;\n"
    end

let parse_output (fn : string) : int option = 
  let chn = open_in fn in
  let line = ref "" in
  let res = (ref None : int option ref) in
  begin
    (try 
       (line := input_line chn;
	while (!line <> solution_string) do
	  line := input_line chn
	done;
	res := Some (int_of_string (input_line chn)))
     with End_of_file -> ());
    close_in chn;
    !res
  end

let min_solution_size (cbacs : cbacForm list) : int option =
  let size = List.length cbacs in
  let chn = open_out (infile size) in
  let _ = write_glpsol_mod cbacs chn in
  let _ = close_out chn in
  let _ = Util.run_with_timeout 
    ("glpsol --math " ^ (infile size) ^ "> " ^ (outfile size)) 15 in
    parse_output (outfile size)

(* ------------------------------------------------------------ *)
(*  Top-level loop *)
(* ------------------------------------------------------------ *)

let _ = Random.self_init ()

let get_new_sample (varno : int) : int option =
  let (cbacs, sol) = random_cbac_formula varno in
    min_solution_size cbacs

let max_sol_size_monte_carlo (varno : int) (iterNo : int) : int =
  let rec iter (k : int) (currentMax : int) : int =
    if k <= 0 then currentMax
    else 
      match get_new_sample varno with
	| None -> 
	    (print_string ", !"; flush_all();
	     iter (k - 1) currentMax)
	| Some s -> 
	    (Printf.printf ", %d" s; flush_all();
	     if s > currentMax then
	       (Sys.command ("cp " ^ infile varno ^ " " ^ maxinfile varno s);
		Sys.command ("cp " ^ outfile varno ^ " " ^ maxoutfile varno s);
		iter (k - 1) s)
	     else 
	       iter (k - 1) currentMax)
  in
  let res = iter iterNo (-1) 
  in
    res

let print_from_to (minVars : int) (maxVars : int) : unit =
  let print_for (k : int) : unit =
    Printf.printf "Max size of min CBAC solution, %d variables" k;
    flush_all();
    let s = max_sol_size_monte_carlo k 2000 in
      Printf.printf " => %d\n" s
  in
  let rec print_all (k : int) : unit =
    if k <= maxVars then
      (print_for k;
       print_all (k + 1))
    else ()
  in
    print_all minVars

let _ = print_from_to 9 9
