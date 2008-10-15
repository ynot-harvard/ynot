(** Interface to formula parser. *)

let parsing_debug = ref false

let (dummy_formula : Form.form) = Form.Var "unparsableFormula"
let (dummy_type_formula : Form.typeForm) = Form.TypeApp (Form.TypeUnit, [])

(** {!ParseForm.parse_formula} and {!ParseForm.parse_type} prepend special strings to 
   enable {!YaccForm.main} to effectively 
   parse multiple different top-level non-terminals. *)

let parse_formula (s0 : string) : Form.form =
  try
  let s = s0 in
  let buff = Lexing.from_string s in begin
    ParsingFormAux.input := Some s;
    ParsingFormAux.buffer := Some buff;
    (if !parsing_debug then Debug.msg ("About to lex+parse: " ^ s) else ());
    let res = YaccForm.main LexForm.token buff in
    (if !parsing_debug then Debug.msg (" -- done.\n") else ());
    match res with
    | Form.AForm f -> f
    | _ -> (Util.warn ("Expected a formula while parsing '" ^ s ^ "'.");
	    dummy_formula)
  end
  with 
      Parsing.Parse_error -> 
	(Util.warn ("Syntax error while parsing formula '" ^ s0 ^ "'");
	 dummy_formula)
    | Failure msg -> 
	(Util.warn (msg ^ " while parsing formula '" ^ s0 ^ "'");
	 dummy_formula)

let parse_type (s0 : string) : Form.typeForm =
  try
  let s = ":" ^ s0 in (* prepend string with special character *)
  let buff = Lexing.from_string s in begin
    ParsingFormAux.input := Some s;
    ParsingFormAux.buffer := Some buff;
    (if !parsing_debug then Debug.msg ("About to lex+parse: " ^ s) else ());
    let res = YaccForm.main LexForm.token buff in
    (if !parsing_debug then Debug.msg (" -- done.\n") else ());
    match res with
    | Form.AType f -> f
    | _ -> (Util.warn ("Expected a type while parsing type '" ^ s ^ "'.");
	    dummy_type_formula)
  end
  with Failure msg -> 
    (Util.warn (msg ^ " while parsing '" ^ s0 ^ "'");
     dummy_type_formula)

let parse_formula_list (s0 : string) : Form.form list =
  try
  let s = s0 in
  let buff = Lexing.from_string s in begin
    ParsingFormAux.input := Some s;
    ParsingFormAux.buffer := Some buff;
    (if !parsing_debug then Debug.msg ("About to lex+parse: " ^ s) else ());
    let res = YaccForm.main LexForm.token buff in
    (if !parsing_debug then Debug.msg (" -- done.\n") else ());
    match res with
    | Form.AFormList fl -> fl
    | _ -> (Util.warn ("Expected a formula list while parsing '" ^ s ^ "'.");
	    [])
  end
  with Failure msg -> 
    (Util.warn (msg ^ " while parsing formula list '" ^ s0 ^ "'");
    [])
