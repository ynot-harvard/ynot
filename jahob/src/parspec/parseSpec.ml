(** Parsing interface for Jahob specifications from {!Specs}.

  TODO: make it resilient wrt. parsing errors *)

open Specs

let parse_specs (s : string) : Specs.spec list =
  try
    let buff = Lexing.from_string s in
      ParsingSpecAux.input := Some s;
      ParsingSpecAux.buffer := Some buff;
      Debug.msg ("About to lex+parse: " ^ s);
      let res = YaccSpec.main LexSpec.token buff in
	Debug.msg (" -- done parsing.\n");
	res
  with Failure msg1 -> 
    (Util.warn (msg1 ^ " while parsing specification '" ^ s ^ ", returning empty.\n"); 
     [])

let parse_spec (s : string) : Specs.spec =
  match parse_specs s with
    | [s] -> s
    | _ -> Util.fail ("Expacted exactly one spec while parsing " ^ s)

let parse_inv (msg : string) (s : string) : Specs.invariant_desc =
  match parse_specs s with
    | [Invariant f] -> f
    | _ -> Util.fail ("While parsing invariant '" ^ s ^ "'\n" ^ msg)

let parse_contract (msg : string) (s : string) 
    : (Form.form option * Form.form list option * Form.form option) =
  match parse_specs s with
    | [Contract c] -> (c.c_pre,c.c_mod,c.c_post)
    | _ -> Util.fail ("While parsing contract '" ^ s ^ "'\n" ^ msg)
  
let parse_modifier (msg : string) (s : string) : mod_kind = 
  match parse_specs s with
    | [Modifier m] -> m
    | _ -> Util.fail ("While parsing modifier '" ^ s ^ "'\n" ^ msg)
