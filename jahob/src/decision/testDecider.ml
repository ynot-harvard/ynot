open Form
open FormUtil
open PrintForm
open TypeReconstruct

let get_sequent seq_string =
  let seq0 = ParseForm.parse_formula seq_string in
  let seq, env = reconstruct_types [] seq0 in
  let sequent = sequent_of_form seq
  in (sequent, env)

let prompt = "Enter a sequent followed by \";;\":\n"

let read_seq_string () =
  let eos = ref 0 in
  let b = Buffer.create 1000 in
  while !eos < 3 do
    let chr = input_char stdin in
    if chr = ';' then
      if !eos < 2 then eos := !eos + 1
      else eos := 0
    else if chr = '\n' && !eos = 2 then 
      eos := !eos + 1
    else eos := 0;
    Buffer.add_char b chr
  done;
  Buffer.sub b 0 (Buffer.length b - 3)

let exc_to_bool (prover : string) (f : 'a -> bool) (x : 'a) : bool =
  try (f x) with 
    | Failure s -> 
	(Util.warn ("Prover '" ^ prover ^ "' failed with error " ^ s ^ ".\n");
	 false)
    | ex -> 
	(Util.warn ("Prover '" ^ prover ^ "' failed with unknown exception.\n");
	 raise ex; false)

let eval seq_string k = 
  try 
    let seq, env = get_sequent seq_string in
    let sqob = {sqob_pos = Common.unknown_pos; 
		sqob_purpose = "testDecider"; 
		sqob_sq = seq}
    in
    let start_time = (Unix.times ()).Unix.tms_cutime in
    let res = Decider.prove_sqob sqob env k in
    let time = (Unix.times ()).Unix.tms_cutime -. start_time in
    if res then Printf.printf "\nSequent is valid (%.2fs).\n\n" time 
    else  Printf.printf "\nSequent is not valid (%.2fs).\n\n" time
  with Failure s -> print_endline s

let _ =
  CmdLine.process();  
  let k = ref 1 in
  try
    while true do
      let _ = print_string prompt; flush stdout in
      let seq_string = read_seq_string () in
      eval seq_string !k; k := !k + 1;
    done
  with End_of_file -> exit 0
