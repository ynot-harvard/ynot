open Form
open FormUtil
open PrintForm
open TermRewrite
open MonaConvert
open TypeReconstruct

let _ = Debug.debugOn := true
let _ = CmdLine.set_timeout 30

let get_sequent seq_string =
  let seq0 = ParseForm.parse_formula seq_string in
  let env0 = List.map (fun x -> (x, TypeUniverse)) (fv seq0) in
  let seq, env = reconstruct_types env0 seq0 in
  let sequent =
    match seq with 
    | App (Const MetaImpl, [App (Const MetaAnd, fs); g]) -> (fs, g)
    | App (Const MetaImpl, [f; g]) -> ([f], g)
    | _ -> ([], seq)
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
	 raise ex)

let eval env seq = 
  let start_time = (Unix.times ()).Unix.tms_cutime in
  let res = exc_to_bool "MONA" (Mona.prove_sequent env) seq in
  let time = (Unix.times ()).Unix.tms_cutime -. start_time in
  if res then Printf.printf "\nSequent is valid (%.2fs).\n\n" time 
  else  Printf.printf "\nSequent is not valid (%.2fs).\n\n" time


let _ =
  try
    while true do
      let _ = print_string prompt; flush stdout in
      let seq_string = read_seq_string () in
      let seq, env = get_sequent seq_string in
      eval env seq
    done
  with End_of_file -> exit 0
