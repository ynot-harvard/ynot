(** Test driver for BAPA decision procedure. *)

let runFormula (f : Form.form) : bool =
  let bf = Formbapa.formToBapa f in
  let _ = print_string ((Alpha.string_of_form bf) ^ "\n\n") in
  let pf = Bapapres.bapaFormToPresForm (Alpha.alpha bf) in
    Presburger.omegaIsValid pf

let runFormulaLash (f : Form.form) : bool =
  let bf = Formbapa.formToBapa f in
  let _ = print_string ((Alpha.string_of_form bf) ^ "\n\n") in
  let pf = Bapapres.bapaFormToPresForm (Alpha.alpha bf) in
    Presburger.lashIsUnsatisfiable pf

let print_validity (f : Form.form) : unit = 
(*  let b = runFormulaLash f in *)
  let b = runFormula f in 
    begin
      print_string (PrintForm.string_of_form f);
      if b then
	print_string ("\n\t is valid\n\n")
      else
	print_string ("\n\t is invalid\n\n")
    end


let remove_comment (str : string) : string =
  let n = String.length str in
  let l = ref 0 in
    while !l < n && str.[!l] != '#' do
      l := !l + 1
    done;
    String.sub str 0 !l

let trim_newlines (str : string) : string =
  let l = ref (String.length str) in
    while str.[!l - 1] = '\n' || str.[!l - 1] = '\r' do
      l := !l - 1
    done;
    String.sub str 0 !l

let _ =
  if Array.length Sys.argv < 2 then
    print_string "Usage: bapa inputfile\n\tinputfile contains BAPA formulae\n"
  else if not (Sys.file_exists (Array.get Sys.argv 1)) then
    print_string ("File " ^ (Array.get Sys.argv 1) ^ " does not exist\n")
  else
    let chn = open_in (Array.get Sys.argv 1) in
(*
  let chn = open_in "/home/nguyenh2/jahob/examples/formulae/simrel6" in
*)
    let contents = Buffer.create 4096 in
      begin
	begin
	  try 
	    while true do
	      let input = remove_comment (input_line chn) in
		if String.length input > 0 then
		  Buffer.add_string contents (trim_newlines input)
	    done
	  with
	      _ -> close_in chn
	end;
	let fs = ParseForm.parse_formula_list (Buffer.contents contents) in
	  begin
	    ignore (List.map print_validity fs)
(*
	    let simplifystr = String.concat "\n" (List.map Simplify.printToSimplify fs) in
	    let chn_out = open_out ((Array.get Sys.argv 1) ^ ".simplify") in
	      begin
		output_string chn_out simplifystr;
		close_out chn_out
	      end
*)
	  end
      end
