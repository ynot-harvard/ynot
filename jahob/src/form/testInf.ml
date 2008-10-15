(** Testing type inference in {!Typeinf}. *)

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
(*
  if Array.length Sys.argv < 2 then
    print_string "Usage: bapa inputfile\n\tinputfile contains BAPA formulae\n"
  else if not (Sys.file_exists (Array.get Sys.argv 1)) then
    print_string ("File " ^ (Array.get Sys.argv 1) ^ " does not exist\n")
  else
    let chn = open_in (Array.get Sys.argv 1) in
*)
  let chn = open_in "/home/nguyenh2/jahob/examples/formulae/testinf" in
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
	    (* ignore (List.map print_validity fs); *)
	    let fs1 = List.map (fun f -> Typeinf.infer f []) fs in
	      List.map (fun f -> print_string ((Alpha.string_of_form (Formbapa.formToBapa f)) ^ "\n\n")) fs1
	  end
      end
