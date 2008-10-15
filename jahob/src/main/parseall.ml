(** jahob main application. *)

open Common

let errors = ref 0
let error msg =
  incr errors;
  Printf.eprintf "%s: %s\n" (Source.location ()) msg

let parse() =
  try
    Source.with_lexbuf
      (fun lexbuf ->
	let result = Parser.goal Lexer.token lexbuf in
        (*
	List.iter print_comment result.Syntax.comments;
	Pretty.print Format.std_formatter result;
         *)
        Some result)
  with e -> (error (Printexc.to_string e); None)

let units = ref ([] : Syntax.compilation_unit list)

let rec parse_java_files (files : string list) =  
  match files with 
    | [] -> ()
    | file::files1 -> 
	Source.set_file_name file;
	(match parse() with
	   | None -> Util.warn ("Java file " ^ file ^ " failed to parse.")
	   | Some ast -> units := ast :: !units);
	parse_java_files files1

let invoke() =
  parse_java_files !CmdLine.javaFiles;
  Debug.msg 
    (Printf.sprintf "Number of compilation units processed: %d.\n"
       (List.length !units));
  let (p,task) = Javajast.joust2jast !units (CmdLine.get_task()) in
  let u = Jastjava.jast2joust p in
  let _ = if !CmdLine.printJast then
    (Debug.msg "Resulting declarations:\n";
     Pretty.print Format.std_formatter u) else() in
  let ast = Jast2ast.c_program p in
  let _ = if !CmdLine.printAst then 
    print_string (PrintAst.string_of_program ast) else() in
    ()

let print_info() =
  print_string "Jahob version -0.99\n"

let _ =
  print_info();
  CmdLine.process();  
  invoke()
