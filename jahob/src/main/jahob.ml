(** jahob main application. *)

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

let invoke () : bool =
  parse_java_files !CmdLine.javaFiles;
  Debug.msg 
    (Printf.sprintf "Number of compilation units processed: %d.\n"
       (List.length !units));
  Util.fail_if_warned("PARSING FAILED.");
  let (p,task) = Javajast.joust2jast !units (CmdLine.get_task()) in
  let u = Jastjava.jast2joust p in
  Util.fail_if_warned("CONVERSION TO Jast FAILED.");
  let _ = if !CmdLine.printJast then
    (Util.msg "Resulting declarations:\n";
     Pretty.print Format.std_formatter u) else() in
  let ast = Jast2ast.c_program p in
  Util.fail_if_warned("CONVERSION TO Ast FAILED.");
  let _ = if !CmdLine.printAst then 
    print_string (PrintAst.string_of_program ast) else() in
  let _ = if !CmdLine.sastVC then 
    (let sast = Sast.ast2sast ast in
       if !CmdLine.printSAst then
	 print_string (PrintAst.simplified_program sast))
  in
    (if !CmdLine.verify then ()
     else 
       Util.amsg "*** VERIFICATION WILL FAIL, -noverify option given.\n");
    let ok = Analyze.analyze ast task in
    let _ = if ok then Util.amsg "\n0=== Verification SUCCEEDED.\n"
    else Util.amsg "\n-1=== Verification FAILED.\n" in
      ok

let print_info() =
  (Util.msg 
"     _       _           _                  _____
    | | __ _| |__   ___ | |__              /     \\
 _  | |/ _` | '_ \\ / _ \\| '_ \\       x <==|  (J)  |===.
| |_| | (_| | | | | (_) | |_) |     ======+=======+===\"  F
 \\____/\\__,_|_| |_|\\___/|_.__/             \\_____/  

";
   Debug.msg "
                            / \\  //\\
             |\\___/|      /   \\//  \\\\
            /0  0  \\__  /    //  | \\ \\
           /     /  \\/_/    //   |  \\  \\                 
           @_^_@'/   \\/_   //    |   \\   \\
           //_^_/     \\/_ //     |    \\    \\
        ( //) |        \\///      |     \\     \\
      ( / /) _|_ /   )  //       |      \\     _\\
    ( // /) '/,_ _ _/  ( ; -.    |    _ _\\.-~        .-~~~^-.
  (( / / )) ,-{        _      `-.|.-~-.           .~         `.
 (( // / ))  '/\\      /                 ~-. _ .-~      .-~^-.  \\
 (( /// ))      `.   {            }                   /      \\  \\
  (( / ))     .----~-.\\        \\-'                 .~         \\  `. \\^-.
 [BUGS]            ///.----..>        \\          _ -~             `.  ^-`  ^-_
                  ///-._ _ _ _ _ _ _}^ - - - - ~                  ~-- ,.-~/.-~
Formal methods are the future of computer science---always have been, always will be.

";
   flush_all())

let _ =
  Util.amsg("[Jahob Version -0.45]\n");
  CmdLine.process();
  print_info();
  try 
    let res = invoke() in
      if res then exit 0 else exit 1
  with _ -> exit 1

