open IOImpl

let axiom_Read _ _ _  = failwith "Read must be computationally irrelevent";;
let axiom_Write _ _ _ = failwith "Write must be computationally irrelevent";;
let axiom_Flush _ _ _ = failwith "Flush must be computationally irrelevent";;
let axiom_Close _ _ _ = failwith "Close must be computationally irrelevent";;

type axiom_fd_model = unit
let axiom_TtyModel = ();;
let axiom_FileModel _ = ();;

type file_descriptor = {
    fd    : Unix.file_descr;
    read  : unit -> char option;
    write : char -> unit -> unit;
    close : unit -> unit;
    flush : unit -> unit
  }

let axiom_read _ _ fd () = 
  match fd.read () with
    None -> let _ = print_string "--EOF"; flush stdout in None
  | Some r -> 
      let _ = print_string (String.make 1 r); flush stdout in
      Some (ctoa r)
;;

let axiom_write _ _ fd chr () =
  let _ = print_string (String.make 1 (atoc chr)); flush stdout in
  fd.write (atoc chr) ()
;;

let axiom_flush _ _ fd = fd.flush;;

let axiom_close _ _ fd = fd.close;;


let file_read fd () =
  let str = String.create 1 in
  let len = Unix.read fd str 0 1 in
  if len = 1 then
    Some (String.get str 0)
  else
    None
;;

let file_write fd c () =
  let str = String.make 1 c in
  let len = Unix.write fd str 0 1 in
  assert (len = 1);
  ()
;;

let file_close fd () = 
  Unix.close fd
;;

let file_flush fd () = 
  flush (Unix.out_channel_of_descr fd)
;;


let stdin = {
  fd    = Unix.stdin;
  read  = file_read Unix.stdin;
  write = (fun _ () -> failwith "can't write stdin");
  flush = (fun () -> failwith "can't flush stdin");
  close = file_close Unix.stdin
}

let stdout = {
  fd    = Unix.stdout;
  read  = (fun () -> failwith "can't read stdout");
  write = file_write Unix.stdout;
  flush = file_flush Unix.stdout;
  close = file_close Unix.stdout
}

let fd_NoRead = fun () -> failwith "Unreadable file descriptor";;
let fd_NoWrite = fun _ () -> failwith "Unwriteable file descriptor";;
let fd_NoFlush = fun () -> failwith "Unflushable file descriptor";;
