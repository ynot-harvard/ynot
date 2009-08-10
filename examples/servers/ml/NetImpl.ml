open ST;;
open Ascii;;
open IOImpl;;

type axiom_SockAddr = Unix.sockaddr;;

let axiom_sockaddr n1 n2 n3 n4 p () =
  let mk n = string_of_int (ntoi n) in
  let str = (mk n1) ^ "." ^ (mk n2) ^ "." ^ (mk n3) ^ "." ^ (mk n4) in
  Unix.ADDR_INET ((Unix.inet_addr_of_string str), (ntoi p))
;;

let axiom_sockeq = (=)
;;

(** UDP **)
let axiom_UDP_Sent _ _ _  = failwith "Sent must be computationally irrelevent";;
let axiom_UDP_Recd _ _ _  = failwith "Recv must be computationally irrelevent";;

let axiom_UDP_send src trg data () =
  let sdata = latostr data in 
  let proto = (Unix.getprotobyname "udp").Unix.p_proto in
  let skt   = Unix.socket Unix.PF_INET Unix.SOCK_DGRAM proto in
  let _     = Unix.setsockopt_optint skt Unix.SO_LINGER (Some 100) in
  let _     = Unix.setsockopt_int skt Unix.SO_SNDBUF (String.length sdata) in
  let _     = Unix.bind skt src in
  let _     = Unix.sendto skt sdata 0 (String.length sdata) [] trg in
  Unix.close skt
;;

let axiom_UDP_recv src () = 
  let proto   = (Unix.getprotobyname "udp").Unix.p_proto in
  let skt     = Unix.socket Unix.PF_INET Unix.SOCK_DGRAM proto in
  let _       = Unix.setsockopt_optint skt Unix.SO_LINGER (Some 100) in
  let _       = Unix.bind skt src in
  let data    = String.create 255 in
  let len,adr = Unix.recvfrom skt data 0 255 [] in
  Unix.close skt;
  Datatypes.Coq_pair (adr, strtola (String.sub data 0 len))
;;

(** TCP **)
let axiom_BoundSocketModel _ _ = ();;
let axiom_ListenSocketModel _ = ();;

let axiom_TCP_Accept _ _ _  = failwith "Accept must be computationally irrelevent";;

let axiom_TCP_listenSocket sa () =
  let skt = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  let _   = Unix.bind skt sa in
  let _   = Unix.listen skt 5 in
  {FSImpl.fd    = skt;
   FSImpl.read  = FSImpl.fd_NoRead; 
   FSImpl.write = FSImpl.fd_NoWrite;
   FSImpl.flush = FSImpl.fd_NoFlush;
   FSImpl.close = FSImpl.file_close skt}
;;

let axiom_TCP_bindSocket local remote () =
  let skt = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  let _   = Unix.bind skt local in
  let _   = Unix.connect skt remote in
  {FSImpl.fd    = skt;
   FSImpl.read  = FSImpl.file_read skt;
   FSImpl.write = FSImpl.file_write skt;
   FSImpl.flush = FSImpl.file_flush skt;
   FSImpl.close = FSImpl.file_close skt}
;;

let axiom_TCP_accept _ skt () =
  let (fd,ra) = Unix.accept skt.FSImpl.fd in
  let la = Unix.getsockname fd in
  let bskt = 
    {FSImpl.fd    = fd;
     FSImpl.read  = FSImpl.file_read fd;
     FSImpl.write = FSImpl.file_write fd;
     FSImpl.flush = FSImpl.file_flush fd;
     FSImpl.close = FSImpl.file_close fd} in
  Specif.Coq_existT (Datatypes.Coq_pair (la,ra), bskt)
;;


(** SSL **)
let axiom_SslListenSocketModel _ = ();;

let ssl_ctx =
  let ctx = ref None in
  fun () ->
    match !ctx with
    | Some cert -> cert
    | None ->
	let _ = Ssl.init () in
	let c = Ssl.create_context Ssl.SSLv23 Ssl.Server_context in
	let _ = ctx := Some c in
	c
;;

let ssl_read fd () = 
  let str = " " in
  let len = Ssl.read fd str 0 1 in
  if len = 0 then
    None
  else
    Some (String.get str 0)
;;
  
let ssl_write fd chr () = 
  let _ = Ssl.write fd (String.make 1 chr) 0 1 in
  ()
;;

let ssl_flush fd () = 
  Ssl.flush fd
;;

let ssl_close fd () = 
  Ssl.shutdown fd
;;

let axiom_SSL_listenSocket sa () =
  let ctx  = ssl_ctx () in
  let skt  = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  let _    = Unix.bind skt sa in
  let _    = Unix.listen skt 5 in
  let sskt = Ssl.embed_socket skt ctx in (** Do I really not use this? **)
  {FSImpl.fd    = skt;
   FSImpl.read  = FSImpl.fd_NoRead;
   FSImpl.write = FSImpl.fd_NoWrite;
   FSImpl.flush = FSImpl.fd_NoFlush;
   FSImpl.close = ssl_close sskt}
;;

let axiom_SSL_bindSocket local remote () =
  let skt = Ssl.open_connection Ssl.SSLv23 remote in
  {FSImpl.fd    = Obj.magic skt; (** A little bit sketchy but the coq interface
				     guarantees it. Potential problems in 
				     extending things though. **)
   FSImpl.read  = ssl_read skt;
   FSImpl.write = ssl_write skt;
   FSImpl.flush = ssl_flush skt;
   FSImpl.close = ssl_close skt}
;;

let axiom_SSL_accept _ skt () =
  let (fd,ra) = Unix.accept skt.FSImpl.fd in
  let la = Unix.getsockname fd in
  let ssl_s = Ssl.embed_socket fd (ssl_ctx ()) in
  let bskt = 
    {FSImpl.fd    = fd;
     FSImpl.read  = ssl_read ssl_s;
     FSImpl.write = ssl_write ssl_s;
     FSImpl.flush = ssl_flush ssl_s;
     FSImpl.close = ssl_close ssl_s} in
  Specif.Coq_existT (Datatypes.Coq_pair (la,ra), bskt)
;;
