type 'a oref = 'a option ref

type cell = {
    data : int;
    next : cell oref;
  }

let (first : cell oref) = ref None

let print_cells() =
  let rec pr (c: cell oref) = match !c with
  | None -> ()
  | Some cl -> 
      Printf.printf "%d " cl.data;
      pr cl.next
  in (Printf.printf "[";
      pr first;
      Printf.printf "]\n")

let dr oc = match !oc with
| None -> failwith "Null dereference"
| Some c -> c

let add (x:int) =
  let c = {data=x; next = ref (!first)} in
  first := Some c
