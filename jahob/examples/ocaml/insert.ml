(* Global mutable list *)

type cell = {
    mutable data : int;
    mutable next : cell option;
  }

let (first : cell option ref) = ref None

let rec pr (oc: cell option) = match oc with
| None -> ()
| Some c -> 
    Printf.printf "%d " c.data;
    pr c.next

let p() =
  (Printf.printf "[";
   pr !first;
   Printf.printf "]\n")

let add (x:int) =
  let c = {data=x; next = !first} in
  first := Some c

let rec rem1 (x:int) (c:cell option) : cell option = 
  match c with
  | None -> None
  | Some c1 -> 
      c1.next <- rem1 x c1.next;
      (if c1.data = x then c1.next
      else c)

let remove (x:int) =
  first := rem1 x !first

let rec add1 (x:int) (c:cell) = match c.next with
| None -> 
    c.next <- Some {data=x; next = None}
| Some c1 -> 
    add1 x c1

let add_last (x:int) =
  match !first with
  | None -> first := Some {data=x; next = None}
  | Some c -> add1 x c

let test() =
  (add 5;
   add 2;
   add 8;
   add 14;
   add 5;
   add 23;
   p();
   remove 2;
   p();
   remove 14;
   p();
   remove 5;
   p();
   remove 23;
   p())
