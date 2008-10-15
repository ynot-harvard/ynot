(* Instantiatable mutable list *)

type cell = {
    mutable data : int;
    mutable next : cell option;
  }

type list = {
    mutable first : cell option;
  }

let mk_empty() = { first = None }

let rec pr (oc: cell option) = match oc with
| None -> ()
| Some c -> 
    Printf.printf "%d " c.data;
    pr c.next

let p (l : list) =
  (Printf.printf "[";
   pr l.first;
   Printf.printf "]\n")

let add (l:list) (x:int) =
  let c = {data=x; next = l.first} in
  l.first <- Some c

let rec add1 (x:int) (c:cell) = match c.next with
| None -> 
    c.next <- Some {data=x; next = None}
| Some c1 -> 
    add1 x c1

let add_last (l:list) (x:int) =
  match l.first with
  | None -> l.first <- Some {data=x; next = None}
  | Some c -> add1 x c

let rec rem1 (x:int) (c:cell option) : cell option = 
  match c with
  | None -> None
  | Some c1 -> 
      c1.next <- rem1 x c1.next;
      (if c1.data = x then c1.next
      else c)

let remove (l:list) (x:int) =
  l.first <- rem1 x l.first

let test() =
  let l1 = mk_empty() in
  let l2 = mk_empty() in
  (add l1 5;
   add l1 2;
   add l2 8;
   add l1 14;
   add l2 5;
   add l2 23;
   p l1; p l2;
   remove l1 2;
   p l1; p l2;
   remove l1 14;
   p l1; p l2;
   remove l2 5;
   p l1; p l2;
   remove l2 23;
   p l1; p l2)
