

type c_array = Obj.t array

let array_length a : Datatypes.nat = 
  MlCoq.int_to_nat (Array.length a)
;;

let new_array size () : c_array = 
  Array.make (MlCoq.nat_to_int size) (Obj.magic ())
;;

let free_array ary () =
  ()
;;

let sub_array ary idx () =
  Obj.magic (Array.unsafe_get ary (MlCoq.nat_to_int idx))
;;

let upd_array ary idx v () =
  Array.unsafe_set ary (MlCoq.nat_to_int idx) (Obj.magic v)
;;
