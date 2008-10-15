(benchmark linear2.smt
  :source { Proof obligation: 
	([|(((fieldRead Array_length x_12) :: int) = (10 :: int));
	((x_12 :: obj) ~: (Object_alloc :: obj set));
	((x_12 :: obj) ~= (null :: obj))|] ==>
	    comment ''InvHoldsInitially'' ((0 :: int) <= (10 :: int)))
}
  :logic AUFLIA
  :extrasorts (Obj)
  :extrafuns  ((null Obj))
  :extrafuns  ((x_12 Obj))
  :extrafuns  ((arrayLength Obj Int))
  :extrapreds ((objectAlloc Obj))
  :assumption (= (arrayLength x_12) 10)
  :assumption (not (objectAlloc x_12))
  :assumption (not (= x_12 null))
  :formula    (not (<= 0 10))
  :status unknown
)