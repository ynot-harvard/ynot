(benchmark linear8.smt
  :source { Proof obligation: 
	([|((intless (x_3 :: int) (10 :: int)) :: bool);
	comment ''allocatedObject'' (((fieldRead (Object_owner :: (obj => int)) (x_1 :: obj)) :: int) = (token_NoOwner :: int));
	((x_1 :: obj) ~= (null :: obj));
	((x_1 :: obj) ~: ((Object_alloc \<setminus> \{x_12\}) :: obj set));
	((0 :: int) <= (x_3 :: int));
	((x_3 :: int) <= (10 :: int));
	(((fieldRead Array_length x_12) :: int) = (10 :: int));
	((x_12 :: obj) ~: (Object_alloc :: obj set));
	((x_12 :: obj) ~= (null :: obj))|] ==>
	    comment ''null check'' (((arrayRead ((arrayWrite (x_10 :: (obj => (int => obj))) (x_12 :: obj) (x_3 :: int) (x_1 :: obj)) :: (obj => (int => obj))) (x_12 :: obj) (x_3 :: int)) :: obj) ~= (null :: obj)))

}
  :logic AUFLIA
  :extrafuns  ((x_3 Int))
  :extrasorts (Obj)
  :extrasorts (Owner)
  :extrafuns  ((x_1 Obj))
  :extrafuns  ((noOwner Owner))
  :extrafuns  ((objectOwner Obj Owner))
  :extrafuns  ((null Obj))
  :extrapreds ((objectAlloc Obj))
  :extrafuns  ((x_12 Obj))
  :extrafuns  ((arrayLength Obj Int))
  :extrafuns  ((arrayRead Obj Int Obj))

  :assumption (< x_3 10)
  :assumption (= (objectOwner x_1) noOwner)
  :assumption (not (= x_1 null))
  :assumption (or (not (objectAlloc x_1)) (= x_1 x_12))
  :assumption (<= 0 x_3)
  :assumption (<= x_3 10)
  :assumption (= (arrayLength x_12) 10)
  :assumption (not (objectAlloc x_12))
  :assumption (not (= x_12 null))

  :formula    (not (not (= (ite (= x_3 x_3) x_1 (arrayRead x_12 x_3)) null)))

  :status unknown
)