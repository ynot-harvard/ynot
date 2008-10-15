(benchmark node2.smt
  :source     { Proof obligation: 
	([|((Node_y :: (obj => int)) = ((% (this::obj). 0) :: (obj => int)));
	((Node_x :: (obj => int)) = ((% (this::obj). 0) :: (obj => int)))|] ==>
	    ((Node_x :: (obj => int)) = ((% (this::obj). 0) :: (obj => int))))
 }
  :logic      AUFLIA
  :extrasorts (Obj)
  :extrafuns  ((x Obj))
  :extrafuns  ((nodeY Obj Int))
  :extrafuns  ((nodeX Obj Int))

  :assumption (forall (?x Obj) (= (nodeY ?x) 0))
  :assumption (forall (?x Obj) (= (nodeX ?x) 0))

  :formula    (not (= (nodeX x) 0))
  :status     unknown
)