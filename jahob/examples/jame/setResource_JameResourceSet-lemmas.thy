theory "setResource_JameResourceSet-lemmas" = Jahob:

lemma JameResourceSet_setResource_InitialPartOfProcedure10: "([|(ALL this__25. ((fieldRead JameResourceSet_resources this__25) ~= null));
(ALL this__26. ((fieldRead Object_owner (fieldRead JameResourceSet_resources this__26)) = token_JameResourceSet));
((fieldRead JameResource_value x_3) = (fieldRead JameResource_value newRes));
(ALL x. ((((fieldRead Object_owner x) ~= token_JameResourceSet) & (x ~= x_3) & (x : alloc_JameResource)) --> ((fieldRead JameResource_value x) = (fieldRead JameResource_value x))));
(x_3 ~= null);
(ALL this__21. ((fieldRead JameResourceSet_resources this__21) ~= null));
(ALL this__22. ((fieldRead Object_owner (fieldRead JameResourceSet_resources this__22)) = token_JameResourceSet));
(((x_3 = null) & (ALL x. ((x : (fieldRead (% this__19. {p. (EX e. ((e : (fieldRead JameCollection_collection (fieldRead JameResourceSet_resources this__19))) & (p = ((fieldRead JameResource_name e), (fieldRead JameResource_value e)))))}) this)) --> ((fst x) ~= (fieldRead JameResource_name newRes))))) | ((x_3 ~= null) & ((fieldRead JameResource_name x_3) = (fieldRead JameResource_name newRes)) & (((fieldRead JameResource_name x_3), (fieldRead JameResource_value x_3)) : (fieldRead (% this__20. {p. (EX e. ((e : (fieldRead JameCollection_collection (fieldRead JameResourceSet_resources this__20))) & (p = ((fieldRead JameResource_name e), (fieldRead JameResource_value e)))))}) this))));
(ALL this. ((fieldRead JameResourceSet_resources this) ~= null));
(newRes ~= null);
comment ''thisNotNull'' (this ~= null);
comment ''thisType'' ((this : alloc_JameResourceSet) & (this : JameResourceSet));
((fieldRead JameResource_name newRes) ~= null);
(ALL this. ((fieldRead Object_owner (fieldRead JameResourceSet_resources this)) = token_JameResourceSet))|] ==>
    ((EX y. ((y : (fieldRead (% this__27. {p. (EX e. ((e : (fieldRead JameCollection_collection (fieldRead JameResourceSet_resources this__27))) & (p = ((fieldRead JameResource_name e), (fieldRead JameResource_value e)))))}) this)) & ((fst y) = (fieldRead JameResource_name newRes)) & ((fieldRead (% this__28. {p. (EX e. ((e : (fieldRead JameCollection_collection (fieldRead JameResourceSet_resources this__28))) & (p = ((fieldRead JameResource_name e), (fieldRead JameResource_value e)))))}) this) = (((fieldRead (% this__29. {p. (EX e. ((e : (fieldRead JameCollection_collection (fieldRead JameResourceSet_resources this__29))) & (p = ((fieldRead JameResource_name e), (fieldRead JameResource_value e)))))}) this) - {y}) Un {((fieldRead JameResource_name newRes), (fieldRead JameResource_value newRes))})))) | ((~(EX y. ((y : (fieldRead (% this__30. {p. (EX e. ((e : (fieldRead JameCollection_collection (fieldRead JameResourceSet_resources this__30))) & (p = ((fieldRead JameResource_name e), (fieldRead JameResource_value e)))))}) this)) & ((fst y) = (fieldRead JameResource_name newRes))))) & ((fieldRead (% this__31. {p. (EX e. ((e : (fieldRead JameCollection_collection (fieldRead JameResourceSet_resources this__31))) & (p = ((fieldRead JameResource_name e), (fieldRead JameResource_value e)))))}) this) = ((fieldRead (% this__32. {p. (EX e. ((e : (fieldRead JameCollection_collection (fieldRead JameResourceSet_resources this__32))) & (p = ((fieldRead JameResource_name e), (fieldRead JameResource_value e)))))}) this) Un {((fieldRead JameResource_name newRes), (fieldRead JameResource_value newRes))})))))"
apply(force)
done


end
