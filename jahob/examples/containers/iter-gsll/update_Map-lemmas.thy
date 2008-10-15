theory "update_Map-lemmas" = Jahob:

lemma Map_update_InitialPartOfProcedure5: "([|(n : (List_content - x_10));
(List_content <= alloc_Pair1);
(List_iter <= List_content);
(null ~: List_content);
(ALL n1 n2. (((n1 : List_content) & (n2 : List_content) & ((fieldRead Pair1_key n1) = (fieldRead Pair1_key n2))) --> (n1 = n2)));
(x_10 = List_content);
(key ~= null);
(value ~= null)|] ==>
    ((fieldRead Pair1_key n) ~= key))"
apply safe
done

lemma relationUpdate:
"x_3 ~: List_content ==>
 {p. (EX n. ((n : List_content Un {x_3}) & (p = ((fieldRead (fieldWrite Pair1_key x_3 key) n), (fieldRead (fieldWrite Pair1_value x_3 value) n)))))} =  
 {p. (EX n. ((n : List_content) & (p = (fieldRead Pair1_key n, fieldRead Pair1_value n))))} Un {(key,value)}"
apply safe
thm "fieldRead"
apply (simp add: Jahob.fieldRead_def)
ML {*ResClasimp.use_simpset := true*}
ML {*ResAtp.prover := "vampire"*}
ML {*ResAtp.time_limit := 10*}
ProofGeneral.call_atp

done

lemma Map_update_LoopInvImpliesPost7: "([|(k ~= key);
(List_content <= (alloc_Pair1 Un {x_3}));
(List_iter <= List_content);
(null ~: List_content);
(ALL n1 n2. (((n1 : List_content) & (n2 : List_content) & ((fieldRead (fieldWrite Pair1_key x_3 key) n1) = (fieldRead (fieldWrite Pair1_key x_3 key) n2))) --> (n1 = n2)));
(x_1 = (List_content Un {x_3}));
(List_content <= alloc_Pair1);
(x_3 ~= null);
(~(~x_9));
(x_3 ~: alloc_Pair1);
(x_9 = (List_iter = {}));
(ALL n1 n2. (((n1 : List_content) & (n2 : List_content) & ((fieldRead Pair1_key n1) = (fieldRead Pair1_key n2))) --> (n1 = n2)));
(Pair1_value = old_Pair1_value);
(ALL n. ((n : (List_content - List_iter)) --> ((fieldRead Pair1_key n) ~= key)));
(Pair1_key = old_Pair1_key);
(List_content = old_List_content)|] ==>
    (((k, v) : {p. (EX n. ((n : x_1) & (p = ((fieldRead (fieldWrite Pair1_key x_3 key) n), (fieldRead (fieldWrite Pair1_value x_3 value) n)))))}) = 
     ((k, v) : {p. (EX n. ((n : old_List_content) & (p = ((fieldRead old_Pair1_key n), (fieldRead old_Pair1_value n)))))})))"
sorry

lemma Map_update_LoopInvImpliesPost8: "([|((fieldRead (fieldWrite Pair1_key x_3 key) n1) = (fieldRead (fieldWrite Pair1_key x_3 key) n2));
(n2 : x_1);
(n1 : x_1);
(List_content <= (alloc_Pair1 Un {x_3}));
(List_iter <= List_content);
(null ~: List_content);
(ALL n1 n2. (((n1 : List_content) & (n2 : List_content) & ((fieldRead (fieldWrite Pair1_key x_3 key) n1) = (fieldRead (fieldWrite Pair1_key x_3 key) n2))) --> (n1 = n2)));
(x_1 = (List_content Un {x_3}));
(List_content <= alloc_Pair1);
(x_3 ~= null);
(~(~x_9));
(x_3 ~: alloc_Pair1);
(x_9 = (List_iter = {}));
(Pair1_value = old_Pair1_value);
(ALL n. ((n : (List_content - List_iter)) --> ((fieldRead Pair1_key n) ~= key)));
(Pair1_key = old_Pair1_key);
(List_content = old_List_content)|] ==>
    (n1 = n2))"
sorry
(*
apply (subgoal_tac "List_iter = {}")
prefer 2
apply force
apply (case_tac "n1 = x_3")
apply (case_tac "n2 = x_3")
apply force
apply (subgoal_tac "key = old_Pair1_key n2")
defer
apply force
apply force
apply force
*)

lemma Map_update_LoopInvImpliesPost9: "([|(List_content <= (alloc_Pair1 Un {x_3}));
(List_iter <= List_content);
(null ~: List_content);
(ALL n1 n2. (((n1 : List_content) & (n2 : List_content) & ((fieldRead (fieldWrite Pair1_key x_3 key) n1) = (fieldRead (fieldWrite Pair1_key x_3 key) n2))) --> (n1 = n2)));
(x_1 = (List_content Un {x_3}));
(List_content <= alloc_Pair1);
(x_3 ~= null);
(~(~x_9));
(x_3 ~: alloc_Pair1);
(x_9 = (List_iter = {}));
(ALL n1 n2. (((n1 : List_content) & (n2 : List_content) & ((fieldRead Pair1_key n1) = (fieldRead Pair1_key n2))) --> (n1 = n2)));
(Pair1_value = old_Pair1_value);
(ALL n. ((n : (List_content - List_iter)) --> ((fieldRead Pair1_key n) ~= key)));
(Pair1_key = old_Pair1_key);
(List_content = old_List_content)|] ==>
    (null ~: x_1))"
apply force
done

lemma Map_update_LoopInvImpliesPost10: "([|(List_content <= (alloc_Pair1 Un {x_3}));
(List_iter <= List_content);
(null ~: List_content);
(ALL n1 n2. (((n1 : List_content) & (n2 : List_content) & ((fieldRead (fieldWrite Pair1_key x_3 key) n1) = (fieldRead (fieldWrite Pair1_key x_3 key) n2))) --> (n1 = n2)));
(x_1 = (List_content Un {x_3}));
(List_content <= alloc_Pair1);
(x_3 ~= null);
(~(~x_9));
(x_3 ~: alloc_Pair1);
(x_9 = (List_iter = {}));
(ALL n1 n2. (((n1 : List_content) & (n2 : List_content) & ((fieldRead Pair1_key n1) = (fieldRead Pair1_key n2))) --> (n1 = n2)));
(Pair1_value = old_Pair1_value);
(ALL n. ((n : (List_content - List_iter)) --> ((fieldRead Pair1_key n) ~= key)));
(Pair1_key = old_Pair1_key);
(List_content = old_List_content)|] ==>
    (List_iter <= x_1))"
apply force
done

lemma Map_update_LoopInvImpliesPost11: "
[|(List_content <= (alloc_Pair1 Un {x_3}));
  (x_1 = (List_content Un {x_3}))|] ==>
    (x_1 <= (alloc_Pair1 Un {x_3}))"
apply force
done

lemma Map_update_LoopInvImpliesPost13: "([|((fieldRead (fieldWrite Pair1_key x_3 key) n1) = (fieldRead (fieldWrite Pair1_key x_3 key) n2));
(n2 : List_content);
(n1 : List_content);
(List_iter <= List_content);
(List_content <= alloc_Pair1);
(x_3 ~= null);
(~(~x_9));
(x_3 ~: alloc_Pair1);
(x_9 = (List_iter = {}));
(ALL n1 n2. (((n1 : List_content) & (n2 : List_content) & ((fieldRead Pair1_key n1) = (fieldRead Pair1_key n2))) --> (n1 = n2)));
(null ~: List_content);
(Pair1_value = old_Pair1_value);
(ALL n. ((n : (List_content - List_iter)) --> ((fieldRead Pair1_key n) ~= key)));
(Pair1_key = old_Pair1_key);
(List_content = old_List_content)|] ==>
    (n1 = n2))"
apply (subgoal_tac "List_iter = {}")
prefer 2
apply force
apply clarify
apply (case_tac "n1 = x_3")
apply (case_tac "n2 = x_3")
apply force
apply force
apply force
done

lemma Map_update_LoopInvImpliesPost6: "([|(List_content <= (alloc_Pair1 Un {x_3}));
(List_iter <= List_content);
(null ~: List_content);
(x_1 = (List_content Un {x_3}));
(List_content <= alloc_Pair1);
(x_3 ~= null);
(~(~x_9));
(x_3 ~: alloc_Pair1);
(x_9 = (List_iter = {}));
(Pair1_value = old_Pair1_value);
(Pair1_key = old_Pair1_key);
(List_content = old_List_content)|] ==>
    ((key, value) : {p. (EX n. ((n : x_1) & (p = ((fieldRead (fieldWrite Pair1_key x_3 key) n), (fieldRead (fieldWrite Pair1_value x_3 value) n)))))}))"
apply force
done

end