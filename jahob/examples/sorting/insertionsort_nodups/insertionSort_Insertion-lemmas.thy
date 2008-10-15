theory insertionSort_Insertion_lemmas = Jahob:

lemma Insertion_insertionSort_InitialPartOfProcedure30: "([|(ALL k. (((0 <= k) & (intless k (j_23 - 1))) --> ((fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr k)) <= (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr (intplus k 1))))));
(intless 0 (j_23 - 1))|] ==>
    comment ''InvPreservation'' ((fieldRead InsertionSortNode_key (arrayRead (arrayWrite (arrayWrite Array_arrayState_26 Insertion_arr j_23 (arrayRead Array_arrayState_26 Insertion_arr (j_23 - 1))) Insertion_arr (j_23 - 1) (arrayRead Array_arrayState_26 Insertion_arr j_23)) Insertion_arr ((j_23 - 1) - 1))) <= (fieldRead InsertionSortNode_key (arrayRead (arrayWrite (arrayWrite Array_arrayState_26 Insertion_arr j_23 (arrayRead Array_arrayState_26 Insertion_arr (j_23 - 1))) Insertion_arr (j_23 - 1) (arrayRead Array_arrayState_26 Insertion_arr j_23)) Insertion_arr (intplus (j_23 - 1) 1)))))"
apply (erule_tac x="(j_23 - 2)" in allE, simp add: linear_rews)
done

lemma Insertion_insertionSort_InitialPartOfProcedure32: "([|(intless i_43 (fieldRead Array_length Insertion_arr));
(Insertion_content_21 = Insertion_content);
(Insertion_content_21 = {n. (EX i__4. ((0 <= i__4) & ((arrayRead Array_arrayState_26 Insertion_arr i__4) = n) & (intless i__4 (Array_length Insertion_arr))))});
(((intless 0 j_23) & (intless j_23 i_43)) --> ((fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr (j_23 - 1))) <= (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr (intplus j_23 1)))));
(j_23 <= i_43);
(0 < j_23);
(intless (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr j_23)) (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr (j_23 - 1))));
(Insertion_content_5 = {n. (EX i__6. ((0 <= i__6) & ((arrayRead (arrayWrite (arrayWrite Array_arrayState_26 Insertion_arr j_23 (arrayRead Array_arrayState_26 Insertion_arr (j_23 - 1))) Insertion_arr (j_23 - 1) (arrayRead Array_arrayState_26 Insertion_arr j_23)) Insertion_arr i__6) = n) & (intless i__6 (Array_length Insertion_arr))))})|] ==>
    comment ''InvPreservation'' (Insertion_content_5 = Insertion_content))"
apply simp
apply safe
apply (rule_tac x="i__6" in exI, simp)
apply force
apply (rule_tac x="i_43" in exI, simp)
apply force
apply (rule_tac x="(j_23 - 1)" in exI, simp)
apply force
apply (rule_tac x="(j_23 - 1)" in exI, simp)
apply (rule_tac x="i__6" in exI, simp)
apply force
apply (rule_tac x="j_23" in exI, simp)
apply force
apply (rule_tac x="(j_23 - 1)" in exI, simp)
apply force
apply (rule_tac x="(j_23 - 1)" in exI, simp)
apply (case_tac "i__4 = i_43")
apply (rule_tac x="i_43 - 1" in exI, simp)
apply (case_tac "i__4 = (i_43 - 1)")
apply (rule_tac x="i_43" in exI, simp)
apply (rule_tac x="i__4" in exI, simp)
apply (case_tac "i__4 = j_23")
apply (rule_tac x="j_23 - 1" in exI, simp)
apply (case_tac "i__4 = (j_23 - 1)")
apply (rule_tac x="j_23" in exI, simp)
apply (rule_tac x="i__4" in exI, simp)
done

lemma Insertion_insertionSort_InitialPartOfProcedure43: "([|(ALL k. (((0 <= k) & (intless k (j_23 - 1))) --> ((fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr k)) <= (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr (intplus k 1))))));
(~(intless (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr j_23)) (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr (j_23 - 1)))));
(intless 0 (j_23 - 1))|] ==>
    comment ''InvPreservation'' ((fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr ((j_23 - 1) - 1))) <= (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr (intplus (j_23 - 1) 1)))))"
apply simp
apply (erule_tac x="(j_23 - 2)" in allE, simp add: linear_rews)
done

lemma Insertion_insertionSort_InitialPartOfProcedure46: "([|(ALL k. (((j_23 <= k) & (intless k i_43)) --> ((fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr k)) <= (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr (intplus k 1))))));
(~(intless (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr j_23)) (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr (j_23 - 1)))));
((j_23 - 1) <= k);
(intless k i_43)|] ==>
    comment ''InvPreservation'' ((fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr k)) <= (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr (intplus k 1)))))"
apply simp
apply (case_tac "k = j_23 - 1", simp)
apply force
done

lemma Insertion_insertionSort_InitialPartOfProcedure26: "([|(intless i_43 (fieldRead Array_length Insertion_arr));
(Insertion_content_21 = {n. (EX i__5. ((intless i__5 (Array_length Insertion_arr)) & (0 <= i__5) & ((arrayRead Array_arrayState_26 Insertion_arr i__5) = n)))});
(((intless 0 j_23) & (intless j_23 i_43)) --> ((fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr (j_23 - 1))) <= (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_26 Insertion_arr (intplus j_23 1)))));
(j_23 <= i_43);
(Insertion_content_21 = Insertion_content);
(0 < j_23);
(Insertion_content_5 = {n. (EX i__7. ((intless i__7 (Array_length Insertion_arr)) & (0 <= i__7) & ((arrayRead (arrayWrite (arrayWrite Array_arrayState_26 Insertion_arr j_23 (arrayRead Array_arrayState_26 Insertion_arr (j_23 - 1))) Insertion_arr (j_23 - 1) (arrayRead Array_arrayState_26 Insertion_arr j_23)) Insertion_arr i__7) = n)))})|] ==>
    comment ''InvPreservation'' (Insertion_content_5 = Insertion_content))"
apply simp
apply safe
apply simp_all
apply (rule_tac x="i__7" in exI, simp)
apply (erule_tac x="i_43" in allE, simp)
apply (rule_tac x="j_23" in exI, simp)
apply (erule_tac x="(i_43 - 1)" in allE, simp)
apply (rule_tac x="(j_23 - 1)" in exI, simp)
apply (rule_tac x="(j_23 - 1)" in exI, simp)
apply (rule_tac x="i__7" in exI, simp)
apply (erule_tac x="j_23" in allE, simp)
apply (rule_tac x="j_23" in exI, simp)
apply (erule_tac x="(j_23 - 1)" in allE, simp)
apply (rule_tac x="(j_23 - 1)" in exI, simp)
apply (rule_tac x="(j_23 - 1)" in exI, simp)
apply (case_tac "i__5 = (j_23 - 1)")
apply (rule_tac x="j_23" in exI, simp)
apply (case_tac "i__5 = j_23")
apply (rule_tac x="(j_23 - 1)" in exI, simp)
apply (rule_tac x="i__5" in exI, simp)
apply (case_tac "i__5 = (j_23 - 1)")
apply (rule_tac x="j_23" in exI, simp)
apply (case_tac "i__5 = j_23")
apply (rule_tac x="(j_23 - 1)" in exI, simp)
apply (rule_tac x="i__5" in exI, simp)
done

end
