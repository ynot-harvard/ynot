theory insertionSort_Insertion_lemmas = Jahob:

lemma Insertion_insertionSort_InitialPartOfProcedure21: "([|(ALL k. (((0 <= k) & (intless k (j_20 - 1))) --> ((fieldRead InsertionSortNode_key (arrayRead Array_arrayState_23 arr k)) <= (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_23 arr (intplus k 1))))));
(intless 0 (j_20 - 1))|] ==>
    comment ''InvPreservation'' ((fieldRead InsertionSortNode_key (arrayRead (arrayWrite (arrayWrite Array_arrayState_23 arr j_20 (arrayRead Array_arrayState_23 arr (j_20 - 1))) arr (j_20 - 1) (arrayRead Array_arrayState_23 arr j_20)) arr ((j_20 - 1) - 1))) <= (fieldRead InsertionSortNode_key (arrayRead (arrayWrite (arrayWrite Array_arrayState_23 arr j_20 (arrayRead Array_arrayState_23 arr (j_20 - 1))) arr (j_20 - 1) (arrayRead Array_arrayState_23 arr j_20)) arr (intplus (j_20 - 1) 1)))))"
apply simp
apply (erule_tac x="j_20 - 2" in allE, simp add: linear_rews)
done

lemma Insertion_insertionSort_InitialPartOfProcedure32: "([|(ALL k. (((0 <= k) & (intless k (j_20 - 1))) --> ((fieldRead InsertionSortNode_key (arrayRead Array_arrayState_23 arr k)) <= (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_23 arr (intplus k 1))))));
(~(intless (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_23 arr j_20)) (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_23 arr (j_20 - 1)))));
(intless 0 (j_20 - 1))|] ==>
    comment ''InvPreservation'' ((fieldRead InsertionSortNode_key (arrayRead Array_arrayState_23 arr ((j_20 - 1) - 1))) <= (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_23 arr (intplus (j_20 - 1) 1)))))"
apply simp
apply (erule_tac x="j_20 - 2" in allE, simp add: linear_rews)
done

lemma Insertion_insertionSort_InitialPartOfProcedure33: "([|(ALL k. (((j_20 <= k) & (intless k i_39)) --> ((fieldRead InsertionSortNode_key (arrayRead Array_arrayState_23 arr k)) <= (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_23 arr (intplus k 1))))));
(~(intless (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_23 arr j_20)) (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_23 arr (j_20 - 1)))));
((j_20 - 1) <= k);
(intless k i_39)|] ==>
    comment ''InvPreservation'' ((fieldRead InsertionSortNode_key (arrayRead Array_arrayState_23 arr k)) <= (fieldRead InsertionSortNode_key (arrayRead Array_arrayState_23 arr (intplus k 1)))))"
apply simp
apply (case_tac "k = j_20 - 1", simp)
apply force
done

end
