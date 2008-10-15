theory "add_Relation-lemmas" = Jahob:

lemma relation_base_add: "[|
(Relation_content = {p. (EX k v. ((p = (k, v)) & (EX n. ((k = (fieldRead Node_key n)) & (n : Relation_nodes) & (v = (fieldRead Node_value n))))))});
comment ''Relation_PrivateInv '' (Relation_nodes \<subseteq> Object_alloc);
(tmp_1_13 ~= null);
(tmp_1_13 ~: Object_alloc);
(Relation_content_1 = {p. (EX k v. ((p = (k, v)) & (EX n__6. ((k = (fieldRead (fieldWrite Node_key tmp_1_13 key) n__6)) & (n__6 : Relation_nodes_2) & (v = (fieldRead (fieldWrite Node_value tmp_1_13 value) n__6))))))});
(Relation_nodes_2 = (Relation_nodes Un {tmp_1_13}))|] ==>
    Relation_content_1 = Relation_content Un {(key, value)}"
by auto

end