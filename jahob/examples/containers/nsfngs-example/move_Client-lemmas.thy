theory move_Client_lemmas = Jahob:

lemma Client_move_InitialPartOfProcedure4: "([|
(token_NoOwner ~= token_List);
(Client_b : List);
(Client_a : List);
(Client_a ~= null);
(Client_a ~= Client_b);
(Client_b : Object_alloc);
((fieldRead Object_owner Client_b) = token_NoOwner);
((fieldRead Object_owner Client_a) = token_NoOwner);
(Client_a : Object_alloc);
(Client_b ~= null);
(Object_alloc \<subseteq> Object_alloc_9);
(Object_alloc_9 \<subseteq> Object_alloc_5);
(Object_alloc_5 \<subseteq> Object_alloc_1);
(ALL framedObj. ((((fieldRead Object_owner framedObj) ~= token_List) & (framedObj : List) & (framedObj : Object_alloc_1) & (framedObj ~= Client_a)) --> ((fieldRead List_content_2 framedObj) = (fieldRead List_content framedObj))))|] ==>
    ((fieldRead List_content_2 Client_b) = (fieldRead List_content Client_b)))"
apply auto
done

lemma Client_move_InitialPartOfProcedure7: "([|
(Client_init --> (((fieldRead List_content Client_a) Int (fieldRead List_content Client_b)) = {}));
Client_init;
comment ''tmp_3_type'' (tmp_3 : Object);
comment ''tmp_3_type'' (tmp_3 : Object_alloc);
(Client_a ~= null);
(Client_a ~= Client_b);
(Client_b : Object_alloc);
((fieldRead Object_owner Client_b) = token_NoOwner);
((fieldRead Object_owner Client_a) = token_NoOwner);
(Client_a : Object_alloc);
(Client_b ~= null);
comment ''oa_type'' (oa : Object);
comment ''oa_type'' (oa : Object_alloc);
(result_10 = (ALL x. (x ~: (fieldRead List_content Client_a))));
(Object_alloc \<subseteq> Object_alloc_9);
(~result_10);
(result_6 : (fieldRead List_content Client_a));
(Object_alloc_9 \<subseteq> Object_alloc_5);
((fieldRead List_content_2 Client_a) = ((fieldRead List_content Client_a) \<setminus> {result_6}));
(Object_alloc_5 \<subseteq> Object_alloc_1);
((fieldRead List_content_2 Client_b) = (fieldRead List_content Client_b))|] ==>
    (((fieldRead List_content_2 Client_a) Int (fieldRead List_content_2 Client_b)) = {}))"
apply auto
done

end