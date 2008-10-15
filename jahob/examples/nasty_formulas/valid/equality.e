% original : ([|((SetIterBoundedArray_maxSize :: (obj => int)) = ((% (this::obj). (fieldRead (Array_length :: (obj => int)) (fieldRead (SetIterBoundedArray_a :: (obj => obj)) (this :: obj)))) :: (obj => int)));
% (token_NoOwner ~= token_Object);
% (token_NoOwner ~= token_Array);
% (token_NoOwner ~= token_String);
% (token_NoOwner ~= token_SetIterBoundedArray);
% (token_Object ~= token_Array);
% (token_Object ~= token_String);
% (token_Object ~= token_SetIterBoundedArray);
% (token_Array ~= token_String);
% (token_Array ~= token_SetIterBoundedArray);
% (token_String ~= token_SetIterBoundedArray);
% comment ''unalloc_lonely_SetIterBoundedArray'' (ALL (x::obj). ((((x :: obj) : (SetIterBoundedArray :: obj set)) & ((x :: obj) ~: (Object_alloc :: obj set))) --> ((fieldRead Object_owner x) = token_NoOwner)));
% comment ''unalloc_lonely_String'' (ALL (x::obj). ((((x :: obj) : (String :: obj set)) & ((x :: obj) ~: (Object_alloc :: obj set))) --> ((fieldRead Object_owner x) = token_NoOwner)));
% comment ''unalloc_lonely_Array'' (ALL (x::obj). ((((x :: obj) : (Array :: obj set)) & ((x :: obj) ~: (Object_alloc :: obj set))) --> ((fieldRead Object_owner x) = token_NoOwner)));
% comment ''unalloc_lonely_Object'' (ALL (x::obj). ((((x :: obj) : (Object :: obj set)) & ((x :: obj) ~: (Object_alloc :: obj set))) --> ((fieldRead Object_owner x) = token_NoOwner)));
% ((null :: obj) : (Object_alloc :: obj set));
% (((Object Int Array) :: obj set) = ({null} :: obj set));
% (((Object Int String) :: obj set) = ({null} :: obj set));
% (((Object Int SetIterBoundedArray) :: obj set) = ({null} :: obj set));
% (((Array Int String) :: obj set) = ({null} :: obj set));
% (((Array Int SetIterBoundedArray) :: obj set) = ({null} :: obj set));
% (((String Int SetIterBoundedArray) :: obj set) = ({null} :: obj set));
% (ALL (this::obj). comment ''BasicIntegrity'' ((fieldRead (SetIterBoundedArray_init :: (obj => bool)) (this :: obj)) --> (((0 :: int) <= ((fieldRead (SetIterBoundedArray_size :: (obj => int)) (this :: obj)) :: int)) & (((fieldRead (SetIterBoundedArray_size :: (obj => int)) (this :: obj)) :: int) <= ((fieldRead (SetIterBoundedArray_maxSize :: (obj => int)) (this :: obj)) :: int)) & ((null :: obj) ~: ((fieldRead (SetIterBoundedArray_content :: (obj => (obj set))) (this :: obj)) :: obj set)))));
% (ALL (this::obj). ((fieldRead (SetIterBoundedArray_init :: (obj => bool)) this) --> ((((fieldRead (SetIterBoundedArray_a :: (obj => obj)) this) :: obj) ~= (null :: obj)) & ((fieldRead Object_owner (fieldRead (SetIterBoundedArray_a :: (obj => obj)) this)) = token_SetIterBoundedArray))));
% comment ''valuesNonNull'' (ALL (this::obj) (i::int). (((fieldRead (SetIterBoundedArray_init :: (obj => bool)) this) & ((this :: obj) : (Object_alloc :: obj set)) & ((0 :: int) <= (i :: int)) & ((this :: obj) : (SetIterBoundedArray :: obj set)) & (intless i (fieldRead (SetIterBoundedArray_size :: (obj => int)) this))) --> (((arrayRead (Array_arrayState :: (obj => ((int => obj)))) (fieldRead (SetIterBoundedArray_a :: (obj => obj)) this) i) :: obj) ~= (null :: obj))));
% comment ''arraysDisjoint'' (ALL (ma1::obj) (ma2::obj). (((fieldRead (SetIterBoundedArray_init :: (obj => bool)) ma1) & ((ma1 :: obj) : (Object_alloc :: obj set)) & ((ma2 :: obj) : (SetIterBoundedArray :: obj set)) & (fieldRead (SetIterBoundedArray_init :: (obj => bool)) ma2) & ((ma2 :: obj) : (Object_alloc :: obj set)) & ((ma1 :: obj) : (SetIterBoundedArray :: obj set)) & (((fieldRead (SetIterBoundedArray_a :: (obj => obj)) ma1) :: obj) = ((fieldRead (SetIterBoundedArray_a :: (obj => obj)) ma2) :: obj))) --> ((ma1 :: obj) = (ma2 :: obj))));
% comment ''noDuplicates'' (ALL (this::obj) (i::int) (j::int). ((((0 :: int) <= (j :: int)) & ((this :: obj) : (Object_alloc :: obj set)) & (fieldRead (SetIterBoundedArray_init :: (obj => bool)) this) & (intless j (fieldRead (SetIterBoundedArray_size :: (obj => int)) this)) & (intless i (fieldRead (SetIterBoundedArray_size :: (obj => int)) this)) & ((this :: obj) : (SetIterBoundedArray :: obj set)) & ((0 :: int) <= (i :: int)) & (((arrayRead (Array_arrayState :: (obj => ((int => obj)))) (fieldRead (SetIterBoundedArray_a :: (obj => obj)) this) i) :: obj) = ((arrayRead (Array_arrayState :: (obj => ((int => obj)))) (fieldRead (SetIterBoundedArray_a :: (obj => obj)) this) j) :: obj))) --> ((i :: int) = (j :: int))));
% ((x :: obj) ~: ((fieldRead (SetIterBoundedArray_content :: (obj => (obj set))) (this :: obj)) :: obj set));
% (fieldRead (SetIterBoundedArray_init :: (obj => bool)) (this :: obj));
% ((x :: obj) ~= (null :: obj));
% (intless (fieldRead (SetIterBoundedArray_size :: (obj => int)) (this :: obj)) (fieldRead (SetIterBoundedArray_maxSize :: (obj => int)) (this :: obj)));
% ((SetIterBoundedArray_content :: (obj => (obj set))) = ((% (this::obj). {n. (EX (i::int). (((0 :: int) <= (i :: int)) & (intless i (fieldRead (SetIterBoundedArray_size :: (obj => int)) (this :: obj))) & ((n :: obj) = ((arrayRead (Array_arrayState :: (obj => ((int => obj)))) (fieldRead (SetIterBoundedArray_a :: (obj => obj)) (this :: obj)) i) :: obj))))}) :: (obj => (obj set))));
% comment ''thisNotNull'' ((this :: obj) ~= (null :: obj));
% comment ''x_type'' ((x :: obj) : (Object :: obj set));
% comment ''x_type'' ((x :: obj) : (Object_alloc :: obj set));
% comment ''tmp_1_type'' ((tmp_1 :: obj) : (Array :: obj set));
% comment ''tmp_1_type'' ((tmp_1 :: obj) : (Object_alloc :: obj set));
% comment ''thisType'' ((this :: obj) : (SetIterBoundedArray :: obj set));
% comment ''thisType'' ((this :: obj) : (Object_alloc :: obj set));
% ((SetIterBoundedArray_content_5 :: (obj => (obj set))) = ((% (this__5::obj). {n. (EX (i::int). (((0 :: int) <= (i :: int)) & (intless i (fieldRead (SetIterBoundedArray_size :: (obj => int)) (this__5 :: obj))) & ((n :: obj) = ((arrayRead ((arrayWrite (Array_arrayState :: (obj => ((int => obj)))) ((fieldRead (SetIterBoundedArray_a :: (obj => obj)) (this :: obj)) :: obj) ((fieldRead (SetIterBoundedArray_size :: (obj => int)) (this :: obj)) :: int) (x :: obj)) :: (obj => (int => obj))) (fieldRead (SetIterBoundedArray_a :: (obj => obj)) (this__5 :: obj)) i) :: obj))))}) :: (obj => (obj set))));
% ((SetIterBoundedArray_content_1 :: (obj => (obj set))) = ((% (this__4::obj). {n. (EX (i::int). (((0 :: int) <= (i :: int)) & (intless i (fieldRead ((fieldWrite (SetIterBoundedArray_size :: (obj => int)) (this :: obj) ((intplus ((fieldRead (SetIterBoundedArray_size :: (obj => int)) (this :: obj)) :: int) (1 :: int)) :: int)) :: (obj => int)) (this__4 :: obj))) & ((n :: obj) = ((arrayRead ((arrayWrite (Array_arrayState :: (obj => ((int => obj)))) ((fieldRead (SetIterBoundedArray_a :: (obj => obj)) (this :: obj)) :: obj) ((fieldRead (SetIterBoundedArray_size :: (obj => int)) (this :: obj)) :: int) (x :: obj)) :: (obj => (int => obj))) (fieldRead (SetIterBoundedArray_a :: (obj => obj)) (this__4 :: obj)) i) :: obj))))}) :: (obj => (obj set))))|] ==>
%     ((((fieldRead (SetIterBoundedArray_content :: (obj => (obj set))) (this :: obj)) Un {(x :: obj)}) :: obj set) = ((fieldRead (SetIterBoundedArray_content_1 :: (obj => (obj set))) (this :: obj)) :: obj set))) 


fof(axiom_tptp_1, axiom, is_int(0)).

fof(axiom_tptp_2, axiom, is_int(1)).

fof(axiom_tptp_3, axiom, lt(0, 1)).

fof(axiom_tptp_4, axiom, ! [X] : gteq(X,X)).

fof(axiom_tptp_5, axiom, ! [X] : lteq(X,X)).

fof(axiom_tptp_6, axiom, ! [X, Y] : (lt(X,Y) => lteq(X,Y))).

fof(axiom_tptp_7, axiom, ! [X, Y] : (gt(X,Y) => gteq(X,Y))).

fof(axiom_tptp_8, axiom, ! [X, Y] : (gteq(X,Y) <=> (~lt(X,Y)))).

fof(axiom_tptp_9, axiom, ! [X, Y] : (lteq(X,Y) <=> (~gt(X,Y)))).

fof(axiom_tptp_10, axiom, ! [X, Y] : (lt(X,Y) <=> gt(Y,X))).

fof(axiom_tptp_11, axiom, ! [X, Y] : (gteq(X,Y) <=> (lteq(Y,X)))).

fof(axiom_tptp_12, axiom, ! [X, Y, Z] : ((lteq(X,Y) & lt(Y,Z)) => lt(X,Z))).

fof(axiom_tptp_13, axiom, ! [X, Y, Z] : ((lt(X,Y) & lteq(Y,Z)) => lt(X,Z))).

fof(axiom_tptp_14, axiom, ! [X, Y] : ((lteq(X,Y) & lteq(Y,X)) => X=Y)).

fof(axiom_tptp_15, axiom, ! [X, Y] : (lt(X,Y) => ~(X=Y))).

fof(axiom_tptp_16, axiom, ! [X, Y] : ( lteq(X, minus(Y, 1)) <=> lt(X,Y) )).

fof(axiom_tptp_17, axiom, ! [X, Y] : ( lt(X, Y) <=> lteq(plus(X, 1),Y) ) ).

fof(axiom_tptp_18, axiom, ! [X, Y, Z, T] : ( (lteq(X,Y) & lteq(Z, T)) => lteq(plus(X,Z), plus(Y,T)) )).

fof(axiom_tptp_19, axiom, ! [X, Y, Z, T] : ( (lteq(X,Y) & lteq(Z, T)) => lteq(minus(X,T), minus(Y,Z)) )).

fof(axiom_tptp_20, axiom, ! [X, Y] : ( plus(X,Y) = plus(Y,X) )).

fof(axiom_tptp_21, axiom, ! [X] : ( plus(X,0) = X )).

fof(axiom_tptp_22, axiom, ! [X] : ( minus(X,0) = X )).

fof(axiom_tptp_23, axiom, ! [X] : ( minus(X,X) = 0 )).

% (token_NoOwner ~= token_Object)

fof(hyp_tptp_24, hypothesis, ~(token_NoOwner = token_Object)).


% (token_NoOwner ~= token_Array)

fof(hyp_tptp_25, hypothesis, ~(token_NoOwner = token_Array)).


% (token_NoOwner ~= token_String)

fof(hyp_tptp_26, hypothesis, ~(token_NoOwner = token_String)).


% (token_NoOwner ~= token_SetIterBoundedArray)

fof(hyp_tptp_27, hypothesis, ~(token_NoOwner = token_SetIterBoundedArray)).


% (token_Object ~= token_Array)

fof(hyp_tptp_28, hypothesis, ~(token_Object = token_Array)).


% (token_Object ~= token_String)

fof(hyp_tptp_29, hypothesis, ~(token_Object = token_String)).


% (token_Object ~= token_SetIterBoundedArray)

fof(hyp_tptp_30, hypothesis, ~(token_Object = token_SetIterBoundedArray)).


% (token_Array ~= token_String)

fof(hyp_tptp_31, hypothesis, ~(token_Array = token_String)).


% (token_Array ~= token_SetIterBoundedArray)

fof(hyp_tptp_32, hypothesis, ~(token_Array = token_SetIterBoundedArray)).


% (token_String ~= token_SetIterBoundedArray)

fof(hyp_tptp_33, hypothesis, ~(token_String = token_SetIterBoundedArray)).


% (ALL (x__29::obj). (((x__29 : SetIterBoundedArray) & (x__29 ~: Object_alloc)) --> ((Object_owner x__29) = token_NoOwner)))

fof(hyp_tptp_34, hypothesis, (! [X__29] : (((~setIterBoundedArray(X__29) | object_alloc(X__29)) | (token_NoOwner = object_owner(X__29)))))).


% (ALL (x__28::obj). (((x__28 : String) & (x__28 ~: Object_alloc)) --> ((Object_owner x__28) = token_NoOwner)))

fof(hyp_tptp_35, hypothesis, (! [X__28] : (((~string(X__28) | object_alloc(X__28)) | (token_NoOwner = object_owner(X__28)))))).


% (ALL (x__27::obj). (((x__27 : Array) & (x__27 ~: Object_alloc)) --> ((Object_owner x__27) = token_NoOwner)))

fof(hyp_tptp_36, hypothesis, (! [X__27] : (((~array(X__27) | object_alloc(X__27)) | (token_NoOwner = object_owner(X__27)))))).


% (ALL (x__26::obj). (((x__26 : Object) & (x__26 ~: Object_alloc)) --> ((Object_owner x__26) = token_NoOwner)))

fof(hyp_tptp_37, hypothesis, (! [X__26] : (((~object(X__26) | object_alloc(X__26)) | (token_NoOwner = object_owner(X__26)))))).


% (null : Object_alloc)

fof(hyp_tptp_38, hypothesis, object_alloc(null)).


% ((Object Int Array) === {null})

fof(hyp_tptp_39, hypothesis, ((! [Z_setinc_foltrans_54] : (((~object(Z_setinc_foltrans_54) | ~array(Z_setinc_foltrans_54)) | (Z_setinc_foltrans_54 = null)))) & (! [Z_setinc_foltrans_53] : ((~(Z_setinc_foltrans_53 = null) | (object(Z_setinc_foltrans_53) & array(Z_setinc_foltrans_53))))))).


% ((Object Int String) === {null})

fof(hyp_tptp_40, hypothesis, ((! [Z_setinc_foltrans_52] : (((~object(Z_setinc_foltrans_52) | ~string(Z_setinc_foltrans_52)) | (Z_setinc_foltrans_52 = null)))) & (! [Z_setinc_foltrans_51] : ((~(Z_setinc_foltrans_51 = null) | (object(Z_setinc_foltrans_51) & string(Z_setinc_foltrans_51))))))).


% ((Object Int SetIterBoundedArray) === {null})

fof(hyp_tptp_41, hypothesis, ((! [Z_setinc_foltrans_50] : (((~object(Z_setinc_foltrans_50) | ~setIterBoundedArray(Z_setinc_foltrans_50)) | (Z_setinc_foltrans_50 = null)))) & (! [Z_setinc_foltrans_49] : ((~(Z_setinc_foltrans_49 = null) | (object(Z_setinc_foltrans_49) & setIterBoundedArray(Z_setinc_foltrans_49))))))).


% ((Array Int String) === {null})

fof(hyp_tptp_42, hypothesis, ((! [Z_setinc_foltrans_48] : (((~array(Z_setinc_foltrans_48) | ~string(Z_setinc_foltrans_48)) | (Z_setinc_foltrans_48 = null)))) & (! [Z_setinc_foltrans_47] : ((~(Z_setinc_foltrans_47 = null) | (array(Z_setinc_foltrans_47) & string(Z_setinc_foltrans_47))))))).


% ((Array Int SetIterBoundedArray) === {null})

fof(hyp_tptp_43, hypothesis, ((! [Z_setinc_foltrans_46] : (((~array(Z_setinc_foltrans_46) | ~setIterBoundedArray(Z_setinc_foltrans_46)) | (Z_setinc_foltrans_46 = null)))) & (! [Z_setinc_foltrans_45] : ((~(Z_setinc_foltrans_45 = null) | (array(Z_setinc_foltrans_45) & setIterBoundedArray(Z_setinc_foltrans_45))))))).


% ((String Int SetIterBoundedArray) === {null})

fof(hyp_tptp_44, hypothesis, ((! [Z_setinc_foltrans_44] : (((~string(Z_setinc_foltrans_44) | ~setIterBoundedArray(Z_setinc_foltrans_44)) | (Z_setinc_foltrans_44 = null)))) & (! [Z_setinc_foltrans_43] : ((~(Z_setinc_foltrans_43 = null) | (string(Z_setinc_foltrans_43) & setIterBoundedArray(Z_setinc_foltrans_43))))))).


% (ALL (this__23::obj). comment ''BasicIntegrity'' ((SetIterBoundedArray_init this__23) --> ((0 <= (SetIterBoundedArray_size this__23)) & ((SetIterBoundedArray_size this__23) <= (Array_length (SetIterBoundedArray_a this__23))) & (null ~: {n. (EX (i::int). ((0 <= i) & (intless i (SetIterBoundedArray_size this__23)) & (n = (arrayRead Array_arrayState (SetIterBoundedArray_a this__23) i))))}))))

fof(hyp_tptp_45, hypothesis, (! [This__23] : ((~setIterBoundedArray_init(This__23) | ((? [Fun_flat_foltrans_37] : ((lteq(0, Fun_flat_foltrans_37) & (Fun_flat_foltrans_37 = setIterBoundedArray_size(This__23))))) & (? [Fun_flat_foltrans_39, Fun_flat_foltrans_38] : ((lteq(Fun_flat_foltrans_39, Fun_flat_foltrans_38) & (Fun_flat_foltrans_39 = setIterBoundedArray_size(This__23)) & (? [T_eqof_foltrans_40] : (((T_eqof_foltrans_40 = setIterBoundedArray_a(This__23)) & (Fun_flat_foltrans_38 = array_length(T_eqof_foltrans_40)))))))) & (! [I] : ((~lteq(0, I) | (? [Fun_flat_foltrans_41] : (((Fun_flat_foltrans_41 = setIterBoundedArray_size(This__23)) & ~lt(I, Fun_flat_foltrans_41)))) | (? [T_eqof_foltrans_42] : (((T_eqof_foltrans_42 = setIterBoundedArray_a(This__23)) & ~(null = array_arrayState(T_eqof_foltrans_42, I))))))))))))).


% (ALL (this__22::obj). ((SetIterBoundedArray_init this__22) --> (((SetIterBoundedArray_a this__22) ~= null) & ((Object_owner (SetIterBoundedArray_a this__22)) = token_SetIterBoundedArray))))

fof(hyp_tptp_46, hypothesis, (! [This__22] : ((~setIterBoundedArray_init(This__22) | (~(null = setIterBoundedArray_a(This__22)) & (? [T_eqof_foltrans_35] : (((T_eqof_foltrans_35 = setIterBoundedArray_a(This__22)) & (token_SetIterBoundedArray = object_owner(T_eqof_foltrans_35)))))))))).


% (ALL (i::int) (this__21::obj). (((SetIterBoundedArray_init this__21) & (this__21 : Object_alloc) & (0 <= i) & (this__21 : SetIterBoundedArray) & (intless i (SetIterBoundedArray_size this__21))) --> ((arrayRead Array_arrayState (SetIterBoundedArray_a this__21) i) ~= null)))

fof(hyp_tptp_47, hypothesis, (! [I, This__21] : (((~setIterBoundedArray_init(This__21) | ~object_alloc(This__21) | gt(0, I) | ~setIterBoundedArray(This__21) | (? [Fun_flat_foltrans_33] : ((gteq(I, Fun_flat_foltrans_33) & (Fun_flat_foltrans_33 = setIterBoundedArray_size(This__21)))))) | (? [T_eqof_foltrans_34] : (((T_eqof_foltrans_34 = setIterBoundedArray_a(This__21)) & ~(null = array_arrayState(T_eqof_foltrans_34, I))))))))).


% (ALL (ma2::obj) (ma1::obj). (((SetIterBoundedArray_init ma1) & (ma1 : Object_alloc) & (ma2 : SetIterBoundedArray) & (SetIterBoundedArray_init ma2) & (ma2 : Object_alloc) & (ma1 : SetIterBoundedArray) & ((SetIterBoundedArray_a ma1) = (SetIterBoundedArray_a ma2))) --> (ma1 = ma2)))

fof(hyp_tptp_48, hypothesis, (! [Ma2, Ma1] : (((~setIterBoundedArray_init(Ma1) | ~object_alloc(Ma1) | ~setIterBoundedArray(Ma2) | ~setIterBoundedArray_init(Ma2) | ~object_alloc(Ma2) | ~setIterBoundedArray(Ma1) | (? [T_eqof_foltrans_32] : (((T_eqof_foltrans_32 = setIterBoundedArray_a(Ma1)) & ~(T_eqof_foltrans_32 = setIterBoundedArray_a(Ma2)))))) | (Ma1 = Ma2))))).


% (ALL (j::int) (i::int) (this__20::obj). (((0 <= j) & (this__20 : Object_alloc) & (SetIterBoundedArray_init this__20) & (intless j (SetIterBoundedArray_size this__20)) & (intless i (SetIterBoundedArray_size this__20)) & (this__20 : SetIterBoundedArray) & (0 <= i) & ((arrayRead Array_arrayState (SetIterBoundedArray_a this__20) i) = (arrayRead Array_arrayState (SetIterBoundedArray_a this__20) j))) --> (i = j)))

fof(hyp_tptp_49, hypothesis, (! [J, I, This__20] : (((gt(0, J) | ~object_alloc(This__20) | ~setIterBoundedArray_init(This__20) | (? [Fun_flat_foltrans_27] : ((gteq(J, Fun_flat_foltrans_27) & (Fun_flat_foltrans_27 = setIterBoundedArray_size(This__20))))) | (? [Fun_flat_foltrans_28] : ((gteq(I, Fun_flat_foltrans_28) & (Fun_flat_foltrans_28 = setIterBoundedArray_size(This__20))))) | ~setIterBoundedArray(This__20) | gt(0, I) | (? [T_eqof_foltrans_29] : (((? [T_eqof_foltrans_30] : (((T_eqof_foltrans_30 = setIterBoundedArray_a(This__20)) & (T_eqof_foltrans_29 = array_arrayState(T_eqof_foltrans_30, I))))) & (? [T_eqof_foltrans_31] : (((T_eqof_foltrans_31 = setIterBoundedArray_a(This__20)) & ~(T_eqof_foltrans_29 = array_arrayState(T_eqof_foltrans_31, J))))))))) | (I = J))))).


% (x ~: {n. (EX (i::int). ((0 <= i) & (intless i (SetIterBoundedArray_size this)) & (n = (arrayRead Array_arrayState (SetIterBoundedArray_a this) i))))})

fof(hyp_tptp_50, hypothesis, (! [I] : ((~lteq(0, I) | (? [Fun_flat_foltrans_25] : (((Fun_flat_foltrans_25 = setIterBoundedArray_size(this)) & ~lt(I, Fun_flat_foltrans_25)))) | (? [T_eqof_foltrans_26] : (((T_eqof_foltrans_26 = setIterBoundedArray_a(this)) & ~(x = array_arrayState(T_eqof_foltrans_26, I))))))))).


% (SetIterBoundedArray_init this)

fof(hyp_tptp_51, hypothesis, setIterBoundedArray_init(this)).


% (x ~= null)

fof(hyp_tptp_52, hypothesis, ~(x = null)).


% (intless (SetIterBoundedArray_size this) (Array_length (SetIterBoundedArray_a this)))

fof(hyp_tptp_53, hypothesis, (? [Fun_flat_foltrans_22, Fun_flat_foltrans_21] : ((lt(Fun_flat_foltrans_22, Fun_flat_foltrans_21) & (Fun_flat_foltrans_22 = setIterBoundedArray_size(this)) & (? [T_eqof_foltrans_23] : (((T_eqof_foltrans_23 = setIterBoundedArray_a(this)) & (Fun_flat_foltrans_21 = array_length(T_eqof_foltrans_23))))))))).


% (this ~= null)

fof(hyp_tptp_54, hypothesis, ~(this = null)).


% (x : Object)

fof(hyp_tptp_55, hypothesis, object(x)).


% (x : Object_alloc)

fof(hyp_tptp_56, hypothesis, object_alloc(x)).


% (tmp_1 : Array)

fof(hyp_tptp_57, hypothesis, array(tmp_1)).


% (tmp_1 : Object_alloc)

fof(hyp_tptp_58, hypothesis, object_alloc(tmp_1)).


% (this : SetIterBoundedArray)

fof(hyp_tptp_59, hypothesis, setIterBoundedArray(this)).


% (this : Object_alloc)

fof(hyp_tptp_60, hypothesis, object_alloc(this)).



% (({n. (EX (i::int). ((0 <= i) & (intless i (SetIterBoundedArray_size this)) & (n = (arrayRead Array_arrayState (SetIterBoundedArray_a this) i))))} Un {x}) === {n. (EX (i::int). ((0 <= i) & (intless i ((fieldWrite SetIterBoundedArray_size this (intplus (SetIterBoundedArray_size this) 1)) this)) & (n = (arrayRead (arrayWrite Array_arrayState (SetIterBoundedArray_a this) (SetIterBoundedArray_size this) x) (SetIterBoundedArray_a this) i))))})

fof(goal, conjecture, (

(! [Z_setinc_foltrans_2] : ((((! [I] : ((~lteq(0, I) | (! [Fun_flat_foltrans_7] : ((~lt(I, Fun_flat_foltrans_7) | ~(Fun_flat_foltrans_7 = setIterBoundedArray_size(this))))) | (! [T_eqof_foltrans_8] : ((~(T_eqof_foltrans_8 = setIterBoundedArray_a(this)) | ~(Z_setinc_foltrans_2 = array_arrayState(T_eqof_foltrans_8, I)))))))) & ~(Z_setinc_foltrans_2 = x)) | (? [I] : ((lteq(0, I) & (! [Fun_flat_foltrans_9] : (((? [Fun_flat_foltrans_10] : (((Fun_flat_foltrans_10 = setIterBoundedArray_size(this)) & ~(Fun_flat_foltrans_9 = plus(Fun_flat_foltrans_10, 1))))) | lt(I, Fun_flat_foltrans_9)))) & (((! [T_eqof_foltrans_11] : ((~(T_eqof_foltrans_11 = setIterBoundedArray_a(this)) | (T_eqof_foltrans_11 = setIterBoundedArray_a(this))))) & (I = setIterBoundedArray_size(this)) & (Z_setinc_foltrans_2 = x)) | (((! [T_eqof_foltrans_12] : ((~(T_eqof_foltrans_12 = setIterBoundedArray_a(this)) | ~(T_eqof_foltrans_12 = setIterBoundedArray_a(this))))) | ~(I = setIterBoundedArray_size(this))) & (! [T_eqof_foltrans_13] : ((~(T_eqof_foltrans_13 = setIterBoundedArray_a(this)) | (Z_setinc_foltrans_2 = array_arrayState(T_eqof_foltrans_13, I))))))))))))) 

& 

(! [Z_setinc_foltrans_1] : (((! [I] : ((~lteq(0, I) | (! [Fun_flat_foltrans_14] : ((~lt(I, Fun_flat_foltrans_14) | (! [Fun_flat_foltrans_15] : ((~(Fun_flat_foltrans_14 = plus(Fun_flat_foltrans_15, 1)) | ~(Fun_flat_foltrans_15 = setIterBoundedArray_size(this)))))))) | (((! [T_eqof_foltrans_16] : ((~(T_eqof_foltrans_16 = setIterBoundedArray_a(this)) | ~(T_eqof_foltrans_16 = setIterBoundedArray_a(this))))) | ~(I = setIterBoundedArray_size(this)) | ~(Z_setinc_foltrans_1 = x)) & (((! [T_eqof_foltrans_17] : ((~(T_eqof_foltrans_17 = setIterBoundedArray_a(this)) | (T_eqof_foltrans_17 = setIterBoundedArray_a(this))))) & (I = setIterBoundedArray_size(this))) | (! [T_eqof_foltrans_18] : ((~(T_eqof_foltrans_18 = setIterBoundedArray_a(this)) | ~(Z_setinc_foltrans_1 = array_arrayState(T_eqof_foltrans_18, I)))))))))) | ((? [I] : ((lteq(0, I) & (! [Fun_flat_foltrans_19] : ((~(Fun_flat_foltrans_19 = setIterBoundedArray_size(this)) | lt(I, Fun_flat_foltrans_19)))) & (! [T_eqof_foltrans_20] : ((~(T_eqof_foltrans_20 = setIterBoundedArray_a(this)) | (Z_setinc_foltrans_1 = array_arrayState(T_eqof_foltrans_20, I)))))))) | (Z_setinc_foltrans_1 = x)))))

)).