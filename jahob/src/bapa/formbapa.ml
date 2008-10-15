(** Convert a BAPA formula from {!Form.form} into {!Alpha.form}. *)

open Form
open FormUtil

let rec genPairs (xs0 : 'a list) : ('a * 'a) list = match xs0 with
  | [] -> []
  | [x] -> []
  | (x :: xs) ->
      let tailpairs = genPairs xs in
      let hdpairs = List.map (fun y -> (x, y)) xs in
	List.append hdpairs tailpairs

let warn (msg : string) = print_string (msg ^ "\n")
let panic (msg : string) = failwith msg

(* let typedIdentToIdent (iden, _) = iden *)
let typedIdentToIdent = fst

(*
  translating Form.form to Alpha.form along with list of variables 
  representing elements involving in membership relation (Elem)
*)
let rec formToBapaHelper (f0 : form) : (Alpha.form * ident list) = match f0 with
  | Binder (binder, tvids, f1) ->
      let (bf1, vs) = formToBapaHelper f1 in
	varToSet binder tvids vs bf1
	(*
	  let bf2 = List.fold_right 
	  (fun tvid -> fun bf -> Alpha.Bind (transBinder binder tvid, typedIdentToIdent tvid, bf))
	  tvids bf1 in
	  bf2
	*)
	  
  | App (f1, fs) -> transApp f1 fs

  | Const c ->
      begin
	match c with
	  | (BoolConst b) -> 
	      if b then
		(Alpha.Less (Alpha.Const 0, Alpha.Const 1), [])
	      else
		(Alpha.Less (Alpha.Const 1, Alpha.Const 0), [])
	  |  _ -> panic "formbapa:formToBapa: called with non-boolean constant parameter"
      end

  | Var iden -> panic ("formbapa:formToBapa: called with Var " ^ iden ^ " parameter")
  | TypedForm (f, ft) -> formToBapaHelper f
      

(*
  Converting quantified variables (qvars0) that take part in membership
  constraint (those that are in vars0) into quantified singleton sets.

  Return value: transformed formula and the rest of the variables
  to be transformed by outer binders
*)
and varToSet (binder : binderKind) (qvars0 : typedIdent list) (vars0 : ident list) (f0 : Alpha.form) : (Alpha.form * ident list) =
  let rec varToSetHelper qvars1 f1 xvars = match qvars1 with
    | [] -> (f1, xvars)
    | qvar :: qvars ->
	begin
	  if List.mem (fst qvar) vars0 then
	    (* convert this element variable into a singleton set with the same name *)
	    begin
	      match binder with
		| Forall ->
		    let (f2, xvars1) = varToSetHelper qvars f1 xvars in
		      (Alpha.Bind (Alpha.Forallset, fst qvar, 
				   Alpha.Impl (Alpha.Inteq (Alpha.Card (Alpha.Setvar (fst qvar)), 
							    Alpha.Const 1), f2)),
		       (fst qvar) :: xvars1)
		| Exists ->
		    let (f2, xvars1) = varToSetHelper qvars f1 xvars in
		      (Alpha.Bind (Alpha.Existsset, fst qvar, 
				   Alpha.And [Alpha.Inteq (Alpha.Card (Alpha.Setvar (fst qvar)), 
							   Alpha.Const 1); f2]),
		       (fst qvar) :: xvars1)
		| _ -> panic "formbapa:varToSet: unsupported binder kind"
	    end
	  else
	    let (f2, xvars1) = varToSetHelper qvars f1 xvars in
	      (Alpha.Bind (transBinder binder qvar, fst qvar, f2), xvars1)
	end
  in
  let (f, xvars) = varToSetHelper qvars0 f0 [] in
    (f, List.filter (fun v -> not (List.mem v xvars)) vars0)


and transBinder b (iden, typform) = match b with
  | Forall ->
      begin
	match typform with
	  | TypeApp (TypeSet, _) -> Alpha.Forallset
	  | TypeApp (TypeInt, _) -> Alpha.Forallint
	  | _ -> panic ("formbapa:transBinder: unsupported binder type for variable " ^ iden)
      end
  | Exists ->
      begin
	match typform with
	  | TypeApp (TypeSet, _) -> Alpha.Existsset
	  | TypeApp (TypeInt, _) -> Alpha.Existsint
	  | _ -> panic ("formbapa:transBinder: unsupported binder type " ^ iden)
      end
  | _ -> panic ("formbapa:transBinder: Comprehension/Lambda not supported for variable " ^ iden)

 
and transApp (c1 : form) (fs : form list) : (Alpha.form * ident list) = match c1 with
  | Const And -> 
      begin
	if List.length fs <= 1 then
	  warn ("formbapa:transApp: And received " ^ (string_of_int (List.length fs)) ^ " parameters");
	let (fs2, vs2) = List.split (List.map formToBapaHelper fs) in
	  (Alpha.And fs2, List.concat vs2)
      end;
  | Const Or -> 
      begin
	if List.length fs <= 1 then
	  warn ("formbapa:transApp: Or received " ^ (string_of_int (List.length fs)) ^ " parameters");
	let (fs2, vs2) = List.split (List.map formToBapaHelper fs) in
	  (Alpha.Or fs2, List.concat vs2)
      end;
  | Const Not -> 
      begin
	if List.length fs != 1 then
	  panic ("formbapa:transApp: Not needs 1 parameter, received " ^ (string_of_int (List.length fs)))
	else
	  let (f2, vs2) = formToBapaHelper (List.hd fs) in
	    (Alpha.Not f2, vs2)
      end;

  | Const Impl -> 
      if List.length fs != 2 then
	panic ("formbapa:transApp: implication needs 2 arguments, receiving " ^ 
		    (string_of_int (List.length fs)))
      else
	let (ante, avs) = formToBapaHelper (List.hd fs) in (* assuming first element implies the second one *)
	let (conseq, cvs) = formToBapaHelper (List.hd (List.tl fs)) in
	  (Alpha.Impl (ante, conseq), avs @ cvs)

  | Const Iff -> (* assuming Iff is applied to a set of formulae *)
      let (bfs, vss) = List.split (List.map formToBapaHelper fs) in
      let pairs = genPairs bfs in
      let iffs  = List.map (fun (f1, f2) -> 
			      Alpha.And [Alpha.Impl (f1, f2); Alpha.Impl (f2, f1)]) pairs in
	begin
	  if List.length fs <= 1 then
	    warn "formbapa:transApp: Iff is applied to 0 or 1 parameter\n";

	  if List.length iffs > 1 then
            (Alpha.And iffs, List.concat vss)
	  else
	    (List.hd iffs, List.concat vss)
	end;

  | Const Disjoint -> (* assuming Disjoint is applied to a set of set terms *)
      let sets = List.map transSetTerm fs in
      let pairs = genPairs sets in
      let djnts =List.map (fun (s1, s2) -> 
			     Alpha.Seteq (Alpha.Inter [s1; s2], Alpha.Emptyset)) pairs in 
	begin
	  if List.length fs <= 1 then
	    warn"formbapa:transApp: Disjoint is applied to 0 or 1 parameter\n";

	  if List.length djnts > 1 then
	    (Alpha.And djnts, [])
	  else
	    (List.hd djnts, [])
	end;

  | Const Seteq ->
      if List.length fs != 2 then
	panic ("formbapa:transApp: Subseteq needs two parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let s1 = transSetTerm (List.hd fs) in
	let s2 = transSetTerm (List.hd (List.tl fs)) in
	  (Alpha.Seteq (s1, s2), [])

  | Const Subseteq ->
      if List.length fs != 2 then
	panic ("formbapa:transApp: Subseteq needs two parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let s1 = transSetTerm (List.hd fs) in
	let s2 = transSetTerm (List.hd (List.tl fs)) in
	  (Alpha.Subseteq (s1, s2), [])

  | Const Subset ->
      if List.length fs != 2 then
	panic ("formbapa:transApp: Subset needs two parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let s1 = transSetTerm (List.hd fs) in
	let s2 = transSetTerm (List.hd (List.tl fs)) in
	  (Alpha.And [Alpha.Subseteq (s1, s2); Alpha.Not (Alpha.Seteq (s1, s2))], [])


  | Const Elem ->
      let _ = print_string ("\nWARNING: Elem should be eliminated during type inference\n") in
      if List.length fs != 2 then
	panic ("formbapa:transApp: Elem needs two parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let var0 = List.hd fs in
	  begin
	    match var0 with
	      | Var var ->
		  let s = transSetTerm (List.hd (List.tl fs)) in
		    (Alpha.Inteq (Alpha.Card (Alpha.Inter [Alpha.Setvar var; s]), Alpha.Const 1), [var])
	      | TypedForm (tf, _) -> transApp (Const Elem) (tf :: (List.tl fs))
	      | _ -> panic "formbapa:transApp: only <variable> \\in <set> form is suppoprted"
	  end
  | Const Cardeq ->
      let sets = List.map transSetTerm fs in
      let pairs = genPairs sets in
      let eqs = List.map (fun (s1, s2) -> Alpha.Inteq (Alpha.Card s1, Alpha.Card s2)) pairs in
	begin
	  if List.length fs <= 1 then
	    warn"formbapa:transApp: Cardeq is applied to 0 or 1 parameter\n";

	  if List.length eqs > 1 then
	    (Alpha.And eqs, [])
	  else
	    (List.hd eqs, [])
	end;

  | Const Cardleq ->
      if List.length fs != 2 then
	panic ("formbapa:transApp: Cardleq needs two parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let s1 = transSetTerm (List.hd fs) in
	let s2 = transSetTerm (List.hd (List.tl fs)) in
	  (Alpha.Leq (Alpha.Card s1, Alpha.Card s2), [])

  | Const Cardgeq ->
      if List.length fs != 2 then
	panic ("formbapa:transApp: Cardgeq needs two parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let s1 = transSetTerm (List.hd fs) in
	let s2 = transSetTerm (List.hd (List.tl fs)) in
	  (Alpha.Leq (Alpha.Card s2, Alpha.Card s1), [])

  | Const Lt -> (* The list of parameters are expected to be integer expressions *)
      if List.length fs != 2 then
	panic ("formbapa:transApp: Lt needs two parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let biterm1 = transIntTerm (List.hd fs) in
	let biterm2 = transIntTerm (List.hd (List.tl fs)) in
	  (Alpha.Less (biterm1, biterm2), [])

  | Const Gt ->
      if List.length fs != 2 then
	panic ("formbapa:transApp: Gt needs two parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let biterm1 = transIntTerm (List.hd fs) in
	let biterm2 = transIntTerm (List.hd (List.tl fs)) in
	  (Alpha.Less (biterm2, biterm1), [])

  | Const LtEq -> 
      if List.length fs != 2 then
	panic ("formbapa:transApp: LtEq needs two parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let biterm1 = transIntTerm (List.hd fs) in
	let biterm2 = transIntTerm (List.hd (List.tl fs)) in
	  (Alpha.Leq (biterm1, biterm2), [])

  | Const GtEq -> 
      if List.length fs != 2 then
	panic ("formbapa:transApp: GtEq needs 2 parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let biterm1 = transIntTerm (List.hd fs) in
	let biterm2 = transIntTerm (List.hd (List.tl fs)) in
	  (Alpha.Leq (biterm2, biterm1), [])

  | Const Eq -> 
      if List.length fs != 2 then
	panic ("formbapa:transApp: Eq needs 2 parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let biterm1 = transIntTerm (List.hd fs) in
	let biterm2 = transIntTerm (List.hd (List.tl fs)) in
	  (Alpha.Inteq (biterm2, biterm1), [])

  | Var fsym ->
      if fsym = "finite" then
	(Alpha.Less (Alpha.Const 0, Alpha.Const 1), [])
      else
	panic ("formbapa:transApp: can't translate predicate " ^ fsym)

  | _ -> panic ("formbapa:transApp: can't translate ")


and transIntTerm iterm0 = match iterm0 with
  | Var iden -> Alpha.Intvar iden

  | Const c ->
      begin
	match c with
	  | IntConst i -> Alpha.Const i
	  | _ -> panic ("formbapa:transIntTerm: non-integer constant " ^ (string_of_const c))
      end;
  
  | App (op, iterms) -> 
      begin
	match op with
	  | Const Plus ->
	      let biterms = List.map transIntTerm iterms in
		Alpha.Plus biterms

	  | Const Minus ->
	      if List.length iterms != 2 then
		panic ("formbapa:transIntTerm: Minus needs 2 parameters, received "
		       ^ (string_of_int (List.length iterms)))
	      else
		let biterm1 = transIntTerm (List.hd iterms) in
		let biterm2 = transIntTerm (List.hd (List.tl iterms)) in
		  Alpha.Minus (biterm1, biterm2)

	  | Const Mult -> (* expecting first an integer and then an intTerm *)
	      if List.length iterms != 2 then
		panic ("formbapa:transIntTerm: Mult needs 2 parameters, received "
		       ^ (string_of_int (List.length iterms)))
	      else
		let c = match (List.hd iterms) with 
		  | Const (IntConst i) -> i 
		  | _ -> panic "formbapa:transIntTerm: first argument of Mult must be integer constant"  in
		let biterm = transIntTerm (List.hd (List.tl iterms)) in
		  Alpha.Times (c, biterm)

	  | Const Card ->
	      if List.length iterms != 1 then
		panic ("frombapa:transIntTerm: cardinality operator needs one parameter, received " 
		       ^ (string_of_int (List.length iterms)))
	      else
		let s = transSetTerm (List.hd iterms) in
		  Alpha.Card s

	  | Const (IntConst i) -> Alpha.Const i

	  | Const Old -> transIntTerm (List.hd iterms)

	  | Var fsym -> panic ("formbapa:transIntTerm: can't translate function symbol " ^ fsym)

	  | _ -> panic ("formbapa:transIntTerm: can't translate App")
      end;
  | TypedForm (f, ft) -> transIntTerm f
  | _ -> panic ("formbapa:transIntTerm: can't translate")


and transSetTerm sterm0 = match sterm0 with
  | Var iden -> Alpha.Setvar iden
  | Const c -> 
      begin
	match c with
	  | EmptysetConst -> Alpha.Emptyset
	  | NullConst -> Alpha.Emptyset
	  | _ -> panic ("formbapa:transSetTerm: can't translate " ^ (string_of_const c))
      end;
  | App (op, sterms) -> 
      begin
	match op with
	  | Const Cap ->
	      let bsterms = List.map transSetTerm sterms in
		Alpha.Inter bsterms

	  | Const Cup ->
	      let bsterms = List.map transSetTerm sterms in
		Alpha.Union bsterms

	  | Const Diff | Const Minus ->
	      if List.length sterms != 2 then
		panic ("formbapa:transSetTerm: Diff needs 2 parameters, received "
		       ^ (string_of_int (List.length sterms)))
	      else
		let bsterm1 = transSetTerm (List.hd sterms) in
		let bsterm2 = transSetTerm (List.hd (List.tl sterms)) in 
		  Alpha.Inter [bsterm1; Alpha.Complement bsterm2]

	  | Const Old -> transSetTerm (List.hd sterms)

	  | Var fsym -> panic ("formbapa:transIntTerm: can't translate function symbol " ^ fsym)

	  | _ -> panic ("formbapa:transSetTerm: can't translate App")
      end;
  | TypedForm (f, ft) -> transSetTerm f
  | _ -> panic ("formbapa:transSetTerm: can't translate")


let rec simplifyHelper candidates excands f0 = match f0 with
  | TypedForm (f, tf) -> TypedForm (simplifyHelper candidates excands f, tf)
  | Binder (Forall, tvids, f) ->
      begin
	let simpf  = simplifyHelper ((List.map fst tvids) @ candidates) excands f in
	let fvs = fv simpf in
	  smk_foralls (List.filter (fun tv -> List.mem (fst tv) fvs) tvids, simpf)
      end
  | Binder (Exists, tvids, f) ->
      begin
	let simpf  = simplifyHelper candidates ((List.map fst tvids) @ excands) f in
	let fvs = fv simpf in
	  smk_exists (List.filter (fun tv -> List.mem (fst tv) fvs) tvids, simpf)
      end
  | App (Const Impl, fs) ->
      begin
	if List.length candidates > 0 && List.length fs = 2 then
	  let simpf = smk_impl_eq2 candidates excands (List.hd fs, List.hd (List.tl fs)) in
	  let _ = print_string ("\nsimplified:\n" ^ (PrintForm.string_of_form simpf)) in
	    simpf
	else
	  f0
      end
  | _ -> f0


let simplifyForm (f0 : form) : form = simplifyHelper [] [] f0

let formToBapa (f0 : form) : Alpha.form =
  let f1 = simplifyForm f0 in
  let tf1 = Typeinf.infer f1 [] in
  let _ = print_string ("\ntype inferred:\n" ^ (PrintForm.string_of_form tf1) ^ "\n"); flush_all () in
    fst (formToBapaHelper tf1)


(*----------------------------------------
  Testing
  ----------------------------------------*)
(*
let a = Var "a"
let b = Var "b"
let c = Var "c"
let seta = Var "A"
let setb = Var "B"
let setc = Var "C"

(* a + b < c *)
let f1 = App (Const Lt, [App (Const Plus, [Var "a"; Var "b"]); Var "c"])
(* a + b < c - 10 *)
let f2 = App (Const Lt, [App (Const Plus, [Var "a"; Var "b"]); 
			 App (Const Minus, [Var "c"; Const (IntConst 10)])])
(* | A U B | >= 3c *)
let f3 = App (Const GtEq, [App (Const Card, [App (Const Cup, [seta; setb])]);
			   App (Const Mult, [Const (IntConst 3); c])])
let f4 = App (Const Iff, [f1; f2])
let f5 = App (Const Iff, [f1; f2; f3])
let f6 = App (Const Disjoint, [seta; setb])
let f7 = App (Const Disjoint, [seta; setb; setc])

let print_line s = print_string (s ^ "\n\n")

let _ = print_line "\nTesting Form.form to Alpha.form translation:\n"
let _ = print_line (Alpha.string_of_form (formToBapa f1)) 
let _ = print_line (Alpha.string_of_form (formToBapa f2)) 
let _ = print_line (Alpha.string_of_form (formToBapa f3)) 
let _ = print_line (Alpha.string_of_form (formToBapa f4)) 
let _ = print_line (Alpha.string_of_form (formToBapa f5)) 
let _ = print_line (Alpha.string_of_form (formToBapa f6)) 
let _ = print_line (Alpha.string_of_form (formToBapa f7)) 
*)

