(** Basic interface to the Simplify theorem prover. *)

open Form

let rec genPairs (xs0 : 'a list) : ('a * 'a) list = match xs0 with
  | [] -> []
  | [x] -> []
  | (x :: xs) ->
      let tailpairs = genPairs xs in
      let hdpairs = List.map (fun y -> (x, y)) xs in
	List.append hdpairs tailpairs


let warn (msg : string) = print_string msg
let panic (msg : string) = failwith msg

let printIdents (names : ident list) = String.concat " " names

let rec printToSimplify (f0 : form) : string = match f0 with
  | Binder (binder, tvids, f1) ->
      let ids = List.map (fun tvid -> fst tvid) tvids in
      let idsstr = Util.replace_dot_with_uscore (printIdents ids) in
      let f1str = printToSimplify f1 in
      let binderstr = printBinder binder in
	"(" ^ binderstr ^ " (" ^ idsstr ^ ") " ^ f1str ^ ")"

  | App (f1, fs) -> printApp f1 fs

  | Const (BoolConst b) -> 
      if b then
	"TRUE"
      else
	"FALSE"
  | Var iden -> Util.replace_dot_with_uscore iden
  | TypedForm (f, _) -> printToSimplify f
  | _ -> panic ("simplify:printToSimplify: unsupported form of formula: " ^ PrintForm.string_of_form f0)


and printBinder b = match b with
  | Forall -> "FORALL"
  | Exists -> "EXISTS"
  | _ -> panic "simplify:printBinder: unsupported binder"

and printApp c1 fs = match c1 with
  | Const And ->
      let fsstr = String.concat " " (List.map printToSimplify fs) in
	"(AND " ^ fsstr ^ ")"

  | Const Or -> 
      let fsstr = String.concat " " (List.map printToSimplify fs) in
	"(OR " ^ fsstr ^ ")"

  | Const Not ->
      if List.length fs != 1 then
	panic ("simplify:printApp: Not need 1 parameter, received " ^ (string_of_int (List.length fs)))
      else
	"(NOT " ^ (printToSimplify (List.hd fs)) ^ ")"
      
  | Const Impl -> 
      if List.length fs != 2 then
	panic ("simplify:printApp: Impl need 2 parameters, received " ^ (string_of_int (List.length fs)))
      else
	let antestr = printToSimplify (List.hd fs) in (* assuming first element implies the second one *)
	let conseqstr = printToSimplify (List.hd (List.tl fs)) in
	  "(IMPLIES " ^ antestr ^ " " ^ conseqstr ^ ")"

  | Const Iff -> (* assuming Iff is applied to a set of formulae *)
      if List.length fs <= 1 then
	panic ("simplify:printApp: Iff need at least 2 parameters, received " ^ (string_of_int (List.length fs)))
      else
	let pairs = genPairs fs in
	let iffsstr = List.map (fun (f1, f2) -> "(IFF " ^ (printToSimplify f1) 
				  ^ " " ^ (printToSimplify f2) ^ ")") pairs in
	  if List.length iffsstr > 1 then
            "(AND " ^ (String.concat "\n" iffsstr) ^ ")"
	  else
	    List.hd iffsstr

  | Const Disjoint -> (* assuming Disjoint is applied to a set of set terms *)
      let sets = List.map printTerm fs in
      let pairs = genPairs sets in
      let djnts =List.map (fun (s1, s2) -> 
			     "(EQ (INTER " ^ s1 ^ " " ^ s2 ^ ") EMPTYSET)" ) pairs in
	begin
	  if List.length fs <= 1 then
	    warn "formbapa:transApp: Disjoint is applied to 0 or 1 parameter\n";

	  if List.length djnts > 1 then
	     "(AND " ^ (String.concat " " djnts) ^ ")"
	  else
	    List.hd djnts
	end;

  | Const Seteq ->
      if List.length fs != 2 then
	panic ("formbapa:transApp: Subseteq needs two parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let s1 = printTerm (List.hd fs) in
	let s2 = printTerm (List.hd (List.tl fs)) in
	  "(EQ " ^ s1 ^ " " ^ s2 ^")"

  | Const Subseteq ->
      if List.length fs != 2 then
	panic ("formbapa:printApp: Subseteq needs two parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let s1 = printTerm (List.hd fs) in
	let s2 = printTerm (List.hd (List.tl fs)) in
	  "(SUBSETEQ " ^ s1 ^ " " ^ s2 ^")"

  | Const Subset ->
      if List.length fs != 2 then
	panic ("formbapa:printApp: Subset needs two parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let s1 = printTerm (List.hd fs) in
	let s2 = printTerm (List.hd (List.tl fs)) in
	  "(SUBSET " ^ s1 ^ " " ^ s2 ^")"

  | Const Elem ->
      if List.length fs != 2 then
	panic ("formbapa:printApp: Elem needs two parameters, received " 
	       ^ (string_of_int (List.length fs)))
      else
	let s1 = printTerm (List.hd fs) in
	let s2 = printTerm (List.hd (List.tl fs)) in
	  "(MEMBER " ^ s1 ^ " " ^ s2 ^")"

  | Const Cardeq ->
      let sets = List.map printTerm fs in
      let pairs = genPairs sets in
      let eqns =List.map (fun (s1, s2) -> 
			    "(EQ " ^ s1 ^ " " ^ s2 ^ ")" ) pairs in
	begin
	  if List.length fs <= 1 then
	    warn "formbapa:transApp: Disjoint is applied to 0 or 1 parameter\n";

	  if List.length eqns > 1 then
	     "(AND " ^ (String.concat " " eqns) ^ ")"
	  else
	    List.hd eqns
	end;

  | Const Cardleq ->
      if List.length fs != 2 then
	panic ("simplify:printApp: Cardleq need 2 parameters, received " ^ (string_of_int (List.length fs)))
      else
	let s1 = printTerm (List.hd fs) in
	let s2 = printTerm (List.hd (List.tl fs)) in
	  "(<= (CARD " ^ s1 ^ ") (CARD " ^ s2 ^ "))"

  | Const Cardgeq ->
      if List.length fs != 2 then
	panic ("simplify:printApp: Cardleq need 2 parameters, received " ^ (string_of_int (List.length fs)))
      else
	let s1 = printTerm (List.hd fs) in
	let s2 = printTerm (List.hd (List.tl fs)) in
	  "(>= (CARD " ^ s1 ^ ") (CARD " ^ s2 ^ "))"

  | Const Lt -> (* The list of parameters are expected to be integer expressions *)
      if List.length fs != 2 then
	panic ("simplify:printApp: Lt need 2 parameters, received " ^ (string_of_int (List.length fs)))
      else
	let iterm1str = printTerm (List.hd fs) in
	let iterm2str = printTerm (List.hd (List.tl fs)) in
	  "(< " ^ iterm1str ^ " " ^ iterm2str ^ ")"

  | Const Gt ->
      if List.length fs != 2 then
	panic ("simplify:printApp: Gt need 2 parameters, received " ^ (string_of_int (List.length fs)))
      else
	let iterm1str = printTerm (List.hd fs) in
	let iterm2str = printTerm (List.hd (List.tl fs)) in
	  "(> " ^ iterm1str ^ " " ^ iterm2str ^ ")"

  | Const LtEq -> (* The list of parameters are expected to be integer expressions *)
      if List.length fs != 2 then
	panic ("simplify:printApp: GtEq need at least 2 parameters, received " ^ (string_of_int (List.length fs)))
      else
	let iterm1str = printTerm (List.hd fs) in
	let iterm2str = printTerm (List.hd (List.tl fs)) in
	  "(<= " ^ iterm1str ^ " " ^ iterm2str ^ ")"

  | Const GtEq ->
      if List.length fs != 2 then
	panic ("simplify:printApp: GtEq need at least 2 parameters, received " ^ (string_of_int (List.length fs)))
      else
	let iterm1str = printTerm (List.hd fs) in
	let iterm2str = printTerm (List.hd (List.tl fs)) in
	  "(>= " ^ iterm1str ^ " " ^ iterm2str ^ ")"

  | Const Eq ->
      if List.length fs != 2 then
	panic ("simplify:printApp: Eq need at least 2 parameters, received " ^ (string_of_int (List.length fs)))
      else
	let iterm1str = printTerm (List.hd fs) in
	let iterm2str = printTerm (List.hd (List.tl fs)) in
	  "(EQ " ^ iterm1str ^ " " ^ iterm2str ^ ")"

  (* reading boolean fields *)
  | Const FieldRead ->
      if List.length fs != 2 then
	panic ("simplify:printApp: FieldRead needs 2 parameters, received " ^ (string_of_int (List.length fs)))
      else
	let term1str = printTerm (List.hd fs) in
	let term2str = printTerm (List.hd (List.tl fs)) in
	  "(fieldRead S " ^ term1str ^ " " ^ term2str ^ ")"
  | Const FieldWrite ->
      if List.length fs != 3 then
	panic ("simplify:printApp: FieldWrite needs 3 parameters, received " ^ (string_of_int (List.length fs)))
      else
	let term1str = printTerm (List.hd fs) in
	let term2str = printTerm (List.hd (List.tl fs)) in
	let term3str = printTerm (List.hd (List.tl (List.tl fs))) in
	  "(fieldWrite S " ^ term1str ^ " " ^ term2str ^ " " ^ term3str ^ ")"

  | Const Comment ->
      if List.length fs != 2 then
	panic ("simplify:printApp: Comment needs 2 argument, received " ^ (string_of_int (List.length fs)))
      else
	printToSimplify (List.hd (List.tl fs))
	  

  | _ -> panic ("simplify:printApp: can't translate formula: " ^ PrintForm.string_of_form (App (c1, fs)))


and printTerm term0 = match term0 with

  | Var iden -> Util.replace_dot_with_uscore iden

  | Const (IntConst i) -> string_of_int i

  | Const EmptysetConst -> "EMPTYSET"

  | Const NullConst -> "nullObject"

  | App (op, terms) -> 
      begin
	match op with
	  | Const Plus ->
	      let termsstr = String.concat " " (List.map printTerm terms) in
		"(+ " ^ termsstr ^ ")"
	  | Const Minus ->
	      let termsstr = String.concat " " (List.map printTerm terms) in
		"(- " ^ termsstr ^ ")"
	  | Const Mult ->
	      let termsstr = String.concat " " (List.map printTerm terms) in
		"(* " ^ termsstr ^ ")"
	  | Const (IntConst i) -> string_of_int i
	  | Const Card ->
	      if List.length terms != 1 then
		panic ("simplify:printTerm: Card needs 1 parameter, received "
		       ^ (string_of_int (List.length terms)))
	      else
		let s = printTerm (List.hd terms) in
		  "(CARD " ^ s ^ ")"
	  | Const Cap ->
	      if List.length terms != 2 then
		panic ("simplify:printTerm: Cap needs 2 parameters, received " ^ (string_of_int (List.length terms)))
	      else
		let term1str = printTerm (List.hd terms) in
		let term2str = printTerm (List.hd (List.tl terms)) in
		  "(INTER " ^ term1str ^ " " ^ term2str ^ ")"
	  | Const Cup ->
	      if List.length terms != 2 then
		panic ("simplify:printTerm: Cup needs 2 parameters, received " ^ (string_of_int (List.length terms)))
	      else
		let term1str = printTerm (List.hd terms) in
		let term2str = printTerm (List.hd (List.tl terms)) in
		  "(UNION " ^ term1str ^ " " ^ term2str ^ ")"
	  | Const Diff ->
	      if List.length terms != 2 then
		panic ("simplify:printTerm: Diff needs 2 parameters, received " ^ (string_of_int (List.length terms)))
	      else
		let term1str = printTerm (List.hd terms) in
		let term2str = printTerm (List.hd (List.tl terms)) in
		  "(DIFF " ^ term1str ^ " " ^ term2str ^ ")"
	  | Const FieldRead ->
	      if List.length terms == 1 then
		printTerm (List.hd terms)
	      else if List.length terms == 2 then
		let term1str = printTerm (List.hd terms) in
		let term2str = printTerm (List.hd (List.tl terms)) in
		  "(fieldRead S " ^ term1str ^ " " ^ term2str ^ ")"
	      else
		panic ("simplify:printTerm: FieldRead needs 2 parameters, received " ^ (string_of_int (List.length terms)) ^ " as " ^ PrintForm.string_of_form (List.hd terms))

	  | Const FieldWrite ->
	      if List.length terms != 3 then
		panic ("simplify:printTerm: FieldWrite needs 3 parameters, received " ^ (string_of_int (List.length terms)))
	      else
		let term1str = printTerm (List.hd terms) in
		let term2str = printTerm (List.hd (List.tl terms)) in
		let term3str = printTerm (List.hd (List.tl (List.tl terms))) in
		  "(fieldWrite S " ^ term1str ^ " " ^ term2str ^ " " ^ term3str ^ ")"
	  | Const Comment ->
	      if List.length terms != 2 then
		panic ("simplify:printTerm: Comment needs 2 argument, received " ^ (string_of_int (List.length terms)))
	      else
		printToSimplify (List.hd (List.tl terms))
	  | _ -> panic ("simplify:printTerm: can't translate App formula: " ^ PrintForm.string_of_form term0)
      end;
(*  | Binder (Coprehension, [(tvar, _)], defpred) -> *)
      
  | TypedForm (f, _) -> printTerm f
  | _ -> panic ("simplify:printTerm: can't translate formula: " ^ PrintForm.string_of_form term0)
   


let rec betaReduction f0 = match f0 with
  | Const c -> Const c
  | Var v -> Var v
  | TypedForm (f, t) -> let ff = betaReduction f in TypedForm (ff, t)
(*  | Binder (Lambda, tvids, f) -> Binder (Lambda, tvids, f) *)
  | Binder (bk, tvids, f) -> Binder (bk, tvids, betaReduction f)
  | App (c, fs) -> 
      begin
	let rfs = List.map betaReduction fs in
	  match rfs with
	    | [f1; f2] ->
		if isLambda f1 then
		  App (c, [betaRedex f1 f2; f2])
		else
		  App (c, rfs)
	    | _ -> App (c, rfs)
      end;
      
and betaRedex f0 a0 = match f0 with
  | Binder (Lambda, [(v, _)], f) -> 
      let rf = FormUtil.subst [(v, a0)] f in
	print_string ("\nf0: " ^ PrintForm.string_of_form f0 ^ 
			"\na0: " ^ PrintForm.string_of_form a0 ^
			"\nrf: " ^ PrintForm.string_of_form rf ^ "\n\n");
	
	rf
  | TypedForm (f, t) -> TypedForm (betaRedex f a0, t)
  | _ -> panic "betaRedex: first argument is not a function"

and isLambda f = match f with
  | Binder (Lambda, _, _) -> true
  | TypedForm (f, t) -> isLambda f
  | _ -> false

(*----------------------------------------
  Testing
  ----------------------------------------*)

(*
let a = Var "a"
let b = Var "b"
let c = Var "c"

(* a + b < c *)
let f1 = App (Const Lt, [App (Const Plus, [Var "a"; Var "b"]); Var "c"])
(* a + b >= c - 10 *)
let f2 = App (Const GtEq, [App (Const Plus, [Var "a"; Var "b"]); 
			 App (Const Minus, [Var "c"; Const (IntConst 10)])])
let f3 = App (Const Iff, [f1; f2])
let f4 = App (Const Iff, [f3; f2; f1])

let print_line s = print_string ((printToSimplify s) ^ "\n\n")
let _ = print_line f1
let _ = print_line f2
let _ = print_line f3
let _ = print_line f4
*)
