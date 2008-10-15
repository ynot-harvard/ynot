(**
   Conversion from BAPA (boolean algebras with Presburger arithmetic) sentences
   into PA (pure Presburger arithmetic) sentences.  
   Shows that BAPA is decidable and elementary.
   Viktor Kuncak, 16 July 2004.
*)

(*
 * Copyright (C) 2004 Viktor Kuncak <vkuncak@mit.edu>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the  Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307,
 * USA.
 *)

(* -------------------------------------------------- *)
(** Datatype of formulas *)

type ident = string

type binder = | Forallset | Existsset 
              | Forallint | Existsint 
              | Forallnat | Existsnat

type form = 
  | Not of form
  | And of form list
  | Or of form list
  | Impl of form * form
  | Bind of binder * ident * form
  | Less of intTerm * intTerm
  | Leq of intTerm * intTerm
  | Inteq of intTerm * intTerm
  | Seteq of setTerm * setTerm
  | Subseteq of setTerm * setTerm
and intTerm =
  | Intvar of ident
  | Const of int
  | Plus of intTerm list
  | Minus of intTerm * intTerm
  | Times of int * intTerm
  | Card of setTerm
and setTerm =
  | Setvar of ident
  | Emptyset
  | Fullset
  | Complement of setTerm
  | Union of setTerm list
  | Inter of setTerm list

let maxcard = "MAXC"

(* -------------------------------------------------- *)
(**  Algorithm \alpha *)

  (* replace Seteq and Subseteq with Card(...)=0 *)
let simplify_set_relations (f:form) : form = 
  let rec sform f = match f with
  | Not f -> Not (sform f)
  | And fs -> And (List.map sform fs)
  | Or fs -> Or (List.map sform fs)
  | Impl(f1,f2) -> Impl(sform f1,sform f2)
  | Bind(b,id,f1) -> Bind(b,id,sform f1)
  | Less(it1,it2) -> Less(siterm it1, siterm it2)
  | Leq(it1,it2) -> Leq(siterm it1, siterm it2)
  | Inteq(it1,it2) -> Inteq(siterm it1,siterm it2)
  | Seteq(st1,st2) -> And[sform (Subseteq(st1,st2)); 
                          sform (Subseteq(st2,st1))]
  | Subseteq(st1,st2) -> Inteq(Card(Inter[st1;Complement st2]),Const 0)
  and siterm it = match it with
  | Intvar _ -> it
  | Const _ -> it
  | Plus its -> Plus (List.map siterm its)
  | Minus(it1,it2) -> Minus(siterm it1, siterm it2)
  | Times(k,it1) -> Times(k,siterm it1)
  | Card st -> it
  in sform f

  (* split f into quantifier sequence and body *)
let split_quants_body f = 
  let rec vl f acc = match f with
  | Bind(b,id,f1) -> vl f1 ((b,id)::acc)
  | f -> (acc,f)
  in vl f []

  (* extract set variables from quantifier sequence *)
let extract_set_vars quants = 
  List.map (fun (b,id) -> id)
    (List.filter (fun (b,id) -> (b=Forallset || b = Existsset))
       quants)

type partition = (ident * setTerm) list

  (* make canonical name for integer variable naming a cube *)
let make_name sts = 
  let rec mk sts = match sts with
  | [] -> ""
  | (Setvar _)::sts1 -> "1" ^ mk sts1
  | (Complement (Setvar _))::sts1 -> "0" ^ mk sts1
  | _ -> failwith "make_name: unexpected partition form"
  in "l_" ^ mk sts

  (* make all cubes over vs *)
let generate_partition (vs : ident list) : partition = 
  let add id ss = (Setvar id)::ss in
  let addc id ss = Complement (Setvar id)::ss in
  let add_set id inters =
    List.map (add id) inters @ 
    List.map (addc id) inters in 
  let mk_nm is = (make_name is, Inter is) in
  List.map mk_nm 
    (List.map List.rev
       (List.fold_right add_set vs [[]]))

  (* is the set term true in the set valuation
     -- reduces to propositional reasoning *)
let istrue (st:setTerm) (id,ivaluation) : bool = 
  let valuation = match ivaluation with
  | Inter v -> v
  | _ -> failwith "wrong valuation" in
  let lookup v = 
    if List.mem (Setvar v) valuation then true
    else if List.mem (Complement (Setvar v)) valuation then false
    else failwith ("istrue: unbound variable " ^ v ^ " in valuation") in
  let rec check st = match st with
  | Setvar v -> lookup v
  | Emptyset -> false
  | Fullset -> true
  | Complement st1 -> not (check st1)
  | Union sts -> List.fold_right (fun st1 t -> check st1 || t) sts false
  | Inter sts -> List.fold_right (fun st1 t -> check st1 && t) sts true
  in check st

  (* compute cardinality of set expression 
     as a sum of cardinalities of cubes *)
let get_sum (p:partition) (st:setTerm) : intTerm list = 
  let get_list (id,inter) = match inter with
  | Inter ss -> ss
  | _ -> failwith "failed inv in get_sum"
  in
  List.map (fun (id,inter) -> Intvar id)
    (List.filter (istrue st) p)

  (* replace cardinalities of sets with sums of 
     variables denoting cube cardinalities *)
let replace_cards (p:partition) (f:form) : form = 
  let rec repl f = match f with
  | Not f -> Not (repl f)
  | And fs -> And (List.map repl fs)
  | Or fs -> Or (List.map repl fs)
  | Impl(f1,f2) -> Impl(repl f1,repl f2)
  | Bind(b,id,f1) -> Bind(b,id,repl f1)
  | Less(it1,it2) -> Less(irepl it1,irepl it2)
  | Leq(it1,it2) -> Leq(irepl it1,irepl it2)
  | Inteq(it1,it2) -> Inteq(irepl it1,irepl it2)
  | Seteq(_,_)|Subseteq(_,_) -> failwith "failed inv in replace_cards"
  and irepl it = match it with
  | Intvar _ -> it
  | Const _ -> it
  | Plus its -> Plus (List.map irepl its)
  | Minus(it1,it2) -> Minus(irepl it1, irepl it2)
  | Times(k,it1) -> Times(k, irepl it1)
  | Card st -> Plus (get_sum p st)
  in repl f

let apply_quants quants f =
  List.fold_right (fun (b,id) f -> Bind(b,id,f)) quants f

let make_defining_eqns id part = 
  let rec mk ps = match ps with
  | [] -> []
  | (id1,Inter (st1::sts1)) :: (id2,Inter (st2::sts2)) :: ps1
    when (st1=Setvar id && st2=Complement (Setvar id) && sts1=sts2) ->
      (Inter sts1,make_name sts1,id1,id2) :: mk ps1
  | _ -> failwith "make_triples: unexpected partition form" in
  let rename_last lss = match lss with
  | [(s,l,l1,l2)] -> [(s,maxcard,l1,l2)]
  | _ -> lss in
  rename_last (mk part)

  (* -------------------------- *)
  (* main loop of the algorithm *)
  (* -------------------------- *)
let rec eliminate_all quants part gr = match quants with
  | [] -> gr
  | (Existsint,id)::quants1 ->
      eliminate_all quants1 part (Bind(Existsint,id,gr))
  | (Forallint,id)::quants1 ->
      eliminate_all quants1 part (Bind(Forallint,id,gr))
  | (Existsnat,id)::quants1 ->
      eliminate_all quants1 part (Bind(Existsnat,id,gr))
  | (Forallnat,id)::quants1 ->
      eliminate_all quants1 part (Bind(Forallnat,id,gr))
  | (Existsset,id)::quants1 ->
      let eqns = make_defining_eqns id part in
      let newpart = List.map (fun (s,l',_,_) -> (l',s)) eqns in 
      let mk_conj (_,l',l1,l2) = Inteq(Intvar l',Plus[Intvar l1;Intvar l2]) in
      let conjs = List.map mk_conj eqns in
      let lquants = List.map (fun (l,_) -> (Existsnat,l)) part in
      let gr1 = apply_quants lquants (And (conjs @ [gr])) in
      eliminate_all quants1 newpart gr1
  | (Forallset,id)::quants1 ->
      let eqns = make_defining_eqns id part in
      let newpart = List.map (fun (s,l',_,_) -> (l',s)) eqns in 
      let mk_conj (_,l',l1,l2) = Inteq(Intvar l',Plus[Intvar l1;Intvar l2]) in
      let conjs = List.map mk_conj eqns in
      let lquants = List.map (fun (l,_) -> (Forallnat,l)) part in
      let gr1 = apply_quants lquants (Impl(And conjs, gr)) in
      eliminate_all quants1 newpart gr1

(* putting everything together *)

let alpha (f:form) : form =   
  (* assumes f in prenex form *)
  let (quants,fm) = split_quants_body f in
  let fm1 = simplify_set_relations fm in
  let setvars = List.rev (extract_set_vars quants) in
  let part = generate_partition setvars in
  let g1 = replace_cards part fm1 in
  eliminate_all quants part g1

(* ************************************************************
   Pretty printing and examples
 ************************************************************)

let string_of_form (f:form) : string = 
  let p s = "(" ^ s ^ ")" in
  let rec str f = match f with
  | Not f1 -> "\\lnot " ^ str f1
  | And [] -> "\\btrue"
  | And fs -> ninfix "\\land" (List.map str fs)
  | Or [] -> "\\btrue"
  | Or fs -> ninfix "\\lor" (List.map str fs)
  | Impl(f1,f2) -> infix (str f1) "\\implies" (str f2)
  | Bind(Forallset,id,f1) -> binder "\\forallset" id f1
  | Bind(Existsset,id,f1) -> binder "\\existsset" id f1
  | Bind(Forallint,id,f1) -> binder "\\forallint" id f1
  | Bind(Existsint,id,f1) -> binder "\\existsint" id f1
  | Bind(Forallnat,id,f1) -> binder "\\forallnat" id f1
  | Bind(Existsnat,id,f1) -> binder "\\existsnat" id f1
  | Less(it1,it2) -> infix (istr it1) "<" (istr it2)
  | Leq(it1,it2) -> infix (istr it1) "\\leq" (istr it2)
  | Inteq(it1,it2) -> infix (istr it1) "=" (istr it2)
  | Seteq(st1,st2) -> infix (sstr st1) "\\<seteq>" (sstr st2)
  | Subseteq(st1,st2) -> infix (sstr st1) "\\subseteq" (sstr st2)
  and istr it = match it with
  | Intvar id -> theid id
  | Const c -> theint c
  | Plus its -> ninfix "+" (List.map istr its)
  | Minus(it1,it2) -> infix (istr it1) "-" (istr it2)
  | Times(k,it) -> infix (theint k) "*" (istr it)
  | Card st -> "|" ^ sstr st ^ "|"
  and sstr st = match st with
  | Setvar id -> theid id
  | Emptyset -> "\\emptyset"
  | Fullset -> "\\Univ"
  | Complement st -> "({" ^ sstr st ^ "})^c"
  | Union sts -> ninfix "\\cup" (List.map sstr sts)
  | Inter sts -> ninfix "\\cap" (List.map sstr sts)
  and ninfix op ss = p (String.concat (" " ^ op ^ " ") ss)
  and infix s1 op s2 = p (s1 ^ " " ^ op ^ " " ^ s2)
  and binder b id f = b ^ " " ^ theid id ^ ". " ^ str f
  and theint k = Printf.sprintf "%d" k
  and theid s = 
    let sf s = if String.length s > 1 then "\\mathit{" ^ s ^ "}" else s in
    try 
      let i = String.index s '_' in
      sf (String.sub s 0 i) ^ "_{" ^
      String.sub s (i+1) (String.length s - i - 1) ^ "}"
    with Not_found -> sf s
  in str f

(*
let add_partition_def part fm = 
  let mk_conj (id,inter) = Inteq(Intvar id,Card(inter)) in
  let conjs = List.map mk_conj part in
  let body = And (conjs @ [fm]) in
  let mk_quant (id,_) f = Bind(Existsset,id,f) in
  List.fold_right mk_quant part body
*)

let process (f:form) = begin 
  print_string "Input formula is:\n\n$";
  print_string (string_of_form f);
  let res = alpha f in
  print_string "$\n\nOutput formula is:\n\n$";
  print_string (string_of_form res);
  print_string "$\n";
  res
end

let e=Setvar "e" and content=Setvar "content" and 
    content'=Setvar "content'" 
and size=Intvar "size" and size'=Intvar "size'"

let a = Setvar "A" and b = Setvar "B"

let example1 =
  Bind(Forallset,"e",
  Bind(Forallset,"content", Bind(Forallset,"content'",
  Bind(Forallint,"size", Bind(Forallint,"size'",
    Impl(And [Inteq(Card(e),Const 1);
              Inteq(Card(Inter[e;content]),Const 0);
              Inteq(Card(content),size);
              Seteq(content',Union[content;e]);
              Inteq(size',Plus[size;Const 1])],
         And[Less(Const 0,size'); Inteq(Card(content'),size')])
  )))))

let example2 =
  Bind(Existsset,"e",
  Bind(Existsset,"content", Bind(Existsset,"content'",
  Bind(Existsint,"size", Bind(Existsint,"size'",
    And [Inteq(Card(e),Const 1);
         Inteq(Card(Inter[e;content]),Const 0);
         Inteq(Card(content),size);
         Seteq(content',Union[content;e]);
         Inteq(size',Plus[size;Const 1]);
         Not (And[Less(Const 0,size'); Inteq(Card(content'),size')])]
  )))))

let example3 =
  Bind(Forallset,"A",
       Bind(Forallset, "B",
	    Impl(Subseteq(a,b),Seteq(a,b))))

let example4 =
  Bind(Forallset,"A",
       Bind(Forallset, "B",
	    Impl(And([Subseteq(b,a); Subseteq(a,b)]),Seteq(a,b))))

let example5 =
  Bind(Forallnat, "x",
  Bind(Forallset,"A",
       Bind(Forallset, "B",
            And [Less (Intvar "x", Const 10);
	         Impl(And([Subseteq(b,a); Subseteq(a,b)]),Seteq(a,b))])))

let example6 =
  Bind(Existsnat, "x",
  Bind(Forallset,"A",
       Bind(Forallset, "B",
            And [Less (Intvar "x", Const 10);
	         Impl(And([Subseteq(b,a); Subseteq(a,b)]),Seteq(a,b))])))

let example7 =
  Bind(Forallnat, "x",
  Bind(Forallset,"A",
       Bind(Forallset, "B",
	         Impl(And[Less (Intvar "x", Const 10);
                          Subseteq(b,a); Subseteq(a,b)],
                      And[Seteq(a,b); Less(Intvar "x", Const 9)]))))

let example8 =
  Bind(Forallset,"A",
       Bind(Forallset, "B",
            And[Leq(Card a, Card (Union [a;b]));
                Leq(Card (Union [a;b]), Plus[Card a; Card b])]))

(*
let pa_example = process example3
*)

