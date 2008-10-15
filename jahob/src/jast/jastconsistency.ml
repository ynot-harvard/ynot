(** Some consistency checks on jast tree, most notably readonly variables.
 @author aragos 
*)

open Jast

let readonly 
	( prog : program )
	(* ( cld : class_decl list ) *)
=
	let get_class (cln : class_name) : class_decl =
  		let rec search (cls : class_decl list) : class_decl option =
    	match cls with
    		| [] -> None
    		| cl::cls0 -> 
        		if cl.cl_name=cln then Some cl
        		else search cls0
  		in 
  		match search prog.Jast.classes with
  			| None -> failwith( "Failed finding class " ^ cln ^ " during readonly check." );
  			| Some x -> x
  	in
  	
  	let get_field_for_current_class
  		( ccl : class_decl )
  		( fld : field )
  		: field
  	=
  		match JastUtil.get_field prog ccl fld.f_var.vd_name with
  			| Some x -> 
  			(
  				if( x.f_cl = fld.f_cl ) then 
  					{ Jast.f_var = x.f_var; Jast.f_cl = ccl.cl_name }
  				else
  					fld
  			)
  			| None -> fld
  	in
  	
  	(* check value assignments for readonly variable access out of allowed range *)
	let rec check
		( vd : var_decl )		
		( vd_cl : class_decl )
		( cl : class_decl )
		( mt : method_decl )
	=
		(* if( vd.vd_name = "movement" ) then
			print_string ("checking assignment to " ^ vd_cl.cl_name ^ "." ^ vd.vd_name ^ " in " ^ cl.cl_name ^ "." ^ mt.m_name ^ "\n"); *)
			
		if ( vd.vd_readonly & not ( vd_cl = cl ) ) then
			Util.warn ("Readonly restriction violated in " ^ cl.cl_name ^ "." ^ mt.m_name ^ " ( " ^ vd_cl.cl_name ^ "." ^ vd.vd_name ^ " is readonly ).");

	in
	let rec walk_stmts
		( stmts : stmt list )
		( cl : class_decl )
		( mt : method_decl )
	=
		(* print_string ( "Number of statements in " ^ cl.cl_name ^ "." ^ mt.m_name ^ ": " ^ ( string_of_int ( List.length stmts ) ) ^ "\n" ); *)
		match stmts with
			| st::tail ->
			(
				match st with
					| ( Basic ( bs, cn ) ) ->
					(
						(* print_string "Found basic statement\n"; *)
						match bs with
							| ( VarAssign ( lv, e ) ) ->
							(
								(* print_string ( "Found VarAssign in " ^ cl.cl_name ^ "." ^ mt.m_name ^ "\n"); *)
								match lv with
									| ( LocalVar vd ) ->
										(* print_string ( "Found assignment to localvar " ^ vd.vd_name ^ " in " ^ cl.cl_name ^ "." ^ mt.m_name ^ "\n"); *)
										 check vd cl cl mt;
										 walk_stmts tail cl mt;
									| ( StaticVar cv ) ->
										(* print_string ( "Found assignment to staticvar " ^ cv.cv_var.vd_name ^ " in " ^ cl.cl_name ^ "." ^ mt.m_name ^ "\n"); *)
										check cv.cv_var (get_class cv.cv_cl) cl mt;
										walk_stmts tail cl mt;
							)
							| ( FieldAssign ( _, fld, _ ) ) ->
							(
								let f = get_field_for_current_class cl fld in
								(* print_string ( "Found assignment to field " ^ fld.f_var.vd_name ^ " in " ^ cl.cl_name ^ "." ^ mt.m_name ^ "\n"); *)
								(* print_string ( "Found assignment to field " ^ f.f_cl ^ "." ^ f.f_var.vd_name ^ " in " ^ cl.cl_name ^ "." ^ mt.m_name ^ "\n"); *)
								check f.f_var (get_class f.f_cl) cl mt;								
								walk_stmts tail cl mt;
							)	
							| _ ->
								(* print_string ( "Found undefined statement in " ^ cl.cl_name ^ "." ^ mt.m_name ^ "\n"); *)
								walk_stmts tail cl mt;
					)
					| ( Block lst ) ->
						walk_stmts lst cl mt;
						walk_stmts tail cl mt;
					| ( If ( _, a, b ) ) ->
						walk_stmts [a;b] cl mt;
						walk_stmts tail cl mt;
				 	| ( Loop ( _, a, _, b ) ) ->
				 		walk_stmts [a;b] cl mt;
				 		walk_stmts tail cl mt;
					| _ -> walk_stmts tail cl mt;					
				)
			| [] ->	()
	in
	let rec walk_methods
		( methods : method_decl list )
		( cl : class_decl )
	=
		(* print_string ( "Number of methods: " ^ ( string_of_int ( List.length methods ) ) ^ "\n" ); *)		
		match methods with
			| mt::tail ->
				(* print_string ( "Checking method " ^ cl.cl_name ^ "." ^ mt.m_name ^ "\n" ); *)
				walk_stmts [mt.m_body] cl mt;				
				walk_methods tail cl;
			| [] -> ()
	in			
	
	let rec walk_classes
		( classes : class_decl list )
	=
		(* print_string ( "Number of classes: " ^ ( string_of_int ( List.length cld ) ) ^ "\n" ); *)
		match classes with
			| cd::tail ->
				walk_methods cd.cl_methods cd;
				walk_classes tail;
			| [] -> ()
	in
	walk_classes prog.Jast.classes