open Options
open Vocab

let main () = 
    let src = ref "" in
    let usage = Printf.sprintf "Usage: %s <options> <file>" Sys.argv.(0) in
    let _ = Arg.parse options
                (fun x ->
                     if Sys.file_exists x then src := x
                     else raise (Arg.Bad (x ^ ": No files given"))
								)
                usage
    in
		if !src = "" then Arg.usage options usage
    else
			let (macro_instantiator, target_function_name, grammar, forall_var_map, spec) = 
				Parse.parse !src 
			in
			(* prerr_endline (Specification.string_of_io_spec spec);  *)
			(* let sol = Afta.synthesis (macro_instantiator, target_function_name, grammar, forall_var_map, spec) in *)
			(* let sol = Generator.enum_bu_search grammar spec in *)
			
			(* PBE spec - input-output examples : ((const list) * const) list  *)
			let spec_total = spec in
			let start = Sys.time () in  
			(* CEGIS loop *)
			let rec cegis spec =
				my_prerr_endline (Specification.string_of_io_spec spec);
				my_prerr_endline (Printf.sprintf "CEGIS iter: %d" (List.length spec));
  			let sol =
  				Bidirectional.synthesis
						(macro_instantiator, target_function_name, grammar, forall_var_map, spec)
  			in
				my_prerr_endline (Printf.sprintf "** Proposed candidate: %s **" (Exprs.string_of_expr sol));
				(* spec' = spec + mismatched input-output examples *)
				let spec' = 
  				List.fold_left (fun acc (inputs, desired) ->
  					try
  						let signature = Exprs.compute_signature [(inputs, desired)] sol in
  						if (Pervasives.compare signature [desired]) <> 0 then
  							acc @ [(inputs, desired)]
  						else acc
  					with Exprs.UndefinedSemantics -> acc @ [(inputs, desired)]
  				) spec spec_total
				in
				(* no mismatched input-output examples *)
				if (List.length spec) = (List.length spec') then 
					match (Specification.verify sol spec) with 
					| None -> sol 
					| Some cex ->
						my_prerr_endline (Specification.string_of_io_spec [cex]); 
						let _ = assert (not (List.mem cex spec')) in  
						cegis (cex :: spec')
				else cegis spec'
			in
			let _ = assert ((List.length spec) > 0) in 
			let sol =
				if !Options.ex_all then cegis spec_total 
				else cegis [List.nth spec 0] 
			in
			my_prerr_endline ("****** solution *******");
			(* prerr_endline (Exprs.string_of_expr sol); *)
			prerr_endline (Exprs.sexpstr_of_fun target_function_name sol);
			prerr_endline ("size : " ^ (string_of_int (Exprs.size_of_expr sol)));
			prerr_endline ("time : " ^ (Printf.sprintf "%.2f sec" (Sys.time() -. start)));
			(* prerr_endline ("check dist time : " ^ (Printf.sprintf "%.2f sec" (!Witness.check_dist_time))); *)
			()
		 
let _ = main ()
