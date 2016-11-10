(* Quentin Carbonneaux - 2016 *)

(* Van Chan Ngo, 2016 *)
(* the work flow:
 * parse the input file
 * construct CFG
 * apply weaken rules heuristically [option]
 * do abstract interpretation using simple or apron
 * add focus functions if needed
 * do analysis
 *)

let debug_flag = ref false
let input_file = ref ""
let main_func = ref None
let dump_ai = ref false
let dump_stats = ref false
let no_weaken = ref false
let no_focus = ref false
let ascii = ref false
let ai = ref "simple"

let usagemsg = Printf.sprintf "usage: %s [OPTIONS] FILE\n" Sys.argv.(0)
let argspec = Arg.align

  [ "-func", Arg.String (fun s -> main_func := Some s),
    "<fn> Analyze the specified function"
  ; "-ai", Arg.Symbol (["apron"; "simple"], fun s -> ai := s),
    " Select the abstract interpretation backend"

  ; "-ascii", Arg.Set ascii,
    " Output results using ascii only"

  ; "-dump-ai", Arg.Set dump_ai,
    " Display abstract interpretation results"
  ; "-dump-stats", Arg.Set dump_stats,
    " Display statistics of the analysis"

  ; "-no-weaken", Arg.Set no_weaken,
    " Do not automatically add weakening points"
  ; "-no-focus", Arg.Set no_focus,
    " Do not automatically add focus functions"
  ; "-debug", Arg.Set debug_flag,
    " Display debug information"
  ]

let annonarg s =
  if !input_file <> "" then
    raise (Arg.Bad "too many input files");
  input_file := s

(* print the error and exit *)
let failarg msg =
  Printf.eprintf "%s: %s\n" Sys.argv.(0) msg;
  Arg.usage argspec usagemsg;
  exit 1

let exec_llvm_reader f =
  let reader = "/llvm-reader" in
  let candidates =
    [ Config.build_path ^ "/../llvm-reader" ^ reader
    ] in
  match
    List.fold_left (fun ico cand ->
      if ico = None then
        try
          let _ = Unix.access cand [Unix.X_OK] in
          let cmd = Printf.sprintf "%s %s" cand f in
          Some (Unix.open_process_in cmd)
        with Sys_error _ | Unix.Unix_error _ -> None
      else ico
    ) None candidates
  with
  | Some ic -> ic
  | None ->
    Format.eprintf "%s: llvm-reader could not be found or run@."
      Sys.argv.(0);
    raise Utils.Error

(* entry point *)
let main () =
  Arg.parse argspec annonarg usagemsg;
  if !input_file = "" then failarg "no input file provided";
  try
    let ends_with s s' =
      let ls' = String.length s' and ls = String.length s in
      ls' >= ls && String.sub s' (ls' - ls) ls = s
    in
    let g_file =
      try
      	(* CFG: if input file is in IMP *)
        if ends_with ".imp" !input_file then
          let (lv, imp_file) = IMP.parse_file !input_file in
          (lv, List.map Graph.from_imp imp_file)
        (* CFG: if input file is LLVM bitcode *)
        else if ends_with ".o" !input_file
             || ends_with ".bc" !input_file then
          let ic = exec_llvm_reader !input_file in
          try
            let gfunc = Graph_Reader.read_func ic in
            let gfunc = Graph.add_loop_counter "z" gfunc in
            ([], [gfunc])
          with End_of_file ->
            match Unix.close_process_in ic with
            | Unix.WEXITED 0 -> failwith "llvm-reader should have failed"
            | Unix.WEXITED _ ->
              Format.eprintf "%s: llvm-reader could not parse '%s'@."
                Sys.argv.(0) !input_file;
              raise Utils.Error
            | _ ->
              Format.eprintf "%s: llvm-reader process was killed@."
                Sys.argv.(0);
              raise Utils.Error
        else begin
          Format.eprintf "%s: unknown input file type for '%s'@."
            Sys.argv.(0) !input_file;
          raise Utils.Error
        end
      with Sys_error _ ->
        Format.eprintf "%s: cannot open file '%s'@."
          Sys.argv.(0) !input_file;
        raise Utils.Error
    in
    (* get the start function *)
    let fstart =
      match !main_func with
      | Some f -> f
      | None ->
        let (lv, lf) = g_file in
        if List.length lf = 1
        then (List.hd lf).Types.fun_name
        else "start"
    in
    let (lv, lf) = g_file in
    if not (List.exists (fun f -> f.Types.fun_name = fstart) lf) then
      failarg (Printf.sprintf "cannot find function '%s' to analyze" fstart);
    (* do weakening if needed *)
    let g_file =
      let (lv, lf) = g_file in
      if !no_weaken then g_file else
      (lv, (List.map Heuristics.add_weaken lf))
    in
    (* instantiate an abstract interpreter *)
    let module AI =
      (val begin
        match !ai with
        | "apron" -> (module Graph.AbsInt.Apron)
        | _   -> (module Graph.AbsInt.Simple)
      end: Graph.AbsInt)
    in
    (* do abstract interpretation *)
    let ai_results = let (lv, lf) = g_file in AI.analyze ~dump:!dump_ai lf fstart in
    let query =
      let open Polynom in
        (Poly.of_monom (Monom.of_var "z") (+1.))
    in
    (* add focus functions if needed *)
    let g_file =
      let (lv, lf) = g_file in
      if !no_focus then g_file else
      (lv, List.map (Heuristics.add_focus ~deg:1 ai_results AI.get_nonneg) lf)
    in
    (* apply the analysis *)
    let st_results = Analysis.run ai_results AI.is_nonneg g_file fstart query in
    let poly_print =
      if !ascii then Polynom.Poly.print_ascii else Polynom.Poly.print
    in
    let retcode =
      match st_results with
      | None ->
        Format.printf "Sorry, I could not find a bound.@.";
        1
      | Some p ->
        Format.printf "Upper bound for %a: %a@." poly_print query poly_print p;
        0
    in
    if !dump_stats then begin
      let open Format in
      let { Analysis.num_lpvars; num_lpcons;
            max_focus; lp_runtime }
        = Analysis.stats in
      let { Graph.weaken_map } = Graph.stats in
      printf "@.Statistics:@.    @[<v>";
      if not !no_weaken then begin
        printf "Weakenings inserted per function:@     @[<hov>";
        let first = ref true in
        List.iter (fun (f, n) ->
          printf (if !first then "%d for %s" else ",@ %d for %s") n f;
          first := false) (List.rev weaken_map);
        printf "@]@ ";
      end;
      printf "Number of LP variables: %d@ " num_lpvars;
      printf "Number of LP constraints: %d@ " num_lpcons;
      printf "Maximum focus functions in use: %d@ " max_focus;
      printf "LP solver runtime: %.3fs" !lp_runtime;
      printf "@]@.";
    end;
    retcode
  with Utils.Error -> 2

let () = Utils.exit (main ())
