(* Quentin Carbonneaux - 2016 *)

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
  ]

let annonarg s =
  if !input_file <> "" then
    raise (Arg.Bad "too many input files");
  input_file := s
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
        if ends_with ".imp" !input_file then
          let imp_file = IMP.parse_file !input_file in
          List.map Graph.from_imp imp_file
        else if ends_with ".o" !input_file
             || ends_with ".bc" !input_file then
          let ic = exec_llvm_reader !input_file in
          try
            let gfunc = Graph_Reader.read_func ic in
            let gfunc = Graph.add_loop_counter "z" gfunc in
            [gfunc]
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
    let fstart =
      match !main_func with
      | Some f -> f
      | None ->
        if List.length g_file = 1
        then (List.hd g_file).Types.fun_name
        else "start"
    in
    if not (List.exists (fun f -> f.Types.fun_name = fstart) g_file) then
      failarg (Printf.sprintf "cannot find function '%s' to analyze" fstart);
    let g_file =
      if !no_weaken then g_file else
      List.map Heuristics.add_weaken g_file
    in
    let module AI = (val begin
        match !ai with
        | "apron" -> (module Graph.AbsInt.Apron)
        | _       -> (module Graph.AbsInt.Simple)
      end: Graph.AbsInt)
    in
    let ai_results = AI.analyze ~dump:!dump_ai g_file fstart in
    let query =
      let open Polynom in
        (Poly.of_monom (Monom.of_var "z") (+1.))
    in
    let g_file =
      if !no_focus then g_file else
      List.map (Heuristics.add_focus ~deg:1 ai_results AI.get_nonneg) g_file
    in
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
