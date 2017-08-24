(* Quentin Carbonneaux - 2016-2017 *)
(* Van Chan Ngo - 2017 *)

open Graph
open Types
open Polynom
open Focus

type stats =
  { mutable num_lpvars: int
  ; mutable num_lpcons: int
  ; mutable max_focus: int
  ; lp_runtime: float ref
  }

let stats =
  { num_lpvars = 0
  ; num_lpcons = 0
  ; max_focus = 0
  ; lp_runtime = ref 0.
  }

let reset_stats () =
  begin
    stats.num_lpvars <- 0;
    stats.num_lpcons <- 0;
    stats.max_focus <- 0;
    stats.lp_runtime := 0.;
  end

type order =
  | Ge
  | Le
  | Eq

let swap_order = function
  | Ge -> Le
  | Le -> Ge
  | Eq -> Eq

let classify_monom globals m =
  let has_glo = ref false in
  let has_loc = ref false in
  let _ =
    Monom.var_exists (fun v ->
      if IdSet.mem v globals then
        has_glo := true
      else
        has_loc := true;
      false (* keep iterating *)
    ) m
  in
  match !has_glo, !has_loc with
  | true, false -> `Global
  | false, true -> `Local
  | true, true -> `Mixed
  | false, false -> `Constant

module Potential
: sig
  type annot
  type focus_annot
  type solution
  val new_annot: Monom.t list -> annot
  val dump: Format.formatter -> annot -> unit
  val of_poly: Poly.t -> annot
  val monoms: annot -> Monom.t list
  val exec_assignment: (id * expr) -> annot -> annot
  val constrain: annot -> order -> annot -> unit
  val weaken: Poly.t list -> annot -> (annot * focus_annot list)
  val split: IdSet.t -> annot -> ((* local *) annot * (* global *) annot)
  val merge: (annot * annot) -> annot
  val addmul: annot -> int -> annot -> annot
  val solve_min: Poly.t list -> annot -> solution option
  val annot_sol: solution -> annot -> Poly.t
  val focus_annot_sol: solution -> focus_annot -> (float * float)
end
= struct

  (* This is the core of the analysis.
     We define what potential annotations are,
     and how they are:

       1. changed by assignments,
       2. constrained between each other (=, or >=).

  *)

  (* LP variables are simple integers. *)
  type lpvar = int

  (* To generate few LP constraints, our potential
     does not map monomials to LP variables directly
     but to linear combinations of those.
     A linear combination is represented as a hash
     table mapping LP variables to their coefficient
     in the linear sum.
  *)
  module M = Map.Make(Monom)
  type linexpr = (lpvar, float) Hashtbl.t
  type annot = linexpr M.t
  type focus_annot = lpvar * lpvar
  type solution = float array

  let new_lpvar () =
    stats.num_lpvars <- stats.num_lpvars + 1;
    Clp.add_column
      { Clp.column_obj = 0.
      ; Clp.column_lower = neg_infinity
      ; Clp.column_upper = infinity
      ; Clp.column_elements = [| |]
      };
    Clp.number_columns () - 1

  let new_linexpr () =
    Hashtbl.create 5

  let new_annot monoms =
    List.fold_left begin fun annot m ->
      if M.mem m annot then annot else
      let le = new_linexpr () in
      let v = new_lpvar () in
      Hashtbl.add le v 1.;
      M.add m le annot
    end M.empty monoms

  let dump fmt a =
    let dump_le fmt le =
      Format.fprintf fmt "@[<h>";
      let first = ref true in
      Hashtbl.iter begin fun lpv k ->
        Format.fprintf fmt
          (if !first
           then "%g v%d"
           else "@ +@ %g v%d")
          k lpv;
        first := false;
      end le;
      Format.fprintf fmt "@]";
    in
    Format.fprintf fmt "@[<v>";
    M.iter begin fun m le ->
      Format.fprintf fmt "Monom (%a) %a@,"
        (Monom.print ~ascii:true) m
        dump_le le
    end a;
    Format.fprintf fmt "@]"

  (* Performs: le2 += k * le1 *)
  let linexpr_addmul le2 k le1 =
    Hashtbl.iter begin fun v kv1 ->
      let kv2 = try Hashtbl.find le2 v with Not_found -> 0. in
      Hashtbl.replace le2 v (kv2 +. k *. kv1)
    end le1

  let add_poly le =
    Poly.fold
      begin fun monom k new_annot ->
        let le_old =
          try M.find monom new_annot
          with Not_found -> new_linexpr ()
        in
        linexpr_addmul le_old k le;
        M.add monom le_old new_annot
      end

  let exec_assignment (v, e) annot =
    let subst e =
      M.fold begin fun monom le ->
        add_poly le (monom_subst v e monom)
      end annot M.empty
    in
    match e with
    | ERandom ->
      let fresh = Utils.fresh_name () in
      let e = Poly.of_monom (Monom.of_var fresh) 1. in
      subst e
    | e -> subst (Poly.of_expr e)

  let add_lprow_array ?(k=0.) arr o =
    begin
      stats.num_lpcons <- stats.num_lpcons + 1;
      Clp.add_row
        { Clp.row_lower = if o = Le then neg_infinity else k
        ; Clp.row_upper = if o = Ge then infinity else k
        ; Clp.row_elements = arr
        };
    end

  (* Constrain the linear expression le
     against the constant k.
  *)
  let add_lprow ?(k=0.) le o =
    let l =
      Hashtbl.fold begin fun v kv l ->
        if abs_float kv <= fsmall
          then l
          else (v, kv) :: l
      end le []
    in
    if l <> [] then begin
      if false then
      begin
        List.iter (fun (v, kv) ->
          Format.eprintf "%g * v%d + " kv v;) l;
        Format.eprintf "0 %s %g@."
          (match o with Ge -> ">=" | Le -> "<=" | Eq -> "=")
          k;
      end;
      add_lprow_array (Array.of_list l) o ~k
    end

  let of_poly p =
    Poly.fold begin fun monom k annot ->
      let v = new_lpvar () in
      let le = new_linexpr () in
      Hashtbl.add le v 1.;
      add_lprow le Eq ~k;
      M.add monom le annot
    end p M.empty

  let monoms a =
    M.fold (fun m _ l -> m :: l) a []

  (* Pointwise constrain annot1 and annot2. *)
  let constrain annot1 o annot2 =
    begin
      (* Constrain common coefficients. *)
      M.iter begin fun m le1 ->
        let le = Hashtbl.copy le1 in
        begin
          try linexpr_addmul le (-1.) (M.find m annot2)
          with Not_found -> ()
        end;
        add_lprow le o
      end annot1;
      (* Constrain the coefficients in annot2 only. *)
      M.iter begin fun m le2 ->
        if not (M.mem m annot1) then
          add_lprow le2 (swap_order o);
      end annot2;
    end

  let expand l pl =
    let le = new_linexpr () in
    (* Compute Σ(kᵢ * plᵢ) as an annotation. *)
    let plsum, kpl =
      List.fold_left begin fun (plsum, kpl) p ->
        let kp = new_lpvar () in
        Hashtbl.clear le;
        Hashtbl.add le kp 1.;
        (add_poly le p plsum, kp :: kpl)
      end (M.empty, []) pl in
    (* Add plsum and l (in plsum). *)
    let plsum =
      M.merge begin fun _ leo vo ->
        let le =
          match leo with
          | Some le -> le
          | None -> new_linexpr ()
        in
        match vo with
        | Some v -> Hashtbl.add le v 1.; Some le
        | None -> failwith "impossible"
      end plsum l in
    (plsum, kpl)

  (* Create a new annotation using the init function to
     create new coefficients.  The returned annotation
     has an LP variable for every monomial in the list
     of polynomials pl and in the annotation annot.
  *)
  let frame_from ?init:(init=fun _ -> new_lpvar ()) pl annot =
    let frame = M.mapi (fun m _ -> init m) annot in
    let frame =
      List.fold_left begin fun frame p ->
        Poly.fold begin fun m _ frame ->
          if M.mem m frame
            then frame
            else M.add m (init m) frame
        end p frame
      end frame pl in
    frame

  (* Returns annot' such that  annot' >= annot, using a
     list of non-negative polynomials.  If the polynomials
     are actually null, the returned potential has the
     same value as the passed one.
  *)
  let weaken pl annot =
    let l = frame_from pl annot in
    let exannot, kpl = expand l pl in
    constrain exannot Eq annot;
    let annot', kpl' = expand l pl in
    List.iter2 begin fun kp1 kp2 ->
      assert (kp1 <> kp2);
      add_lprow_array [| kp2, 1.; kp1, -1. |] Ge;
    end kpl kpl';
    (annot', List.rev (List.combine kpl kpl'))

  (* Split an annotation into two annotations that add
     to the argument annotation.  The first element of
     the pair result is a purely local annotation and
     the second one is purely global.
  *)
  let split gs annot =
    M.fold begin fun m le (purel, pureg) ->
      match classify_monom gs m with
      | `Mixed ->
        (* Mixed term, we currently zero it out.
           FIXME, we should handle cases where the
           monom is a product of a pure global and
           a pure local part.
        *)
        add_lprow le Eq;
        (purel, pureg)
      | `Local -> (M.add m le purel, pureg)
      | `Global | `Constant -> (purel, M.add m le pureg)
    end annot (M.empty, M.empty)

  (* An operation opposite to the split one. *)
  let merge (purel, pureg) =
    M.merge begin fun m leo1 leo2 ->
      match leo1, leo2 with
      | Some le, None
      | None, Some le -> Some le
      | Some le1, Some le2 ->
        if not (Monom.is_one m) then
          let _ =
            Format.eprintf "Merge error on monom: %a@."
              (Monom.print ~ascii:true) m in
          failwith "invalid Potential.merge call"
        else
          let le = new_linexpr () in
          linexpr_addmul le 1. le1; (* ----------------------------- odd... *)
          linexpr_addmul le 1. le2;
          Some le
      | None, None -> assert false
    end purel pureg

  let addmul annot1 k annot2 =
    M.merge begin fun _ leo1 leo2 ->
      match leo1, leo2 with
      | Some le, None
      | None, Some le -> Some le
      | Some le1, Some le2 ->
        let le = new_linexpr () in
        linexpr_addmul le 1. le1;
        linexpr_addmul le (float_of_int k) le2;
        Some le
      | None, None -> assert false
    end annot1 annot2

  let solve_min pl start_annot =
    let absl = ref [] in
    M.iter begin fun m le ->
      (* Zero out all fresh variables created by
         non-deterministic assignments.
      *)
      if Monom.var_exists Utils.is_fresh m then
        add_lprow le Eq
    end start_annot;
    let l = frame_from pl start_annot ~init:begin fun _ ->
        let v = new_lpvar () and abs = new_lpvar () in
        add_lprow_array [| abs, 1.; v, +1. |] Ge;
        add_lprow_array [| abs, 1.; v, -1. |] Ge;
        absl := abs :: !absl;
        v
      end in
    let exannot, kpl = expand l pl in
    constrain exannot Eq start_annot;
    let vmax = new_lpvar () in
    List.iter (fun k ->
      add_lprow_array [| vmax, 1.; k, -1. |] Ge) kpl;

    Time.wrap_duration stats.lp_runtime begin fun () ->
      (* Initial solving call trying to minimize the
         coefficients of the frame L and the max of
         all coefficients of pl polynomials.
      *)
      let obj = Clp.objective_coefficients () in
      List.iter (fun k -> obj.(k) <- 1.) !absl;
      Clp.change_objective_coefficients obj;
      Clp.set_log_level 0;
      Clp.initial_solve ();
      if Clp.status () <> 0 then None else

      (* Second solving call, this time minimizing
         the sum of coefficients of the polynomials
         in pl.
      *)
      let () = if false then
        Printf.printf "[i] Second optimization round.\n" in
      let sol = Clp.primal_column_solution () in
      add_lprow_array [| vmax, 1. |] Le ~k:sol.(vmax);
      List.iter (fun k ->
        obj.(k) <- 0.;
        add_lprow_array [| k, 1. |] Eq ~k:sol.(k)) !absl;
      List.iter (fun k -> obj.(k) <- 1.) kpl;
      Clp.change_objective_coefficients obj;
      Clp.primal ();
      if Clp.status () <> 0 then None else

      (* Build polynomial solution. *)
      let sol = Clp.primal_column_solution () in
      Some sol
    end

  let annot_sol sol a =
    M.fold begin fun m le poly ->
      let k =
        Hashtbl.fold begin fun v kv k ->
          k +. kv *. sol.(v)
        end le 0.
      in Poly.add_monom m k poly
    end a (Poly.zero ())

  let focus_annot_sol sol (ka, kb) =
    (sol.(ka), sol.(kb))

end

let run ai_results ai_is_nonneg (gl, fl) =
  Clp.reset ();
  reset_stats ();

  (* The collection of annotations for each function. *)
  let annots = Hashtbl.create 11 in
  let new_func_annot fn =
    let last_id =
      try fst (Hashtbl.find annots fn)
      with Not_found -> -1 in
    let id = last_id + 1 in
    let func_annot = ref [||] in
    Hashtbl.add annots fn (id, func_annot);
    (id, func_annot)
  in

  let gs = IdSet.of_list gl in
  let debug_dumps = ref [] in
  let _pzero = Potential.of_poly (Poly.zero ()) in

  (* Find all the non-negative focus functions at a
     given program point.
  *)
  let find_focus f node focus =
    let ai = Hashtbl.find ai_results f in
    let ok f =
      List.for_all (ai_is_nonneg ai.(node)) f.checks in
    let res = List.filter ok focus in
    if false then begin
      let fn = List.find (fun g -> g.fun_name = f) fl in
      let fprint fmt {checks = c; proves = f; _} =
        Format.fprintf fmt (if c <> [] then "* %a" else ". %a")
          Poly.print f in
      Format.eprintf "At %a, using:@.%a@."
        Utils.print_position fn.fun_body.g_position.(node)
        (Print.list ~first:"@[<v>" ~sep:"@ " ~last:"@]" fprint) res
    end;
    stats.max_focus <- max (List.length res) stats.max_focus;
    res
  in
  let polys_of_focus = List.map (fun f -> f.proves) in

  (* Analyze the function with name fname for the query
     query.  The return value is a pair consisting of
     an identifier for the given run (used to create
     hints for function calls), and a final annotation
     for the start point of the function.
  *)
  let rec do_fun ctx fname degree query =

    if degree = 0 then (-1, query) (* Optimization. *) else
    try
      let (id, mk_start_annot, end_annot) = List.assoc fname ctx in
      Potential.constrain end_annot Eq query;
      (id, mk_start_annot ())
    with Not_found ->

    let f = List.find (fun f -> f.fun_name = fname) fl in
    let body = f.fun_body in
    let focus = Focus.one :: f.fun_focus in
    let monoms =
      let monoms = Potential.monoms query in
      List.fold_left begin fun monoms f ->
        Poly.fold (fun m _ ms -> m :: ms) f.proves monoms
      end monoms focus
    in
    let focus, monoms =
      List.filter (fun f -> Poly.degree f.proves <= degree) focus,
      List.filter (fun m -> Monom.degree m <= degree) monoms
    in
    let global_monoms = (* --------------------------------- TODO, precompute them. *)
      List.filter (fun m ->
        Monom.degree m < degree &&
        classify_monom gs m = `Global ||
        classify_monom gs m = `Constant
      ) monoms
    in
    let rec_annot = ref None in (* in case of recursion *)
    let mk_rec_annot () =
      match !rec_annot with
      | Some annot -> annot
      | None ->
        let annot = Potential.new_annot monoms in
        rec_annot := Some annot;
        annot
    in

    (* Create the function annotation that will be returned. *)
    let (id, func_annot) = new_func_annot fname in
    let ctx = (fname, (id, mk_rec_annot, query)) :: ctx in

    let hints = Array.map (fun _ -> []) body.Graph.g_position in
    let annot = Array.map (fun _ -> `Todo) body.Graph.g_position in

    (* Create a new potential annotation resulting from
       executing one action (backwards).
    *)
    let do_action node act a =
      match act with
      | Graph.AWeaken ->
        let focus = find_focus fname node focus in
        let polys = polys_of_focus focus in
        let a, fa = Potential.weaken polys a in
        hints.(node) <- (List.combine fa focus);
        a
      | Graph.AGuard LRandom -> debug_dumps := a :: !debug_dumps; a
      | Graph.AGuard _ | Graph.ANone -> a
      | Graph.AAssign (v, e) -> Potential.exec_assignment (v, e) a
      | Graph.ACall f' ->
        let (la, ga) = Potential.split gs a in
        let ga1 = Potential.new_annot global_monoms in
        let ga = Potential.addmul ga (-1) ga1 in
        let _, a = do_fun ctx f' degree ga in
        let (_la', ga) = Potential.split gs a in
        let _, a1 = do_fun [] f' (degree-1) ga1 in
        let (_la1, ga1) = Potential.split gs a1 in
        (* Potential.constrain _la' Eq _pzero; *)
        let ga = Potential.addmul ga (+1) ga1 in
        let a = Potential.merge (la, ga) in
        a
    in

    (* Annotate all program points starting from
       a given node.  The potential at the end of
       the function is set to query.

       We follow a depth-first search on the graph
       and update annotations for nodes lazily, this
       allows to reduce the number of LP variables.
    *)
    let rec dfs node =
      match annot.(node) with
      | `Done a -> a
      | `Doing ->
        let a = Potential.new_annot monoms in
        annot.(node) <- `Done a;
        a
      | `Todo ->
        annot.(node) <- `Doing;
        let a =
          match body.Graph.g_edges.(node) with
          | [] ->
            if node <> body.Graph.g_end then Utils._TODO "mmh?";
            query
          | (act, node') :: edges ->
            let annot = do_action node act (dfs node') in
            List.fold_left begin fun annot (act, node') ->
              let annot' = do_action node act (dfs node') in
              Potential.constrain annot Eq annot';
              annot
            end annot edges
        in
        begin match annot.(node) with
        | `Doing -> ()
        | `Done a' -> Potential.constrain a Eq a'
        | `Todo -> failwith "unreachable"
        end;
        annot.(node) <- `Done a;
        a
    in

    let start_annot = dfs body.Graph.g_start in
    begin match !rec_annot with
    | Some annot -> Potential.constrain start_annot Eq annot
    | None -> ()
    end;
    func_annot :=
      Array.mapi (fun i -> function
        | `Done a -> (a, hints.(i))
        | _ -> failwith "impossible dead code"
      ) annot;
    (id, start_annot)

  in (* End of do_fun. *)

  fun start degree query ->
    let fstart = List.find (fun f -> f.fun_name = start) fl in
    let query = Potential.of_poly query in
    let (_, start_annot) = do_fun [] start degree query in
    Potential.constrain start_annot Ge _pzero;
    match
      let start_node = fstart.fun_body.Graph.g_start in
      let focus = Focus.one :: fstart.fun_focus in
      let focus = find_focus start start_node focus in
      Potential.solve_min (polys_of_focus focus) start_annot
    with
    | None -> None
    | Some sol ->
      let make_poly = Potential.annot_sol sol in
      (*
      List.iter begin fun a ->
        Format.eprintf "Dump: %a@."
          Poly.print_ascii (make_poly a)
      end !debug_dumps;
      *)
      let annots_final = Hashtbl.create 11 in
      Hashtbl.iter (fun fname (_, func_annot) ->
        let func_annots =
          try Hashtbl.find annots_final fname
          with Not_found -> []
        in
        Hashtbl.replace annots_final fname (
          Array.map (fun (annot, hints) ->
            let hints =
              List.map (fun (fa, f) ->
                (Potential.focus_annot_sol sol fa, f)) hints
            in
            (make_poly annot, hints)
          ) !func_annot :: func_annots
        )
      ) annots;
      Some (annots_final, make_poly start_annot)
