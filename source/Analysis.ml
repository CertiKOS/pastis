(* Quentin Carbonneaux - 2016 *)

(* Van Chan Ngo, 2016 *)

open Graph
open Types
open Polynom

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

module Potential
: sig
  type annot
  val new_annot: Monom.t list -> annot
  val of_poly: Poly.t -> annot
  val exec_assignment: (id * expr) -> annot -> annot
  val constrain: annot -> order -> annot -> unit
  val rewrite: Poly.t list -> annot -> annot
  val solve_min: Poly.t list -> annot -> annot list -> Poly.t option
  (*val exec_simplecall: id -> annot -> annot*)
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
  let rewrite pl annot =
    let l = frame_from pl annot in
    let exannot, kpl = expand l pl in
    constrain exannot Eq annot;
    let annot', kpl' = expand l pl in
    List.iter2 begin fun kp1 kp2 ->
      assert (kp1 <> kp2);
      add_lprow_array [| kp2, 1.; kp1, -1. |] Ge;
    end kpl kpl';
    annot'

  let solve_min pl annot dumps =
    let absl = ref [] in
    M.iter begin fun m le ->
      (* Zero out all fresh variables created by
         non-deterministic assignments.
      *)
      if Monom.var_exists Utils.is_fresh m then
        add_lprow le Eq
    end annot;
    let l = frame_from pl annot ~init:begin fun _ ->
        let v = new_lpvar () and abs = new_lpvar () in
        add_lprow_array [| abs, 1.; v, +1. |] Ge;
        add_lprow_array [| abs, 1.; v, -1. |] Ge;
        absl := abs :: !absl;
        v
      end in
    let exannot, kpl = expand l pl in
    constrain exannot Ge annot;
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
      let make_poly annot =
        M.fold begin fun m le poly ->
          let k =
            Hashtbl.fold begin fun v kv k ->
              k +. kv *. sol.(v)
            end le 0.
          in Poly.add_monom m k poly
          end annot (Poly.zero ())
      in
      (* Dump debug information. *)
      List.iter (fun annot ->
        Format.eprintf "Dump: %a@."
          Poly.print_ascii (make_poly annot)
      ) dumps;
      Some (make_poly annot)
    end

end

let run ai_results ai_is_nonneg g_file start query =
  let (vl, fl) = g_file in
  reset_stats ();

  let f = List.find (fun f -> f.fun_name = start) fl in
  let focus = ([], Poly.const 1.) :: f.fun_focus in
  let body = f.fun_body in
  let dumps = ref [] in

  let monoms =
    let monoms = Poly.fold (fun m _ ms -> m :: ms) query [] in
    List.fold_left begin fun monoms (_, p) ->
      Poly.fold (fun m _ ms -> m :: ms) p monoms
    end monoms focus
  in

  (* Find all the non-negative focus functions at a
     given program point.
  *)
  let find_focus f node =
    let ai = Hashtbl.find ai_results f in
    let ok (c, _) = List.for_all (ai_is_nonneg ai.(node)) c in
    let res = List.map snd (List.filter ok focus) in
    stats.max_focus <- max (List.length res) stats.max_focus;
    res
  in

  (* Create a new potential annotation resulting from
     executing one action (backwards).
  *)
  let do_action node act a =
    match act with
    | Graph.AWeaken -> Potential.rewrite (find_focus start node) a
    | Graph.AGuard LRandom -> dumps := a :: !dumps; a
    | Graph.AGuard _ -> a
    | Graph.AAssign (v, e) -> Potential.exec_assignment (v, e) a
    | Graph.ACall _ -> Utils._TODO "analysis_call"
    | Graph.ASimpleCall id -> a
  in

  (* Annotate all program points starting from
     a given node.  The potential at the end of
     the function is set to query.

     We follow a depth-first search on the graph
     and update annotations for nodes lazily, this
     allows to reduce the number of LP variables.
  *)
  let annot = Array.map (fun _ -> `Todo) body.Graph.g_position in
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
          Potential.of_poly query
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

  let start_node = body.Graph.g_start in
  let start_annot = dfs start_node in
  let pzero = Potential.of_poly (Poly.zero ()) in
  Potential.constrain start_annot Ge pzero; (* XXX we don't want this *)
  Potential.solve_min (find_focus start start_node) start_annot !dumps
