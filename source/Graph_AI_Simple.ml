(* Quentin Carbonneaux - 2016 *)

(* Van Chan Ngo, 2016 *)

(* Implementation of a simple abstract domain.
   The advantage is that the outcome is more
   predictible than what we obtain using more
   complex domains.
*)

open Types
open Graph_Types
open Polynom

module L = Presburger.L

let monom_var m =
  assert (Monom.degree m = 1);
  match Monom.pick m with
  | (Factor.Var v, _) -> v
  | _ -> assert false

module Translate = struct

  let linear_of_poly p =
    Poly.fold begin fun m k lin ->
      let k = int_of_float k in
      if Monom.is_one m then
        L.addk k lin
      else
        L.set (monom_var m) k lin
    end p (L.const 0)

  let linear_of_expr e =
    let p = Poly.of_expr e in
    if Poly.degree p > 1 then DNF.true_ else
    DNF.lift (linear_of_poly p)

  let dnf_of_logic l =
    let one = ENum 1 in
    let cmp e1 c e2 =
      match c with
      | Le -> linear_of_expr (ESub (e1, e2))
      | Lt -> linear_of_expr (ESub (EAdd (one, e1), e2))
      | Ge -> linear_of_expr (ESub (e2, e1))
      | Gt -> linear_of_expr (ESub (EAdd (one, e2), e1))
      | Eq ->
        DNF.conjunct
          (linear_of_expr (ESub (e1, e2)))
          (linear_of_expr (ESub (e2, e1)))
      | Ne ->
        DNF.disjunct
          (linear_of_expr (ESub (EAdd (one, e1), e2)))
          (linear_of_expr (ESub (EAdd (one, e2), e1)))
    in
    DNF.of_logic cmp l

end

type transfer =
  | TGuard of L.sum DNF.t
  | TAssign of id * Poly.t option
  | TSimpleCall of id

module HyperGraph = struct

  (* Build the hypergraph required by the fixpoint library. *)

  type info = (string, func) Hashtbl.t

  type vertex = id * int  (* pair of function name and node id *)
  type hedge = int

  let print_vertex info fmt (vf, vp) =
    let f = Hashtbl.find info vf in
    let pos = f.fun_body.g_position.(vp) in
    Utils.print_position fmt pos

  let from_funcl fl =
    let new_edge =
      let next_edge = ref (-1) in
      fun () -> incr next_edge; !next_edge in

    (* vertex:   type of vertices
       hedge:    type of hyper-edges
       unit:     data associated to the vertices
       transfer: data associated to the hyper-edges
       info:     data associated to the whole graph
    *)
    let info = Hashtbl.create 51 in
    let g: (vertex, hedge, unit, transfer, info) PSHGraph.t =
      PSHGraph.create PSHGraph.stdcompare 3 info in

    (* Add all the vertices and fill the info table first. *)
    List.iter begin fun f ->
      Hashtbl.add info f.fun_name f;
      for node = 0 to Array.length f.fun_body.g_edges - 1 do
        PSHGraph.add_vertex g (f.fun_name, node) ();
      done;
    end fl;

    (* Then add all the edges. *)
    List.iter begin fun f ->
      Array.iteri begin fun src el ->
        List.iter begin fun (act, dst) ->
          let src = f.fun_name, src in
          let dst = f.fun_name, dst in
          match act with
          | AWeaken ->
            PSHGraph.add_hedge g (new_edge ())
              (TGuard DNF.true_) ~pred:[|src|] ~succ:[|dst|];
          | AGuard log ->
            let disj = Translate.dnf_of_logic log in
            PSHGraph.add_hedge g (new_edge ())
              (TGuard disj) ~pred:[|src|] ~succ:[|dst|];
          | AAssign (id, e) ->
            let peo =
              match e with
              | ERandom -> None
              | _ -> Some (Poly.of_expr e)
            in
            PSHGraph.add_hedge g (new_edge ())
              (TAssign (id, peo)) ~pred:[|src|] ~succ:[|dst|];
          | ASimpleCall id ->
            PSHGraph.add_hedge g (new_edge ())
              (TSimpleCall id) ~pred:[|src|] ~succ:[|dst|];
          | ACall (_idl, _idf', _el) ->
            Utils._TODO "AISimple_call"
        end el;
      end f.fun_body.g_edges;
    end fl;
    g

end

module Solver = struct

  (* Here we use the fixpoint library to find an
     abstract state for each vertex of the hypergraph.
  *)

  let make_fpmanager graph widening apply =
    let info = PSHGraph.info graph in
    let dont_print _ _ = () in
    { Fixpoint.bottom = (fun _ -> Presburger.bottom)
    ; canonical = (fun _ _ -> ())
    ; is_bottom = (fun _ a -> not (Presburger.sat a))
    ; is_leq = begin fun _ a b ->
        List.for_all (Presburger.implies a) b
      end
    ; join = (fun _ -> Presburger.join)
    ; join_list = begin fun _ absl ->
        List.fold_left Presburger.join
          Presburger.bottom absl
      end
    ; odiff = None
    ; widening = (fun _ -> widening)
    ; abstract_init = (fun _ -> [])
    ; arc_init = (fun _ -> ())
    ; apply = apply graph
    ; print_vertex = HyperGraph.print_vertex info
    ; print_hedge = Format.pp_print_int
    ; print_abstract = Presburger.print
    ; print_arc = begin fun fmt () ->
        Format.pp_print_string fmt "()"
      end
    ; accumulate = false
    ; print_fmt = Format.std_formatter
    ; print_analysis = false
    ; print_component = false
    ; print_step = false
    ; print_state = false
    ; print_postpre = false
    ; print_workingsets = false
    ; dot_fmt = None
    ; dot_vertex = dont_print
    ; dot_hedge = dont_print
    ; dot_attrvertex = dont_print
    ; dot_attrhedge = dont_print
    }

  (* We can now define the action of transfers on
     the abstract state.
  *)

  let apply_TGuard abs disj =
    let abs_and_disj = List.map (Presburger.meet abs) disj in
    match abs_and_disj with
    | [] -> Presburger.bottom
    | [x] -> x
    | x :: disj -> List.fold_left Presburger.join x disj

  let apply_TAssign abs id peo =
    let forget_id abs =
      List.filter (fun l -> L.coeff id l = 0) abs in
    if peo = None then forget_id abs else
    let pe = match peo with Some x -> x | _ -> assert false in

    (* Linear assignment, we consider two cases:
       1. If the assignment is an increment "x = x+i"
          we can substitute the assigned variable with
          "x-i".
       2. Otherwise, "x = e", we find upper and lower
          bounds on e and add these to x.
    *)
    if Poly.degree pe <= 1 then
      let sign x = if x < 0 then (-x, -1) else (+x, +1) in
      let k = Poly.get_coeff (Monom.of_var id) pe in
      let k, ks = sign (int_of_float k) in

      if k <> 0 then
        (* Case 1. *)
        let abs', abs =
          List.partition (fun i -> L.coeff id i <> 0) abs
        in
        let abs' =
          let i' = Translate.linear_of_poly pe in
          List.map begin fun i ->
            let idk, idks = sign (L.coeff id i) in
            let l = Presburger.lcm idk k in
            let i = L.mult (l/idk) i in
            if ks = idks then
              let i = L.plus (-l/k) i' i in
              assert (L.coeff id i = 0);
              L.set id (l/k) i
            else
              let i = L.plus (l/k) i' i in
              assert (L.coeff id i = 0);
              L.set id (-l/k) i
          end abs'
        in
        List.rev_append abs' abs

      else
        (* Case 2. *)
        let abs = forget_id abs in
        let lbs, ubs =
          Poly.fold begin fun m k (lbs, ubs) ->
            let k = int_of_float k in
            let addk k (k', l) = (k', L.addk (k*k') l) in
            if Monom.is_one m then
              (List.map (addk (+k)) lbs, List.map (addk (-k)) ubs)
            else
              let v = monom_var m in
              let c_comp f l = f (L.coeff v l) 0 in
              let ubs' = List.filter (c_comp (>)) abs in
              let lbs' = List.filter (c_comp (<)) abs in
              let ubs', lbs', k =
                if k < 0 then (lbs', ubs', -k) else (ubs', lbs', +k)
              in
              let addscale l (k', l') =
                let vk = Pervasives.abs (L.coeff v l) in
                let l = L.mult k l in
                let lcm = Presburger.lcm vk k' in
                let l = L.plus (lcm/vk) l (L.mult (lcm/k') l') in
                (lcm, L.set v 0 l)
              in
              let merge a a' =
                List.concat
                  (List.map (fun l -> List.map (addscale l) a) a')
              in
              (merge lbs lbs', merge ubs ubs')
          end pe ([(1, L.const 0)], [(1, L.const 0)])
        in
        let bound low (k, l) =
          let coeff = if low then (-1) else (+1) in
          L.plus coeff (L.set id k (L.const 0)) l
        in
        let lbs = List.map (bound true) lbs in
        let ubs = List.map (bound false) ubs in
        List.rev_append lbs (List.rev_append ubs abs)

    (* General polynomial assignment, the best we
       we can do is bound independently each monom
       by constants and aggregate the bounds.
    *)
    else
      forget_id abs

  (*
  let apply_TAssign abs id peo =
    let res = apply_TAssign abs id peo in
    Format.eprintf "apply_TAssign(%a) = %a@."
      Presburger.print abs Presburger.print res;
    res
  *)

  let apply graph hedge tabs =
    let transfer = PSHGraph.attrhedge graph hedge in
    let res =
      match transfer with
      | TGuard disj -> apply_TGuard tabs.(0) disj
      | TAssign (id, pe) -> apply_TAssign tabs.(0) id pe
    in ((), res)

  let widening a b =
    let in_a x = List.exists (L.eq x) a in
    Presburger.minimize (List.filter in_a b)

  let compute graph fstart =
    let info = PSHGraph.info graph in
    let fs = Hashtbl.find info fstart in
    let starts =
      PSette.singleton
        PSHGraph.stdcompare.PSHGraph.comparev
        (fstart, fs.fun_body.g_start) in
    let fpman = make_fpmanager graph widening apply in
    ( fpman
    , Fixpoint.analysis_std
        fpman graph starts
        (Fixpoint.make_strategy_default
          ~vertex_dummy:("", -1)
          ~hedge_dummy:(-1)
          graph starts) )

end

let debug_print fmt info graph res =
  let print_transfer fmt = function
    | TGuard disj ->
      Format.fprintf fmt "Guard %a"
        (Print.list ~first:"(@[<h>" ~sep:" ||@ " ~last:"@])"
          Presburger.print)
        disj;
    | TAssign (v, None) ->
      Format.fprintf fmt "Assign %s = random" v
    | TAssign (v, Some pe) ->
      Format.fprintf fmt "Assign %s = %a" v Poly.print_ascii pe;
  in
  let print_hedge_attr fmt hedge transfer =
    Format.fprintf fmt "%a" print_transfer transfer
  in
  PSHGraph.print_dot
    begin fun fmt (vf, vn) -> Format.fprintf fmt "%s_%d" vf vn end
    begin fun fmt hid -> Format.fprintf fmt "e_%d" hid end
    begin fun fmt v _ ->
      Presburger.print fmt (PSHGraph.attrvertex res v)
    end
    print_hedge_attr
    fmt graph

(* Common API for abstract interpretation modules. *)

type absval = Presburger.L.sum list

let analyze ~dump fl fstart =
  let graph = HyperGraph.from_funcl fl in
  let info = PSHGraph.info graph in
  let (fpman, res) = Solver.compute graph fstart in

  if dump then begin
    let (fn, oc) = Filename.open_temp_file "" ".dot" in
    let fpdf = fn ^ ".pdf" in
    let fmt = Format.formatter_of_out_channel oc in
    debug_print fmt info graph res;
    close_out oc;
    let cmd = Printf.sprintf "dot -O -Tpdf %s" fn in
    if (try Sys.command cmd with Sys_error _ -> 1) <> 0 then
      Printf.eprintf
        "Error: '%s' failed, be sure to have Graphviz installed with PDF support.\n"
        cmd
    else Utils.show_remove_pdf fpdf;
    Sys.remove fn;
  end;

  let resh = Hashtbl.create 51 in
  Hashtbl.iter begin fun fname f ->
    Hashtbl.add resh fname
      (Array.make (Array.length f.fun_body.g_edges) []);
  end info;

  PSHGraph.iter_vertex res
  begin fun (vf, vn) abs ~pred ~succ ->
    let map = Hashtbl.find resh vf in
    map.(vn) <- abs;
  end;
  resh

let is_nonneg abs pol =
  if Poly.degree pol > 1 then false else
  let l = L.mult (-1) (Translate.linear_of_poly pol) in
  List.exists (L.eq l) abs || Presburger.implies abs l

let get_nonneg abs =
  let neg x = float_of_int (-x) in
  let poly_of_linear l =
    L.fold
      (fun v k -> Poly.add_monom (Monom.of_var v) (neg k))
      l.L.m (Poly.const (neg l.L.k))
  in List.map poly_of_linear abs
