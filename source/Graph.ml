(* Quentin Carbonneaux - 2016 *)

(* Van Chan Ngo, 2016 *)

open Types
include Graph_Types

type stats =
  { mutable weaken_map: (id * int) list }

let stats =
  { weaken_map = [] }

(* Construct a graph representation of the
   given IMP program. The nodes of the graph
   are program points and the edges have
   actions on them.
*)

(*
 * the set of all edges from a node A is represented
 * by an element with index A in an array of (action * node) list
 *)
 
let from_imp impf =

  let h_position = Hashtbl.create 51 in
  let h_edges = Hashtbl.create 51 in

  let next_node = ref 0 in
  let new_node pos =
    let node = !next_node in
    Hashtbl.add h_position node pos;
    incr next_node;
    node
  in

  let new_edge src act dst =
    if dst < 0 then failwith "invalid input program";
    Hashtbl.add h_edges src (act, dst)
  in

  let rec goi fin loo pos = function
    | IMP.IBreak -> loo
    | IMP.IWeaken ->
      let beg = new_node pos in
      new_edge beg AWeaken fin;
      beg
    | IMP.IAssume log ->
      let beg = new_node pos in
      new_edge beg (AGuard log) fin;
      beg
    | IMP.IAssign (id, e) ->
      let beg = new_node pos in
      new_edge beg (AAssign (id, e)) fin;
      beg
    | IMP.IIf (log, bi, be) ->
      let beg = new_node pos in
      let begi = gob fin loo bi in
      let bege = gob fin loo be in
      new_edge beg (AGuard log) begi;
      new_edge beg (AGuard (LNot log)) bege;
      beg
    | IMP.IWhile (log, b) ->
      let jmp = new_node b.IMP.b_end_p in
      let begb = gob jmp fin b in
      new_edge jmp (AGuard log) begb;
      new_edge jmp (AGuard (LNot log)) fin;
      jmp
    | IMP.ILoop b ->
      let jmp = new_node b.IMP.b_end_p in
      let begb = gob jmp fin b in
      new_edge jmp (AGuard LTrue) begb;
      begb
    | IMP.ICall (idl, idf, el) ->
      let beg = new_node pos in
      new_edge beg (ACall (idl, idf, el)) fin;
      beg

  and goil fin loo = function
    | [] -> fin
    | (i, pos) :: b ->
      let fin = goil fin loo b in
      goi fin loo pos i

  and gob fin loo { IMP.b_end_p; b_body } =
    let beg = new_node b_end_p in
    new_edge beg (AGuard LTrue) fin;
    goil beg loo b_body

  in

  let g_end = new_node impf.fun_end_p in
  let g_start = gob g_end (-1) impf.fun_body in
  let g_position = Array.make !next_node impf.fun_end_p in
  let g_edges = Array.make !next_node [] in
  for i = 0 to !next_node - 1 do
    g_position.(i) <- Hashtbl.find h_position i;
    g_edges.(i) <- Hashtbl.find_all h_edges i;
  done;
  (* impf is typed func in Graph_Types in which its body is a graph *)
  { impf with fun_body = { g_start; g_end; g_edges; g_position } }

let rpo_order gfunc =
  let g = gfunc.fun_body in
  let map = Array.map (fun _ -> -1) g.g_edges in
  let rec dfs node n =
    if map.(node) <> -1 then n else
    begin
      map.(node) <- 0;
      let n = List.fold_left
        (fun n (_, dst) -> dfs dst n)
        n g.g_edges.(node) in
      map.(node) <- n;
      n + 1
    end in
  let nlive = dfs g.g_start 0 in
  Array.iteri (fun i n -> map.(i) <- nlive - 1 - n) map;
  let new_edges = Array.make nlive [] in
  let new_position = Array.make nlive Utils.dummy_position in
  Array.iteri (fun i n ->
    let tr_edges = List.map (fun (a, d) -> (a, map.(d))) in
    if n <> -1 then begin
      new_edges.(n) <- tr_edges g.g_edges.(i);
      new_position.(n) <- g.g_position.(i);
    end
  ) map;
  { gfunc with fun_body =
    { g_start = map.(g.g_start)
    ; g_end = map.(g.g_end)
    ; g_edges = new_edges
    ; g_position = new_position
    }
  }

let add_loop_counter cnt gfunc =
  let gfunc = rpo_order gfunc in
  let g = gfunc.fun_body in
  let nnodes = Array.length g.g_edges in
  let incs = ref [[AAssign (cnt, ENum 0), g.g_start]] in
  let nincs = ref 1 in
  let add_increment dst =
    let e = EAdd (ENum 1, EVar cnt) in
    incs := [AAssign (cnt, e), dst] :: !incs;
    incr nincs;
    !nincs - 1 + nnodes
  in
  let new_edges =
    Array.mapi begin fun src ->
      List.map begin function
        | (a, dst) when dst <= src ->
	  (a, add_increment dst)
	| e -> e
      end
    end g.g_edges
  in
  let incs = Array.of_list (List.rev !incs) in
  let new_position =
    Array.map begin function
      | [_, dst] -> g.g_position.(dst)
      | _ -> assert false
    end incs
  in
  { gfunc with fun_body =
    { g with
      g_start = nnodes;
      g_edges = Array.append new_edges incs;
      g_position = Array.append g.g_position new_position;
    }
  }

module type AbsInt = sig
  type absval
  val analyze: dump:bool -> func list -> id ->
               (string, absval array) Hashtbl.t
  val is_nonneg: absval -> Polynom.Poly.t -> bool
  val get_nonneg: absval -> Polynom.Poly.t list
end

module AbsInt = struct
  module Apron: AbsInt = Graph_AI_Apron
  module Simple: AbsInt = Graph_AI_Simple
end
