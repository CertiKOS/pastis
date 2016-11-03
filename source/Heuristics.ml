(* Quentin Carbonneaux - 2016 *)

open Types
open Graph
open Polynom
open Focus_Builder

module PSet = Set.Make(struct
  type t = Poly.t
  let compare = Poly.compare
end)

(* Helper functions to create higher degree indices. *)

let rec prodfold n l ?(acc=[]) accf f =
  if n = 0 then f acc accf else
  match l with
  | [] -> accf
  | x :: l ->
    let rec iota i accf =
      if i > n then accf else
      let acc = (x, i) :: acc in
      iota (i+1) (prodfold (n-i) l ~acc accf f)
    in iota 0 accf

(* The heuristic to infer focus functions.
*)
let add_focus ?(deg=1) ai_results ai_get_nonneg gfunc =
  let pzero = Poly.zero () in

  let assigns =
    Array.fold_left
      (List.fold_left begin fun l (a, _) ->
          match a with
          | AAssign (_, ERandom) -> l
          | AAssign (v, e) -> (v, Poly.of_expr e) :: l
          | _ -> l
        end)
      [] gfunc.fun_body.g_edges
  in
  (* Collect all conditions used by the program. *)
  let base =
    Hashtbl.fold begin fun _ abs_array base ->
      Array.fold_left begin fun base abs ->
        List.fold_left
          (fun b p -> PSet.add p b) base
          (ai_get_nonneg abs)
      end base abs_array
    end ai_results PSet.empty
  in
  (* Close them under all the program assignments. *)
  let close acc (v, pe) =
    let mv = Monom.of_var v in
    if abs_float (Poly.get_coeff mv pe) = 1. then acc else
    PSet.fold (fun p -> PSet.add (poly_subst v pe p))
      base acc
  in
  let base = List.fold_left close base assigns in
  (* Remove constants. *)
  let base =
    PSet.filter begin fun p ->
      match Poly.is_const p with
      | Some _ -> false
      | None -> true
    end base
  in

  if false then
  PSet.iter (fun p ->
    Format.eprintf " %a@." Poly.print p) base;

  (* Create larger degree indices using product()
     and binom_monotonic().
  *)
  let rec binom n acc =
    if n = 0 then acc else
    let binom_max pol acc =
      binom_monotonic n
        (max0_ge_0 pol)
        (check_ge pzero pzero) ::
      binom_monotonic n
        (max0_ge_arg pol)
        (check_ge pol pzero) ::
      binom_monotonic n
        (max0_le_arg (check_ge pol pzero))
        (max0_ge_0 pol) ::
      acc
    in
    binom (n-1) (PSet.fold binom_max base acc)
  in
  let degn = binom deg [] in
  let base_list = PSet.elements base in
  let degn =
    if false then degn else
    List.fold_left (fun acc x ->
      prodfold (deg - degree x) base_list acc
      begin fun prod acc ->
        List.fold_left
          (fun p (b, e) ->
            if e = 0 then p else
            product p
              (binom_monotonic e
                (max0_ge_0 b)
                (check_ge pzero pzero))
          ) x prod :: acc
      end
    ) degn degn in

  (* Add focus functions. *)
  let fun_focus =
    List.rev_append
      gfunc.fun_focus
      (List.map export degn)
  in
  (*
  List.iter (fun (l, p) ->
    if l = [] then
    Format.eprintf "%a@." Poly.print_ascii p) fun_focus;
  *)
  { gfunc with fun_focus }


(* Place weakening points automatically.
   A good heuristic is to insert them at
   the end of guard edges.
*)
let add_weaken ({ fun_name; fun_body = g } as gfunc) =
  let is_guard = function
    | AGuard _ -> true
    | _ -> false
  in
  let weaken = ref [] in
  let nweaken = ref 0 in
  let add_weaken =
    let nnodes = Array.length g.g_edges in
    fun dst ->
      weaken := [AWeaken, dst] :: !weaken;
      incr nweaken;
      !nweaken - 1 + nnodes
  in
  let new_edges =
    Array.mapi
    begin fun src ->
      List.map
      begin function
        | act, dst when is_guard act ->
          let d_edges = g.g_edges.(dst) in
          if d_edges = []
          || not (List.for_all (fun (a, _) -> is_guard a) d_edges)
          then (act, add_weaken dst)
          else (act, dst)
        | e -> e
      end
    end
    g.g_edges
  in
  let weaken = Array.of_list (List.rev !weaken) in
  let new_position =
    Array.map begin function
      | [_, dst] -> g.g_position.(dst)
      | _ -> assert false
    end weaken
  in
  let fun_body =
    { g with
      g_edges = Array.append new_edges weaken;
      g_position = Array.append g.g_position new_position;
    } in
  stats.weaken_map <- (fun_name, !nweaken) :: stats.weaken_map;
  { gfunc with fun_body }
