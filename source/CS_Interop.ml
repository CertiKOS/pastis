open Types
open Graph
open CS_Interop_Types

module Make_Graph(Q: CS_Interop_Types.CS_Querier) = struct

  include Q

  let blk_foldr f x bd =
    let n = get_nins bd in
    let x = ref x in
    for i = n-1 downto 0 do
      x := f (get_ins bd i) !x;
    done;
    !x

  let blk_foldl f x bd =
    let n = get_nins bd in
    let x = ref x in
    for i = 0 to n-1 do
      x := f (get_ins bd i) !x;
    done;
    !x

  let fun_iteri f fd =
    let n = get_nblk fd in
    for i = 0 to n-1 do
      f i (get_blk fd i);
    done

  (* GOAL: Make a function 'graph' that fetches a function
     using a Querier module Q and turns it into a graph
     representation as in Graph_Types.
     Ignore function calls at first. *)

  let graph_from_fundesc (fname, fdesc) =

    (*init (); it will be called outside *)

    (* each block starts with the node equivalent to its id *)
    let h_edges = Hashtbl.create 45 in
    let initialnumber_of_nodes = get_nblk fdesc in
    let next_node = ref (initialnumber_of_nodes - 1) in
    let start_node = 0 in
    let end_node = ref 0 in
    let ret = ref "" in
    let name = fname in
    let locs = get_locs fdesc in
    let _args = get_args fdesc in
    let focus = [] in

    let new_node () =
      let node = !next_node in
      incr next_node;
      node
    in

    let new_edge src act dst =
      if dst < 0 then
        failwith "invalid input propgram";
      Hashtbl.add h_edges src (act, dst)
    in

    let operand = function
      | OpVar v -> EVar v
      | OpCon k -> ENum k
    in

    let do_ins ins s_node =
      match ins with
      | IInc (id, op, arg) ->
         let a_arg = operand arg in
         let n_act = match op with
           | OPlus -> AAssign (id, EAdd (EVar id, a_arg))
           | OMinus -> AAssign (id, ESub (EVar id, a_arg))
         in
         let e_node = new_node () in
         new_edge s_node n_act e_node;
         e_node
      | ICall (ido, id, idl) ->
         let e_node = new_node () in
         let n_act = failwith "calls TODO" in
         new_edge s_node n_act e_node;
         e_node
      | ITick n ->
         let e_node = new_node () in
         new_edge s_node ANone e_node;
         e_node
      | IAssert (lexpr, cmp, rexp) ->
         (*let e_node = new_node () in
         new_edge s_node ANone e_node;
         e_node *)
         s_node
      | ISet (id, argo) ->
         let e_node = new_node () in
         let n_act = match argo with
           | None -> ANone
           | Some arg -> AAssign (id, operand arg)
         in
         new_edge s_node n_act e_node;
         e_node
    in

    (* s_node is the block id *)
    let do_blk s_node blk =
      let s_node = blk_foldl do_ins s_node blk in
      let jump_ins = get_jmp blk in
      match jump_ins with
      | JJmp il ->
         if (List.length il) = 0 then
           failwith "invalid input program";
         List.iter (fun id_blk -> let blk = get_blk fdesc id_blk in
                                  let fins = get_ins blk 0 in
                                  match fins with
                                  | IAssert (lexpr, cmp, rexpr) -> new_edge s_node (AGuard (LCmp (lexpr,cmp,rexpr))) id_blk
                                  | _ -> failwith "invalid input program"
                   )
                   il

      | JRet id ->
         end_node := s_node; ret := id; ()
    in

    (* function processing *)
    (*for i = 0 to initialnumber_of_nodes - 1 do
      do_blk i (get_blk fdesc i)
    done; *)
    fun_iteri do_blk fdesc;

    let edges = Array.make !next_node [] in
    for i = 0 to !next_node - 1 do
      edges.(i) <- Hashtbl.find_all h_edges i
    done;

    { fun_name = name;
      fun_vars = locs;
      fun_focus = focus;
      fun_body =
        { g_start = start_node;
          g_end = !end_node;
          g_edges = edges;
          g_position = Array.map (fun _ -> Utils.dummy_position) edges
        };
      fun_start_p = Utils.dummy_position;
      fun_end_p = Utils.dummy_position
    }

  (* graph of main function and all called function inside *)
  let graph_from_main () =
    (* init the querier *)
    init ();

    let h_funcs = Hashtbl.create 45 in

    let add_new_func fname fdesc =
      Hashtbl.replace h_funcs fname fdesc
    in

    let rec get_all_called_funcs fd =
      let do_f_ins ins =
        match ins with
        | ICall (_, id, _) ->
           let fdesc = get_func id in
           add_new_func id fdesc;
           get_all_called_funcs fdesc
        | _ -> ()
      in

      let do_f_blk blk =
        let n = get_nins blk in
        for i = 0 to n - 1 do
          do_f_ins (get_ins blk i)
        done
      in

      let n = get_nblk fd in
      for i = 0 to n - 1 do
        do_f_blk (get_blk fd i)
      done
    in

    (* get all function called from main *)
    let mainf = get_main () in
    get_all_called_funcs mainf;
    add_new_func "start" mainf;
    let g_prog = List.map graph_from_fundesc (Hashtbl.fold
                                                (
                                                  fun fn fb acc -> (fn, fb) :: acc
                                                )
                                                h_funcs [])
    in
    List.map (Graph.add_loop_counter "z") g_prog

end
