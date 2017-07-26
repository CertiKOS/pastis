(* Sample code querying module
 * parses programs from the standard input
 *)

open Types
open Tools
open Compat

type fundesc = unit cfg_func
type blkdesc = block

let file = ref None

let getfg () =
  match !file with
  | None -> failwith "Cquery: module not initialized"
  | Some x -> x
let getf () = getfg () |> fst
let getg () = getfg () |> snd

let dummy_func body =
  { fname = ""
  ; fargs = []
  ; flocs = []
  ; fbody = body
  }

let init () =
  let (funcs, main) = Parse.ast_pa_file stdin in
  let funcs = List.map Cfg.of_func funcs in
  let main = (Cfg.of_func (dummy_func main)).fbody in
  let f = (funcs, main) in
  Parse.pp_cfg_file f;
  print_string "-----------------\n\n";
  let f = cfg_clean_file f in
  let g = cfg_file_globals f in
  let g = VSet.add (VNum 0) g in
  file := Some (f, g)

let get_glos () = getg ()
let get_main () = dummy_func (snd (getf ()))

let get_func fn =
  let (fdefs, _) = getf () in
  List.find (fun x -> x.fname = fn) fdefs

let get_args f = f.fargs
let get_locs f = f.flocs
let get_nblk f = Array.length f.fbody
let get_blk f n = f.fbody.(n)
let get_nins b = List.length b.binsts
let get_ins b n = List.nth b.binsts n
let get_jmp b = b.bjump
let get_preds b = b.bpreds
