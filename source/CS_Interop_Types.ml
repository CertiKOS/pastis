(* Van Chan Ngo - 2017 *)

type csjump =
  | JJmp of int list (* list of successor blocks *)

type csinstruction =
  | ITick of int
  | IAssert of Types.logic (* the fist one is used for block guards *)
  | IAssign of Types.id * Types.expr
  | ICall of Types.id (* no return and arguments, use global variables instead *)

type csblock =
{
  bpreds : int list;
  binsts : csinstruction list;
  bjump : csjump
}

type 'a csfunc =
{
  fname : Types.id;
  flocs : Types.id list; (* local variables *)
  fbody : 'a
}

(* For example,
 * blkdesc = csblock
 * funcdesc = block array csfunc
 *)

module type CS_Querier = sig
(* Module signature for code querier.
 * This is the module type that has to be
 * implemented by CodeSurfer.
 *)

(* Conventions about block ids:
 *  - 0 is the id of the function start block
 *  - ids are a DFS numbering of the CFG
 *)

  type blkdesc
  type funcdesc

  val init:      unit -> unit

  (* Program queries. *)
  val get_glos:  unit -> Types.id list            (* global variable list *)
  val get_main:  unit -> funcdesc                 (* return the definition of the main function *)
  val get_func:  Types.id -> funcdesc             (* return the definition of the function named id *)

  (* Function queries. *)
  val get_locs:  funcdesc -> Types.id list        (* return the local variables *)
  val get_nblk:  funcdesc -> int                  (* return the # of blocks *)
  val get_blk:   funcdesc -> int -> blkdesc       (* return the definition of block with the provided id *)

  (* Block queries. *)
  val get_nins:  blkdesc -> int                   (* return # of instruction *)
  val get_ins:   blkdesc -> int -> csinstruction  (* return the instruction with the provided id, starting from 0 *) 
  val get_jmp:   blkdesc -> csjump                  (* return the list of successor blocks *)
  val get_preds: blkdesc -> int list              (* return the list of predecessor blocks *)

end
