type jump =
  | JJmp of int list
  | JRet of Types.id

type operation = OPlus | OMinus

type operand =
  | OpVar of Types.id
  | OpCon of int

type instruction =
  | ITick of int
  | IAssert of Types.expr * Types.cmp * Types.expr
  | IInc of Types.id * operation * operand
  | ISet of Types.id * operand option
  | ICall of Types.id option * Types.id * operand list

type csblock =
  {
    bpreds : int list;
    binsts : instruction list;
    bjump : jump
  }

type 'a csfunc =
  {
    fname : Types.id;
    fargs : Types.id list;
    flocs : Types.id list;
    fbody : 'a
  }

(*
   for example,
   blkdesc = csblock
   funcdesc = block array csfunc
 *)

module type CS_Querier = sig
  (* Module signature for code queriers.
   * This is the module type that has to be
   * implemented by CodeSurfer.
   *)

  (* Conventions about block ids:
   *  - 0 is the id of the function start block
   *  - ids are a DFS numbering of the CFG
   *)

  type fundesc
  type blkdesc

  val init:      unit -> unit

  (* Program queries. *)
  val get_glos:  unit -> Types.id list
  val get_main:  unit -> fundesc
  val get_func:  Types.id -> fundesc

  (* Function queries. *)
  val get_args:  fundesc -> Types.id list
  val get_locs:  fundesc -> Types.id list
  val get_nblk:  fundesc -> int
  val get_blk:   fundesc -> int -> blkdesc

  (* Block queries. *)
  val get_nins:  blkdesc -> int
  val get_ins:   blkdesc -> int -> instruction
  val get_jmp:   blkdesc -> jump
  val get_preds: blkdesc -> int list

end
