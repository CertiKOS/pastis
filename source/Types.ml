(* Quentin Carbonneaux - 2016 *)
(* Van Chan Ngo, 2016 *)

type id = string

type position =
  { pos_file: string
  ; pos_line: int
  ; pos_bol: int
  ; pos_char: int
  }

type expr =
  | ERandom
  | EVar of id
  | ENum of int
  | EAdd of expr * expr
  | ESub of expr * expr
  | EMul of expr * expr

(* Focus functions *)
type free_expr =
  | FBase of expr
  | FApply of id * free_expr list * position

type ('a, 'b) func_ =
  { fun_name: id
  ; fun_vars: id list
  ; fun_args: id list
  ; fun_rets: id list
  ; fun_focus: 'a list
  ; fun_body: 'b
  ; fun_start_p: position
  ; fun_end_p: position
  }

type ('a, 'b) program = id list * ('a, 'b) func_ list

type cmp = Le | Lt | Ge | Gt | Eq | Ne

type logic =
  | LTrue
  | LFalse
  | LRandom
  | LCmp of expr * cmp * expr
  | LAnd of logic * logic
  | LOr of logic * logic
  | LNot of logic
