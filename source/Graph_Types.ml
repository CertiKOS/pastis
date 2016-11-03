(* Quentin Carbonneaux - 2016 *)

(* Van Chan Ngo, 2016 *)

open Types

type node = int

type action =
  | AWeaken
  | AGuard of logic
  | AAssign of id * expr
  | ACall of id list * id * expr list
  | ASimpleCall of id

type graph =
  { g_start: node
  ; g_end: node
  ; g_edges: ((action * node) list) array
  ; g_position: position array
  }

type func = (Focus.focus, graph) func_
