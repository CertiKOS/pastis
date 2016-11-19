(* Van Chan Ngo, 2016
 * Lexical scope and alpha renaming 
 *)

(* 
 * Alpha renaming after parsing, then 
 * generate a new source code file. 
 *)

open Types
open IMP_Types

let idpostfix = ref (-1)


(* new identifier generation *)
let newid fname varname =
  idpostfix := !idpostfix + 1; 
  varname ^ "_" ^ fname ^ "_" ^ (string_of_int (!idpostfix))


(* scope hierarchy: it maps function f to a set of functions which are outer scopes of f *)

(* check a variable is marking *)

(* rename function f if it has marks variables *) 
let renname (lv : Types.id list) (f : (Types.free_expr, IMP_Types.block) Types.func_) =
  f

