open Types
open Focus_Types
open Graph_Types
open Presburger
open Polynom

(* todo: "dump" is probably not quite the right word, what should it be called? *)

let mkvarname funname x = "ID" ^ funname ^ "_" ^ x
let statevar s varname x = "(" ^ s ^ " " ^ varname x ^ ")"

(* Assumes that we have a state s in the context. *)
let rec dump_expr varname fmt  = function
  | ERandom ->
    Utils._TODO "coqgen random expressions"
  | EVar x ->
    Format.fprintf fmt "(EVar %s)" (varname x)
  | ENum n ->
    Format.fprintf fmt "(ENum %d)" n
  | EAdd (e1, e2) ->
     Format.fprintf fmt "(EAdd %a@ %a)"
       (dump_expr varname) e1
       (dump_expr varname) e2
  | ESub (e1, e2) ->
    Format.fprintf fmt "(ESub %a@ %a)"
      (dump_expr varname) e1
      (dump_expr varname) e2
  | EMul (e1, e2) ->
    Format.fprintf fmt "(EMul %a@ %a)"
      (dump_expr varname) e1
      (dump_expr varname) e2

(* Assumes that we have a state s in the context. *)
let rec dump_logic varname fmt = function
  | LTrue ->
    Format.fprintf fmt "True"
  | LFalse ->
    Format.fprintf fmt "False"
  | LRandom ->
    Utils._TODO "coqgen random logic"
  | LCmp (e1,cmp,e2) ->
    let cmp = match cmp with
      | Le -> "<="
      | Lt -> "<"
      | Ge -> ">="
      | Gt -> ">"
      | Eq -> "="
      | Ne -> "<>"
    in
    Format.fprintf fmt "((eval %a@ s) %s@ (eval %a@ s))%%Z"
      (dump_expr varname) e1
      cmp
      (dump_expr varname) e2
  | LAnd (l1,l2) ->
    Format.fprintf fmt "(%a@ /\\ %a)"
      (dump_logic varname) l1
      (dump_logic varname) l2
  | LOr (l1,l2) ->
    Format.fprintf fmt "(%a@ \\/ %a)"
      (dump_logic varname) l1
      (dump_logic varname) l2
  | LNot l ->
     Format.fprintf fmt "(~ %a)"
       (dump_logic varname) l

let dump_action varname fmt = function
  | ANone ->
    Format.fprintf fmt "ANone"
  | AWeaken ->
    Format.fprintf fmt "AWeaken"
  | AGuard a ->
    Format.fprintf fmt "(AGuard@ (fun s => %a))"
      (dump_logic varname) a
  | AAssign (x, e) ->
    Format.fprintf fmt "(AAssign@ %s@ %a)"
      (varname x)
      (dump_expr varname) e
  | ACall (xs,y,es) ->
    Utils._TODO "coqgen calls"

let dump_edges' varname fmt s es =
  List.iter (fun (a,s') ->
    Format.fprintf fmt "@[<hov>(%d,@,%a,@,%d)@]::@,"
      s (dump_action varname) a s'
  ) es

let dump_edges varname fmt es =
  Format.fprintf fmt "@[<hov>";
  Array.iteri (dump_edges' varname fmt) es;
  Format.fprintf fmt "nil";
  Format.fprintf fmt "@]"

let dump_func fmt i f =
  let varname = (mkvarname "func0") in
  Format.fprintf fmt
    "@[<v>Add LoadPath \"coq\".@,\
     Require Import List.@,\
     Require Import Arith.@,\
     Require Import ZArith.@,\
     Require Import QArith.@,\
     Require Import CFG.@,\
     Opaque Zplus.@,\
     Opaque Zminus.@,\
     Opaque Zmult.@,\
     Close Scope Q.@,@,";

  List.iteri (fun i x ->
    Format.fprintf fmt "Notation %s := %d.@," (varname x) i
  ) f.fun_vars;

  Format.fprintf fmt
    "Definition func%d : graph := {|@   @[<v>\
         g_start := %d;@,\
         g_end := %d;@,\
         g_edges := %a\
       @]@,|}.@,"
    i f.fun_body.g_start f.fun_body.g_end
    (dump_edges varname) f.fun_body.g_edges;

  Format.fprintf fmt "@]"

let dump_ai_bounds print_bound fmt bounds =
  (* TODO: print the correct function name *)
  Format.fprintf fmt "@[<v>";
  Format.fprintf fmt "@,Definition func0_bounds (p : node) (s : state) := @,";
  Format.fprintf fmt "  match p with@,";
  let varname = statevar "s" (mkvarname "func0") in
  let print_bound = print_bound varname in
  Format.fprintf fmt "    @[<v>";
  Array.iteri (fun i v ->
    Format.fprintf fmt "| %d => (%a)%%Z@," i print_bound v
  ) bounds;
  Format.fprintf fmt "| _ => False@]@,  end.@,";
  Format.fprintf fmt
    "Theorem func0_bounds_corrects:@   \
     forall s p' s', steps (g_start func0) s func0 p' s' -> \
     func0_bounds p' s'.@,\
     Proof. prove_ai_bounds_correct. Qed.@,";
  Format.fprintf fmt "@]"

let eps = 1e-4

let int_of_flt x =
  let c = ceil x and f = floor x in
  let dc = c -. x and df = x -. f in
  let check_ratios d1 d2 y =
    if (abs_float d1 >= eps || abs_float d2 >= eps)
    && d1 /. eps >= d2 then
      Printf.eprintf "Coq Generation: Warning trying \
                      to convert %g to an integer!\n" x;
    int_of_float y;
  in
  if dc < df
  then (check_ratios dc df c)
  else (check_ratios df dc f)

let rat_of_flt x =
  let sign, x = if x < 0. then -1, -. x else +1, +. x in
  let intp = floor x in
  let x = x -. intp in
  let farey n x =
    let rec go (a, b) (c, d) =
      if b > n then
        (c, d)
      else if d > n then
        (a, b)
      else
        let mediant =
          float_of_int (a+c) /.
          float_of_int (b+d) in
        if abs_float (x -. mediant) < eps then
          if b + d <= n then
            (a+c, b+d)
          else if d > b then
            (c, d)
          else
            (a, b)
        else if x > mediant then
          go (a+c, b+d) (c, d)
        else
          go (a, b) (a+c, b+d)
    in
    go (0, 1) (1, 1)
  in
  let (n, d) = farey 200 x in
  (sign * (n + int_of_float intp * d), d)

let rec dump_poly ring varname fmt pol =
  let print_coeff =
    match ring with
    | `Q -> begin fun fmt c ->
        let n, d = rat_of_flt c in
        Format.fprintf fmt "(%d # %d)" n d
      end
    | `Z -> begin fun fmt c ->
        Format.fprintf fmt "%d" (int_of_flt c)
      end
  in
  Format.fprintf fmt "@[<hov>";
  let is_zero = Poly.fold begin fun monom k first ->
      let pref, flt =
        if k < 0.
        then "-", (-. k)
        else (if first then "" else "+"), k
      in
      if Monom.is_one monom then
        Format.fprintf fmt
          (if first then "%s%a" else "@ %s %a")
          pref print_coeff k
      else if abs_float (flt -. 1.) < eps then
        Format.fprintf fmt
          (if first then "%s%a" else "@ %s %a")
          pref (dump_monom ring varname) monom
      else
        Format.fprintf fmt
          (if first then "%s@[<h>%a * %a@]" else "@ %s @[<h>%a * %a@]")
          pref print_coeff k (dump_monom ring varname) monom;
        false
    end pol true in
  if is_zero then Format.fprintf fmt "0";
  Format.fprintf fmt "@]"

and dump_monom ring varname fmt m =
  Format.fprintf fmt "@[<h>";
  let is_one = Monom.fold begin fun f e first ->
      if e = 0 then first else begin
      if e = 1 then
        Format.fprintf fmt
          (if first then "%a" else "@ %a")
          (dump_factor ring varname) f
      else
        Format.fprintf fmt
          (if first then "%a^%d" else "@ %a^%d")
          (dump_factor ring varname) f e;
        false
      end
    end m true in
  if is_one then Format.fprintf fmt "1";
  Format.fprintf fmt "@]"

and dump_factor ring varname fmt = function
  | Factor.Var v ->
    Format.fprintf fmt
      (match ring with `Q -> "inject_Z %s" | `Z -> "%s")
      (varname v)
  | Factor.Max p ->
    Format.fprintf fmt "max0(%a)"
      (dump_poly `Z varname) p

let dump_annot fmt annot =
  (* TODO: print the correct function name *)
  Format.fprintf fmt "@[<v>@,Definition func0_annots (p : node) (s : state) := @,";
  Format.fprintf fmt "  match p with@,";
  let varname = statevar "s" (mkvarname "func0") in
  Format.fprintf fmt "    @[<v>";
  Array.iteri (fun i v ->
    Format.fprintf fmt "| %d => (%a)%%Q@," i (dump_poly `Q varname) v
  ) annot;
  Format.fprintf fmt "| _ => (0 # 1)%%Q@]@,  end.@,";
  Format.fprintf fmt "@]";
  ()

let dump_hints fmt fannot =

  let varname = statevar "s" (mkvarname "func0") in
  let rec dump_ast fmt =
    let print s = Format.fprintf fmt s in
    let poly = dump_poly `Z varname in
    function
    | F_one -> print "F_one"
    | F_check_ge (a, b) ->
      print "rf_check_ge (%a) (%a)" poly a poly b
    | F_max0_pre_decrement (a, b) ->
      print "rf_max0_pre_decrement (%a) (%a)" poly a poly b
    | F_max0_pre_increment (a, b) ->
      print "rf_max0_pre_increment (%a) (%a)" poly a poly b
    | F_max0_ge_0 a ->
      print "rf_max0_ge_0 (%a)" poly a
    | F_max0_ge_arg a ->
      print "rf_max0_ge_arg (%a)" poly a
    | F_max0_le_arg f ->
      print "rf_max0_le_arg (%a)" dump_ast f
    | F_max0_monotonic f ->
      print "rf_max0_monotonic (%a)" dump_ast f
    | F_max0_sublinear f ->
      print "rf_max0_sublinear (%a)" dump_ast f
    | F_binom_monotonic (k, f, g) ->
      print "rf_binom_monotonic %d (%a) (%a)" k dump_ast f dump_ast g
    | F_product (f, g) ->
      print "rf_product (%a) (%a)" dump_ast f dump_ast g
  in
  let dump_hint fmt ((ka, kb), f) =
    Format.fprintf fmt "@[<h>(*%g %g*) %a@]" ka kb dump_ast f.ast
  in

  Format.fprintf fmt "@[<v>@,Definition func0_hints (p : node) (s : state) := @,";
  Format.fprintf fmt "  match p with@,";
  Format.fprintf fmt "    @[<v>";
  Array.iteri (fun i l ->
    List.filter (fun ((ka, kb), _) -> abs_float (ka -. kb) > fsmall) l |>
    Format.fprintf fmt "| %d => %a@,"
      i (Print.list dump_hint)
  ) fannot;
  Format.fprintf fmt "| _ => []@]@,  end.@,";
  Format.fprintf fmt "@]";
  ()

let dump fstart fs print_bound ai_bounds annot fannot =
  let oc = open_out "generated_coq.v" in
  let fmt = Format.formatter_of_out_channel oc in
  List.iteri (dump_func fmt) fs;
  let bounds = Hashtbl.find ai_bounds fstart in
  dump_ai_bounds print_bound fmt bounds;
  dump_annot fmt annot;
  dump_hints fmt fannot;
  Format.fprintf fmt "@.";
  close_out oc
