(* Quentin Carbonneaux - 2016-2017 *)
(* Van Chan Ngo - 2017 *)

open Types
include IMP_Types

let parse_file f =
  let lexbuf = Lexing.from_channel (open_in f) in
  IMP_Lexer.init lexbuf f;
  try
    let g, l = IMP_Grammar.file IMP_Lexer.lex lexbuf in
    g, List.map (fun f ->
      { f with fun_focus = List.map Focus.interpret f.fun_focus }) l
  with Parsing.Parse_error ->
    let startp = Lexing.lexeme_start_p lexbuf in
    Format.eprintf "%s:%i:%i: syntax error near '%s'@."
      startp.Lexing.pos_fname
      startp.Lexing.pos_lnum
      (startp.Lexing.pos_cnum - startp.Lexing.pos_bol + 1)
      (Lexing.lexeme lexbuf);
    raise Utils.Error


let parse_ic ic =
  let lexbuf = Lexing.from_channel ic in
  IMP_Lexer.init lexbuf "";
  try
    let g, l = IMP_Grammar.file IMP_Lexer.lex lexbuf in
    g, List.map (fun f ->
      { f with fun_focus = List.map Focus.interpret f.fun_focus }) l
  with Parsing.Parse_error ->
    let startp = Lexing.lexeme_start_p lexbuf in
    Format.eprintf "%s:%i:%i: syntax error near '%s'@."
      startp.Lexing.pos_fname
      startp.Lexing.pos_lnum
      (startp.Lexing.pos_cnum - startp.Lexing.pos_bol + 1)
      (Lexing.lexeme lexbuf);
    raise Utils.Error