/* Quentin Carbonneaux - 2016 */
/* Van Chan Ngo, 2016 */
%{
  open Types
  open IMP_Types

  let b startp b endp =
    { b_start_p = startp
    ; b_end_p = endp
    ; b_body = b
    }
%}

%token TVAR TTRUE TFALSE TRANDOM TSKIP TDO TRETURNS
%token TTHEN TNOT TAND TOR TFOCUS TSEMI TCOMMA
%token TRPAR TLEQ TLT TGEQ TGT TEQ TNE TADD TSUB TMUL
%token TEOF
%token <Types.position> TBREAK TASSUME TIF TELSE TWHILE TLOOP TLPAR TFUNC TEND TTHEN TDO TWEAK
%token <(Types.id * Types.position)> TIDENT
%token <int> TNUM

%left TOR
%left TAND
%nonassoc TNOT
%nonassoc TEQ TNE TGEQ TGT TLEQ TLT
%left TADD TSUB
%left TMUL

%type <Types.id list * (Types.free_expr, IMP_Types.block) Types.func_ list> file
%start file
%%

file: varopt rfuncs TEOF { ($1, List.rev $2) }

ident: TIDENT { fst $1 }

expr:
  | ident          { EVar $1 }
  | TNUM           { ENum $1 }
  | TSUB expr      { ESub (ENum 0, $2) }
  | expr TADD expr { EAdd ($1, $3) }
  | expr TSUB expr { ESub ($1, $3) }
  | expr TMUL expr { EMul ($1, $3) }
  | TLPAR expr TRPAR { $2 }

exprr:
  | TRANDOM { ERandom }
  | expr    { $1 }

logic:
    TTRUE            { LTrue }
  | TFALSE           { LFalse }
  | TRANDOM          { LRandom }
  | expr TLEQ expr   { LCmp ($1, Le, $3) }
  | expr TLT expr    { LCmp ($1, Lt, $3) }
  | expr TGEQ expr   { LCmp ($1, Ge, $3) }
  | expr TGT expr    { LCmp ($1, Gt, $3) }
  | expr TEQ expr    { LCmp ($1, Eq, $3) }
  | expr TNE expr    { LCmp ($1, Ne, $3) }
  | logic TAND logic { LAnd ($1, $3) }
  | logic TOR logic  { LOr ($1, $3) }
  | TNOT logic       { LNot $2 }
  | TLPAR logic TRPAR { $2 }

rexprrs1:
    exprr                 { [$1] }
  | rexprrs1 TCOMMA exprr { $3 :: $1 }

exprrs:
    /* empty */ { [] }
  | rexprrs1    { List.rev $1 }

rids1:
  ident              { [$1] }
  | rids1 TCOMMA ident { $3 :: $1 }

ids:
    /* empty */ { [] }
  | rids1       { List.rev $1 }

instr:
  | TBREAK TSEMI                           { IBreak, $1 }
  | TWEAK TSEMI                            { IWeaken, $1 }
  | TASSUME logic TSEMI                    { IAssume $2, $1 }
  | TIDENT TEQ exprr TSEMI                 { IAssign (fst $1, $3), snd $1 }
  | TIF logic TTHEN block TEND             { IIf ($2, b $3 $4 $5, b $5 [] $5), $1 }
  | TIF logic TTHEN block TELSE block TEND { IIf ($2, b $3 $4 $5, b $5 $6 $7), $1 }
  | TWHILE logic TDO block TEND            { IWhile ($2, b $3 $4 $5), $1 }
  | TLOOP block TEND                       { ILoop (b $1 $2 $3), $1 }
  | TLPAR ids TRPAR TEQ ident TLPAR exprrs TRPAR TSEMI  { ICall ($2, $5, $7), $1 }
  | ident TLPAR TRPAR TSEMI  {ISimpleCall $1, $2}



rinstrs1:
    instr          { [$1] }
  | rinstrs1 instr { $2 :: $1 }

block:
    /* empty */ { [] }
  | rinstrs1    { List.rev $1 }

rfrees:
    free               { [$1] }
  | rfrees TCOMMA free { $3 :: $1 }

frees:
    /* empty */ { [] }
  | rfrees      { List.rev $1 }

free:
    expr                     { FBase $1 }
  | TIDENT TLPAR frees TRPAR { FApply (fst $1, $3, snd $1) }
  | expr TGEQ expr           { FApply (">=", [FBase $1; FBase $3]
                                      , Utils.dummy_position) }

retopt:
    /* empty */              { [] }
  | TRETURNS TLPAR ids TRPAR { $3 }

varopt:
    /* empty */    { [] }
  | TVAR ids TSEMI { $2 }

focusopt:
    /* empty */        { [] }
  | TFOCUS frees TSEMI { $2 }

func:
  TFUNC ident TLPAR ids TRPAR
  retopt TDO varopt focusopt block TEND
  { { fun_name = $2; fun_vars = $8; fun_args = $4
    ; fun_rets = $6; fun_focus = $9
    ; fun_body = b $1 $10 $11
    ; fun_start_p = $1; fun_end_p = $11 }
  }

rfuncs:
   func        { [$1] }
  | rfuncs func { $2 :: $1 }
