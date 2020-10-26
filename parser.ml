type token =
  | INT of (int)
  | ID of (string)
  | REG of (int)
  | ADD
  | ADDI
  | AND
  | J
  | JR
  | JAL
  | OR
  | SLT
  | SLTI
  | SUB
  | SW
  | LW
  | BNE
  | BEQ
  | COLON
  | X
  | L
  | R
  | EOF

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
  open Instruction
# 30 "parser.ml"
let yytransl_const = [|
  260 (* ADD *);
  261 (* ADDI *);
  262 (* AND *);
  263 (* J *);
  264 (* JR *);
  265 (* JAL *);
  266 (* OR *);
  267 (* SLT *);
  268 (* SLTI *);
  269 (* SUB *);
  270 (* SW *);
  271 (* LW *);
  272 (* BNE *);
  273 (* BEQ *);
  274 (* COLON *);
  275 (* X *);
  276 (* L *);
  277 (* R *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* INT *);
  258 (* ID *);
  259 (* REG *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\002\000\002\000\003\000\003\000\003\000\
\003\000\003\000\003\000\004\000\004\000\004\000\004\000\004\000\
\005\000\005\000\006\000\006\000\007\000\007\000\008\000\008\000\
\000\000"

let yylen = "\002\000\
\001\000\002\000\001\000\003\000\001\000\006\000\006\000\006\000\
\007\000\002\000\002\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\002\000"

let yydefred = "\000\000\
\000\000\000\000\003\000\000\000\012\000\017\000\014\000\023\000\
\000\000\024\000\015\000\016\000\018\000\013\000\022\000\021\000\
\020\000\019\000\000\000\001\000\005\000\000\000\000\000\000\000\
\000\000\000\000\000\000\011\000\002\000\000\000\000\000\000\000\
\000\000\010\000\004\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\006\000\
\007\000\008\000\000\000\009\000"

let yydgoto = "\002\000\
\019\000\020\000\021\000\022\000\023\000\024\000\025\000\026\000"

let yysindex = "\002\000\
\000\255\000\000\000\000\239\254\000\000\000\000\000\000\000\000\
\045\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\016\255\000\000\000\000\046\255\047\255\048\255\
\049\255\017\255\030\255\000\000\000\000\034\255\035\255\036\255\
\037\255\000\000\000\000\054\255\055\255\056\255\059\255\042\255\
\043\255\044\255\050\255\061\255\064\255\065\255\063\255\000\000\
\000\000\000\000\051\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\068\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\050\000\044\000\000\000\000\000\000\000\000\000\000\000"

let yytablesize = 72
let yytable = "\003\000\
\027\000\004\000\001\000\005\000\006\000\007\000\008\000\009\000\
\010\000\011\000\012\000\013\000\014\000\015\000\016\000\017\000\
\018\000\004\000\034\000\005\000\006\000\007\000\008\000\009\000\
\010\000\011\000\012\000\013\000\014\000\015\000\016\000\017\000\
\018\000\005\000\006\000\007\000\008\000\009\000\010\000\011\000\
\012\000\013\000\014\000\015\000\016\000\017\000\018\000\028\000\
\030\000\031\000\032\000\033\000\036\000\037\000\038\000\039\000\
\040\000\041\000\042\000\043\000\044\000\045\000\046\000\048\000\
\049\000\051\000\050\000\025\000\029\000\047\000\035\000\052\000"

let yycheck = "\000\001\
\018\001\002\001\001\000\004\001\005\001\006\001\007\001\008\001\
\009\001\010\001\011\001\012\001\013\001\014\001\015\001\016\001\
\017\001\002\001\002\001\004\001\005\001\006\001\007\001\008\001\
\009\001\010\001\011\001\012\001\013\001\014\001\015\001\016\001\
\017\001\004\001\005\001\006\001\007\001\008\001\009\001\010\001\
\011\001\012\001\013\001\014\001\015\001\016\001\017\001\003\001\
\003\001\003\001\003\001\003\001\019\001\019\001\019\001\019\001\
\003\001\003\001\003\001\001\001\019\001\019\001\019\001\003\001\
\001\001\003\001\002\001\000\000\019\000\020\001\027\000\021\001"

let yynames_const = "\
  ADD\000\
  ADDI\000\
  AND\000\
  J\000\
  JR\000\
  JAL\000\
  OR\000\
  SLT\000\
  SLTI\000\
  SUB\000\
  SW\000\
  LW\000\
  BNE\000\
  BEQ\000\
  COLON\000\
  X\000\
  L\000\
  R\000\
  EOF\000\
  "

let yynames_block = "\
  INT\000\
  ID\000\
  REG\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 17 "parser.mly"
        (E (_1))
# 162 "parser.ml"
               : Instruction.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Instruction.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 18 "parser.mly"
                 (Elis (_1, _2))
# 170 "parser.ml"
               : Instruction.t))
; (fun __caml_parser_env ->
    Obj.repr(
# 20 "parser.mly"
    ( failwith
        (Printf.sprintf "parse error near line:%d characters %d-%d"
           ((Parsing.symbol_start_pos ()).pos_lnum)
           ((Parsing.symbol_start_pos ()).Lexing.pos_cnum-(Parsing.symbol_start_pos ()).Lexing.pos_bol)
           ((Parsing.symbol_end_pos ()).Lexing.pos_cnum-(Parsing.symbol_start_pos ()).Lexing.pos_bol)))
# 180 "parser.ml"
               : Instruction.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'ins) in
    Obj.repr(
# 27 "parser.mly"
                   ( Label (_1, (Parsing.symbol_start_pos ()).pos_lnum, _3) )
# 188 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'ins) in
    Obj.repr(
# 28 "parser.mly"
               ( Exp (_1))
# 195 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'rdRsRt) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 34 "parser.mly"
                            ( RdRsRt (_1, _2, _4, _6) )
# 205 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'rtRsImm) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 35 "parser.mly"
                            ( RtRsImm (_1, _2, _4, _6) )
# 215 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'rsRtOffset) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 36 "parser.mly"
                              ( RsRtOffset (_1, _2, _4, _6, (Parsing.symbol_start_pos ()).pos_lnum) )
# 225 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : 'rtOffsetBase) in
    let _2 = (Parsing.peek_val __caml_parser_env 5 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 37 "parser.mly"
                                   ( RtOffsetBase (_1, _2, _4, _6) )
# 235 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'imm26) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 38 "parser.mly"
             ( Imm26 (_1, _2) )
# 243 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 39 "parser.mly"
           ( Jr (_2))
# 250 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    Obj.repr(
# 43 "parser.mly"
        ( `Add )
# 256 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 43 "parser.mly"
                       ( `Sub )
# 262 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 43 "parser.mly"
                                      ( `And )
# 268 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 43 "parser.mly"
                                                    ( `Or )
# 274 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 43 "parser.mly"
                                                                  ( `Slt )
# 280 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 48 "parser.mly"
         ( `Addi )
# 286 "parser.ml"
               : 'rtRsImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 48 "parser.mly"
                          ( `Slti )
# 292 "parser.ml"
               : 'rtRsImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 50 "parser.mly"
                  ( `Beq )
# 298 "parser.ml"
               : 'rsRtOffset))
; (fun __caml_parser_env ->
    Obj.repr(
# 50 "parser.mly"
                                 ( `Bne )
# 304 "parser.ml"
               : 'rsRtOffset))
; (fun __caml_parser_env ->
    Obj.repr(
# 52 "parser.mly"
                   ( `Lw )
# 310 "parser.ml"
               : 'rtOffsetBase))
; (fun __caml_parser_env ->
    Obj.repr(
# 52 "parser.mly"
                                ( `Sw )
# 316 "parser.ml"
               : 'rtOffsetBase))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
           ( `J )
# 322 "parser.ml"
               : 'imm26))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
                        ( `Jal )
# 328 "parser.ml"
               : 'imm26))
(* Entry startexp *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let startexp (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Instruction.t)
