type token =
  | INT of (int)
  | ID of (string)
  | REG of (int)
  | ADD
  | ADDI
  | AND
  | SLL
  | SRL
  | J
  | JR
  | JAL
  | OR
  | SLT
  | SLTI
  | SUB
  | SW
  | LW
  | LUI
  | ORI
  | BNE
  | BEQ
  | FADD
  | FSUB
  | FMUL
  | FDIV
  | FEQ
  | FLT
  | SWC
  | LWC
  | SQRT
  | FLOOR
  | FTOI
  | ITOF
  | FLUI
  | FORI
  | OUTC
  | OUTI
  | READI
  | READF
  | COLON
  | X
  | L
  | R
  | EOF

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
  open Instruction
# 52 "parser.ml"
let yytransl_const = [|
  260 (* ADD *);
  261 (* ADDI *);
  262 (* AND *);
  263 (* SLL *);
  264 (* SRL *);
  265 (* J *);
  266 (* JR *);
  267 (* JAL *);
  268 (* OR *);
  269 (* SLT *);
  270 (* SLTI *);
  271 (* SUB *);
  272 (* SW *);
  273 (* LW *);
  274 (* LUI *);
  275 (* ORI *);
  276 (* BNE *);
  277 (* BEQ *);
  278 (* FADD *);
  279 (* FSUB *);
  280 (* FMUL *);
  281 (* FDIV *);
  282 (* FEQ *);
  283 (* FLT *);
  284 (* SWC *);
  285 (* LWC *);
  286 (* SQRT *);
  287 (* FLOOR *);
  288 (* FTOI *);
  289 (* ITOF *);
  290 (* FLUI *);
  291 (* FORI *);
  292 (* OUTC *);
  293 (* OUTI *);
  294 (* READI *);
  295 (* READF *);
  296 (* COLON *);
  297 (* X *);
  298 (* L *);
  299 (* R *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* INT *);
  258 (* ID *);
  259 (* REG *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\002\000\002\000\003\000\003\000\004\000\
\004\000\004\000\004\000\004\000\004\000\004\000\004\000\004\000\
\004\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\007\000\007\000\006\000\006\000\
\006\000\006\000\008\000\008\000\008\000\008\000\009\000\009\000\
\010\000\010\000\011\000\011\000\011\000\011\000\012\000\012\000\
\012\000\012\000\013\000\013\000\000\000"

let yylen = "\002\000\
\001\000\002\000\001\000\002\000\001\000\002\000\003\000\006\000\
\004\000\006\000\006\000\004\000\006\000\007\000\002\000\002\000\
\002\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\003\000\000\000\018\000\035\000\020\000\029\000\
\030\000\051\000\000\000\052\000\021\000\022\000\036\000\019\000\
\044\000\043\000\039\000\037\000\042\000\041\000\023\000\024\000\
\025\000\026\000\027\000\028\000\046\000\045\000\031\000\032\000\
\033\000\034\000\040\000\038\000\047\000\048\000\049\000\050\000\
\000\000\001\000\000\000\005\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\017\000\002\000\
\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\015\000\016\000\007\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\009\000\000\000\000\000\012\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\008\000\010\000\
\011\000\013\000\000\000\014\000"

let yydgoto = "\002\000\
\041\000\042\000\043\000\044\000\045\000\046\000\047\000\048\000\
\049\000\050\000\051\000\052\000\053\000"

let yysindex = "\002\000\
\000\255\000\000\000\000\217\254\000\000\000\000\000\000\000\000\
\000\000\000\000\147\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\038\255\000\000\074\255\000\000\148\255\149\255\150\255\151\255\
\152\255\153\255\154\255\155\255\039\255\157\255\000\000\000\000\
\000\000\119\255\120\255\121\255\122\255\123\255\124\255\125\255\
\000\000\000\000\000\000\164\255\165\255\166\255\167\255\170\255\
\169\255\172\255\133\255\000\000\134\255\135\255\000\000\136\255\
\137\255\175\255\179\255\180\255\181\255\182\255\000\000\000\000\
\000\000\000\000\139\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\184\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\110\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\145\000\133\000\146\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000"

let yytablesize = 189
let yytable = "\003\000\
\054\000\004\000\001\000\005\000\006\000\007\000\008\000\009\000\
\010\000\011\000\012\000\013\000\014\000\015\000\016\000\017\000\
\018\000\019\000\020\000\021\000\022\000\023\000\024\000\025\000\
\026\000\027\000\028\000\029\000\030\000\031\000\032\000\033\000\
\034\000\035\000\036\000\037\000\038\000\039\000\040\000\004\000\
\066\000\005\000\006\000\007\000\008\000\009\000\010\000\011\000\
\012\000\013\000\014\000\015\000\016\000\017\000\018\000\019\000\
\020\000\021\000\022\000\023\000\024\000\025\000\026\000\027\000\
\028\000\029\000\030\000\031\000\032\000\033\000\034\000\035\000\
\036\000\037\000\038\000\039\000\040\000\005\000\006\000\007\000\
\008\000\009\000\010\000\011\000\012\000\013\000\014\000\015\000\
\016\000\017\000\018\000\019\000\020\000\021\000\022\000\023\000\
\024\000\025\000\026\000\027\000\028\000\029\000\030\000\031\000\
\032\000\033\000\034\000\035\000\036\000\037\000\038\000\039\000\
\040\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\055\000\058\000\059\000\
\060\000\061\000\062\000\063\000\064\000\065\000\004\000\068\000\
\069\000\070\000\071\000\072\000\073\000\074\000\075\000\076\000\
\077\000\078\000\079\000\080\000\081\000\082\000\083\000\084\000\
\085\000\087\000\086\000\088\000\089\000\092\000\090\000\053\000\
\091\000\056\000\067\000\000\000\057\000"

let yycheck = "\000\001\
\040\001\002\001\001\000\004\001\005\001\006\001\007\001\008\001\
\009\001\010\001\011\001\012\001\013\001\014\001\015\001\016\001\
\017\001\018\001\019\001\020\001\021\001\022\001\023\001\024\001\
\025\001\026\001\027\001\028\001\029\001\030\001\031\001\032\001\
\033\001\034\001\035\001\036\001\037\001\038\001\039\001\002\001\
\002\001\004\001\005\001\006\001\007\001\008\001\009\001\010\001\
\011\001\012\001\013\001\014\001\015\001\016\001\017\001\018\001\
\019\001\020\001\021\001\022\001\023\001\024\001\025\001\026\001\
\027\001\028\001\029\001\030\001\031\001\032\001\033\001\034\001\
\035\001\036\001\037\001\038\001\039\001\004\001\005\001\006\001\
\007\001\008\001\009\001\010\001\011\001\012\001\013\001\014\001\
\015\001\016\001\017\001\018\001\019\001\020\001\021\001\022\001\
\023\001\024\001\025\001\026\001\027\001\028\001\029\001\030\001\
\031\001\032\001\033\001\034\001\035\001\036\001\037\001\038\001\
\039\001\004\001\005\001\006\001\007\001\008\001\009\001\010\001\
\011\001\012\001\013\001\014\001\015\001\016\001\017\001\018\001\
\019\001\020\001\021\001\022\001\023\001\024\001\025\001\026\001\
\027\001\028\001\029\001\030\001\031\001\032\001\033\001\034\001\
\035\001\036\001\037\001\038\001\039\001\003\001\003\001\003\001\
\003\001\003\001\003\001\003\001\003\001\003\001\002\001\041\001\
\041\001\041\001\041\001\041\001\041\001\041\001\003\001\003\001\
\003\001\003\001\001\001\003\001\001\001\041\001\041\001\041\001\
\041\001\003\001\042\001\001\001\001\001\043\001\002\001\000\000\
\003\001\041\000\054\000\255\255\043\000"

let yynames_const = "\
  ADD\000\
  ADDI\000\
  AND\000\
  SLL\000\
  SRL\000\
  J\000\
  JR\000\
  JAL\000\
  OR\000\
  SLT\000\
  SLTI\000\
  SUB\000\
  SW\000\
  LW\000\
  LUI\000\
  ORI\000\
  BNE\000\
  BEQ\000\
  FADD\000\
  FSUB\000\
  FMUL\000\
  FDIV\000\
  FEQ\000\
  FLT\000\
  SWC\000\
  LWC\000\
  SQRT\000\
  FLOOR\000\
  FTOI\000\
  ITOF\000\
  FLUI\000\
  FORI\000\
  OUTC\000\
  OUTI\000\
  READI\000\
  READF\000\
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
# 19 "parser.mly"
        (E (_1))
# 281 "parser.ml"
               : Instruction.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Instruction.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 20 "parser.mly"
                 (Elis (_1, _2))
# 289 "parser.ml"
               : Instruction.t))
; (fun __caml_parser_env ->
    Obj.repr(
# 22 "parser.mly"
    ( failwith
        (Printf.sprintf "parse error near line:%d characters %d-%d"
           ((Parsing.symbol_start_pos ()).pos_lnum)
           ((Parsing.symbol_start_pos ()).Lexing.pos_cnum-(Parsing.symbol_start_pos ()).Lexing.pos_bol)
           ((Parsing.symbol_end_pos ()).Lexing.pos_cnum-(Parsing.symbol_start_pos ()).Lexing.pos_bol)))
# 299 "parser.ml"
               : Instruction.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'labellis) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'ins) in
    Obj.repr(
# 30 "parser.mly"
                 ( Labelandins (_1, (Parsing.symbol_start_pos ()).pos_lnum, _2) )
# 307 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'ins) in
    Obj.repr(
# 31 "parser.mly"
               ( Exp (_1))
# 314 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 36 "parser.mly"
             ( Label (_1))
# 321 "parser.ml"
               : 'labellis))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'labellis) in
    Obj.repr(
# 37 "parser.mly"
                      ( Labellis (_1, _3))
# 329 "parser.ml"
               : 'labellis))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'rdRsRt) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 40 "parser.mly"
                            ( RdRsRt (_1, _2, _4, _6) )
# 339 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'rdRs) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 41 "parser.mly"
                   ( RdRs (_1, _2, _4) )
# 348 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'rdRtshamt) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 42 "parser.mly"
                              ( RdRtshamt (_1, _2, _4, _6) )
# 358 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'rtRsImm) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 43 "parser.mly"
                            ( RtRsImm (_1, _2, _4, _6) )
# 368 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'rtImm) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 44 "parser.mly"
                    ( RtImm (_1, _2, _4) )
# 377 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'rsRtOffset) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 46 "parser.mly"
                              ( RsRtOffset (_1, _2, _4, _6, (Parsing.symbol_start_pos ()).pos_lnum) )
# 387 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : 'rtOffsetBase) in
    let _2 = (Parsing.peek_val __caml_parser_env 5 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 47 "parser.mly"
                                   ( RtOffsetBase (_1, _2, _4, _6) )
# 397 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'inout) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 48 "parser.mly"
              ( InOut (_1, _2))
# 405 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'imm26) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 49 "parser.mly"
             ( Imm26 (_1, _2) )
# 413 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 50 "parser.mly"
           ( Jr (_2))
# 420 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
        ( `Add )
# 426 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
                       ( `Sub )
# 432 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
                                      ( `And )
# 438 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
                                                    ( `Or )
# 444 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
                                                                  ( `Slt )
# 450 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
         ( `Fadd )
# 456 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
                          ( `Fsub )
# 462 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
                                           ( `Fmul )
# 468 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
                                                            ( `Fdiv )
# 474 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
                                                                            ( `Feq )
# 480 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
                                                                                           ( `Flt )
# 486 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 58 "parser.mly"
        ( `Sll )
# 492 "parser.ml"
               : 'rdRtshamt))
; (fun __caml_parser_env ->
    Obj.repr(
# 58 "parser.mly"
                       ( `Srl )
# 498 "parser.ml"
               : 'rdRtshamt))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "parser.mly"
         ( `Sqrt )
# 504 "parser.ml"
               : 'rdRs))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "parser.mly"
                           ( `Floor )
# 510 "parser.ml"
               : 'rdRs))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "parser.mly"
                                             ( `Ftoi )
# 516 "parser.ml"
               : 'rdRs))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "parser.mly"
                                                              ( `Itof )
# 522 "parser.ml"
               : 'rdRs))
; (fun __caml_parser_env ->
    Obj.repr(
# 64 "parser.mly"
         ( `Addi )
# 528 "parser.ml"
               : 'rtRsImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 64 "parser.mly"
                          ( `Slti )
# 534 "parser.ml"
               : 'rtRsImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 64 "parser.mly"
                                          ( `Ori )
# 540 "parser.ml"
               : 'rtRsImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 64 "parser.mly"
                                                          ( `Fori )
# 546 "parser.ml"
               : 'rtRsImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 67 "parser.mly"
        ( `Lui )
# 552 "parser.ml"
               : 'rtImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 67 "parser.mly"
                        ( `Flui )
# 558 "parser.ml"
               : 'rtImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 72 "parser.mly"
                  ( `Beq )
# 564 "parser.ml"
               : 'rsRtOffset))
; (fun __caml_parser_env ->
    Obj.repr(
# 72 "parser.mly"
                                 ( `Bne )
# 570 "parser.ml"
               : 'rsRtOffset))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
                   ( `Lw )
# 576 "parser.ml"
               : 'rtOffsetBase))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
                                ( `Sw )
# 582 "parser.ml"
               : 'rtOffsetBase))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
                                              ( `Lwc )
# 588 "parser.ml"
               : 'rtOffsetBase))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
                                                             ( `Swc )
# 594 "parser.ml"
               : 'rtOffsetBase))
; (fun __caml_parser_env ->
    Obj.repr(
# 76 "parser.mly"
              ( `Outc )
# 600 "parser.ml"
               : 'inout))
; (fun __caml_parser_env ->
    Obj.repr(
# 76 "parser.mly"
                               ( `Outi )
# 606 "parser.ml"
               : 'inout))
; (fun __caml_parser_env ->
    Obj.repr(
# 76 "parser.mly"
                                                 ( `Readi )
# 612 "parser.ml"
               : 'inout))
; (fun __caml_parser_env ->
    Obj.repr(
# 76 "parser.mly"
                                                                    ( `Readf )
# 618 "parser.ml"
               : 'inout))
; (fun __caml_parser_env ->
    Obj.repr(
# 78 "parser.mly"
           ( `J )
# 624 "parser.ml"
               : 'imm26))
; (fun __caml_parser_env ->
    Obj.repr(
# 78 "parser.mly"
                        ( `Jal )
# 630 "parser.ml"
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
