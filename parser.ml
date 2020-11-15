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
  | LUI
  | ORI
  | BNE
  | BEQ
  | LAHI
  | LALO
  | MTC
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
  | COLON
  | X
  | L
  | R
  | EOF

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
  open Instruction
# 47 "parser.ml"
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
  272 (* LUI *);
  273 (* ORI *);
  274 (* BNE *);
  275 (* BEQ *);
  276 (* LAHI *);
  277 (* LALO *);
  278 (* MTC *);
  279 (* FADD *);
  280 (* FSUB *);
  281 (* FMUL *);
  282 (* FDIV *);
  283 (* FEQ *);
  284 (* FLT *);
  285 (* SWC *);
  286 (* LWC *);
  287 (* SQRT *);
  288 (* FLOOR *);
  289 (* FTOI *);
  290 (* ITOF *);
  291 (* COLON *);
  292 (* X *);
  293 (* L *);
  294 (* R *);
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
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\006\000\006\000\006\000\006\000\006\000\
\007\000\007\000\007\000\008\000\009\000\009\000\010\000\010\000\
\011\000\011\000\011\000\011\000\012\000\012\000\000\000"

let yylen = "\002\000\
\001\000\002\000\001\000\002\000\001\000\002\000\003\000\006\000\
\004\000\006\000\004\000\004\000\006\000\007\000\002\000\002\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\003\000\000\000\017\000\033\000\019\000\045\000\
\000\000\046\000\020\000\021\000\034\000\018\000\042\000\041\000\
\036\000\035\000\040\000\039\000\037\000\038\000\028\000\022\000\
\023\000\024\000\025\000\026\000\027\000\044\000\043\000\029\000\
\030\000\031\000\032\000\000\000\001\000\000\000\005\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\016\000\002\000\004\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\015\000\007\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\009\000\000\000\011\000\012\000\
\000\000\000\000\000\000\000\000\000\000\000\000\008\000\010\000\
\013\000\000\000\014\000"

let yydgoto = "\002\000\
\036\000\037\000\038\000\039\000\040\000\041\000\042\000\043\000\
\044\000\045\000\046\000\047\000"

let yysindex = "\002\000\
\000\255\000\000\000\000\222\254\000\000\000\000\000\000\000\000\
\127\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\033\255\000\000\064\255\000\000\128\255\
\129\255\130\255\131\255\132\255\133\255\134\255\034\255\136\255\
\000\000\000\000\000\000\103\255\104\255\105\255\106\255\107\255\
\108\255\109\255\000\000\000\000\143\255\144\255\145\255\148\255\
\149\255\147\255\151\255\117\255\000\000\118\255\000\000\000\000\
\119\255\120\255\153\255\157\255\158\255\156\255\000\000\000\000\
\000\000\123\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\162\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\095\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\127\000\116\000\128\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000"

let yytablesize = 166
let yytable = "\003\000\
\048\000\004\000\001\000\005\000\006\000\007\000\008\000\009\000\
\010\000\011\000\012\000\013\000\014\000\015\000\016\000\017\000\
\018\000\019\000\020\000\021\000\022\000\023\000\024\000\025\000\
\026\000\027\000\028\000\029\000\030\000\031\000\032\000\033\000\
\034\000\035\000\004\000\059\000\005\000\006\000\007\000\008\000\
\009\000\010\000\011\000\012\000\013\000\014\000\015\000\016\000\
\017\000\018\000\019\000\020\000\021\000\022\000\023\000\024\000\
\025\000\026\000\027\000\028\000\029\000\030\000\031\000\032\000\
\033\000\034\000\035\000\005\000\006\000\007\000\008\000\009\000\
\010\000\011\000\012\000\013\000\014\000\015\000\016\000\017\000\
\018\000\019\000\020\000\021\000\022\000\023\000\024\000\025\000\
\026\000\027\000\028\000\029\000\030\000\031\000\032\000\033\000\
\034\000\035\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\049\000\052\000\053\000\054\000\055\000\056\000\057\000\
\058\000\004\000\061\000\062\000\063\000\064\000\065\000\066\000\
\067\000\068\000\069\000\070\000\071\000\073\000\072\000\074\000\
\075\000\076\000\077\000\079\000\078\000\080\000\082\000\081\000\
\083\000\047\000\050\000\060\000\000\000\051\000"

let yycheck = "\000\001\
\035\001\002\001\001\000\004\001\005\001\006\001\007\001\008\001\
\009\001\010\001\011\001\012\001\013\001\014\001\015\001\016\001\
\017\001\018\001\019\001\020\001\021\001\022\001\023\001\024\001\
\025\001\026\001\027\001\028\001\029\001\030\001\031\001\032\001\
\033\001\034\001\002\001\002\001\004\001\005\001\006\001\007\001\
\008\001\009\001\010\001\011\001\012\001\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\029\001\030\001\031\001\
\032\001\033\001\034\001\004\001\005\001\006\001\007\001\008\001\
\009\001\010\001\011\001\012\001\013\001\014\001\015\001\016\001\
\017\001\018\001\019\001\020\001\021\001\022\001\023\001\024\001\
\025\001\026\001\027\001\028\001\029\001\030\001\031\001\032\001\
\033\001\034\001\004\001\005\001\006\001\007\001\008\001\009\001\
\010\001\011\001\012\001\013\001\014\001\015\001\016\001\017\001\
\018\001\019\001\020\001\021\001\022\001\023\001\024\001\025\001\
\026\001\027\001\028\001\029\001\030\001\031\001\032\001\033\001\
\034\001\003\001\003\001\003\001\003\001\003\001\003\001\003\001\
\003\001\002\001\036\001\036\001\036\001\036\001\036\001\036\001\
\036\001\003\001\003\001\003\001\001\001\003\001\002\001\001\001\
\036\001\036\001\036\001\003\001\037\001\001\001\003\001\002\001\
\038\001\000\000\036\000\048\000\255\255\038\000"

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
  LUI\000\
  ORI\000\
  BNE\000\
  BEQ\000\
  LAHI\000\
  LALO\000\
  MTC\000\
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
# 18 "parser.mly"
        (E (_1))
# 255 "parser.ml"
               : Instruction.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Instruction.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 19 "parser.mly"
                 (Elis (_1, _2))
# 263 "parser.ml"
               : Instruction.t))
; (fun __caml_parser_env ->
    Obj.repr(
# 21 "parser.mly"
    ( failwith
        (Printf.sprintf "parse error near line:%d characters %d-%d"
           ((Parsing.symbol_start_pos ()).pos_lnum)
           ((Parsing.symbol_start_pos ()).Lexing.pos_cnum-(Parsing.symbol_start_pos ()).Lexing.pos_bol)
           ((Parsing.symbol_end_pos ()).Lexing.pos_cnum-(Parsing.symbol_start_pos ()).Lexing.pos_bol)))
# 273 "parser.ml"
               : Instruction.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'labellis) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'ins) in
    Obj.repr(
# 29 "parser.mly"
                 ( Labelandins (_1, (Parsing.symbol_start_pos ()).pos_lnum, _2) )
# 281 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'ins) in
    Obj.repr(
# 30 "parser.mly"
               ( Exp (_1))
# 288 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 35 "parser.mly"
             ( Label (_1))
# 295 "parser.ml"
               : 'labellis))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'labellis) in
    Obj.repr(
# 36 "parser.mly"
                      ( Labellis (_1, _3))
# 303 "parser.ml"
               : 'labellis))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'rdRsRt) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 39 "parser.mly"
                            ( RdRsRt (_1, _2, _4, _6) )
# 313 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'rtRs) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 40 "parser.mly"
                   ( RtRs (_1, _2, _4) )
# 322 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'rtRsImm) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 41 "parser.mly"
                            ( RtRsImm (_1, _2, _4, _6) )
# 332 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'rtImm) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 42 "parser.mly"
                    ( RtImm (_1, _2, _4) )
# 341 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'loadLabel) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 43 "parser.mly"
                       ( LoadLabel (_1, _2, _4, (Parsing.symbol_start_pos ()).pos_lnum) )
# 350 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'rsRtOffset) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 44 "parser.mly"
                              ( RsRtOffset (_1, _2, _4, _6, (Parsing.symbol_start_pos ()).pos_lnum) )
# 360 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : 'rtOffsetBase) in
    let _2 = (Parsing.peek_val __caml_parser_env 5 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 45 "parser.mly"
                                   ( RtOffsetBase (_1, _2, _4, _6) )
# 370 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'imm26) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 46 "parser.mly"
             ( Imm26 (_1, _2) )
# 378 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 47 "parser.mly"
           ( Jr (_2))
# 385 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    Obj.repr(
# 51 "parser.mly"
        ( `Add )
# 391 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 51 "parser.mly"
                       ( `Sub )
# 397 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 51 "parser.mly"
                                      ( `And )
# 403 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 51 "parser.mly"
                                                    ( `Or )
# 409 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 51 "parser.mly"
                                                                  ( `Slt )
# 415 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 52 "parser.mly"
         ( `Fadd )
# 421 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 52 "parser.mly"
                          ( `Fsub )
# 427 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 52 "parser.mly"
                                           ( `Fmul )
# 433 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 52 "parser.mly"
                                                            ( `Fdiv )
# 439 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 52 "parser.mly"
                                                                            ( `Feq )
# 445 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 52 "parser.mly"
                                                                                           ( `Flt )
# 451 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 56 "parser.mly"
        ( `Mtc )
# 457 "parser.ml"
               : 'rtRs))
; (fun __caml_parser_env ->
    Obj.repr(
# 56 "parser.mly"
                        ( `Sqrt )
# 463 "parser.ml"
               : 'rtRs))
; (fun __caml_parser_env ->
    Obj.repr(
# 56 "parser.mly"
                                          ( `Floor )
# 469 "parser.ml"
               : 'rtRs))
; (fun __caml_parser_env ->
    Obj.repr(
# 56 "parser.mly"
                                                            ( `Ftoi )
# 475 "parser.ml"
               : 'rtRs))
; (fun __caml_parser_env ->
    Obj.repr(
# 56 "parser.mly"
                                                                             ( `Itof )
# 481 "parser.ml"
               : 'rtRs))
; (fun __caml_parser_env ->
    Obj.repr(
# 59 "parser.mly"
         ( `Addi )
# 487 "parser.ml"
               : 'rtRsImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 59 "parser.mly"
                          ( `Slti )
# 493 "parser.ml"
               : 'rtRsImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 59 "parser.mly"
                                          ( `Ori )
# 499 "parser.ml"
               : 'rtRsImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 62 "parser.mly"
        ( `Lui )
# 505 "parser.ml"
               : 'rtImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 65 "parser.mly"
         ( `Lahi )
# 511 "parser.ml"
               : 'loadLabel))
; (fun __caml_parser_env ->
    Obj.repr(
# 65 "parser.mly"
                          ( `Lalo )
# 517 "parser.ml"
               : 'loadLabel))
; (fun __caml_parser_env ->
    Obj.repr(
# 67 "parser.mly"
                  ( `Beq )
# 523 "parser.ml"
               : 'rsRtOffset))
; (fun __caml_parser_env ->
    Obj.repr(
# 67 "parser.mly"
                                 ( `Bne )
# 529 "parser.ml"
               : 'rsRtOffset))
; (fun __caml_parser_env ->
    Obj.repr(
# 69 "parser.mly"
                   ( `Lw )
# 535 "parser.ml"
               : 'rtOffsetBase))
; (fun __caml_parser_env ->
    Obj.repr(
# 69 "parser.mly"
                                ( `Sw )
# 541 "parser.ml"
               : 'rtOffsetBase))
; (fun __caml_parser_env ->
    Obj.repr(
# 69 "parser.mly"
                                              ( `Lwc )
# 547 "parser.ml"
               : 'rtOffsetBase))
; (fun __caml_parser_env ->
    Obj.repr(
# 69 "parser.mly"
                                                             ( `Swc )
# 553 "parser.ml"
               : 'rtOffsetBase))
; (fun __caml_parser_env ->
    Obj.repr(
# 71 "parser.mly"
           ( `J )
# 559 "parser.ml"
               : 'imm26))
; (fun __caml_parser_env ->
    Obj.repr(
# 71 "parser.mly"
                        ( `Jal )
# 565 "parser.ml"
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
