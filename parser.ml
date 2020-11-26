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
# 53 "parser.ml"
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
  278 (* LAHI *);
  279 (* LALO *);
  280 (* MTC *);
  281 (* FADD *);
  282 (* FSUB *);
  283 (* FMUL *);
  284 (* FDIV *);
  285 (* FEQ *);
  286 (* FLT *);
  287 (* SWC *);
  288 (* LWC *);
  289 (* SQRT *);
  290 (* FLOOR *);
  291 (* FTOI *);
  292 (* ITOF *);
  293 (* OUTC *);
  294 (* OUTI *);
  295 (* READI *);
  296 (* READF *);
  297 (* COLON *);
  298 (* X *);
  299 (* L *);
  300 (* R *);
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
\004\000\004\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\007\000\007\000\006\000\
\006\000\006\000\006\000\006\000\008\000\008\000\008\000\009\000\
\010\000\010\000\011\000\011\000\012\000\012\000\012\000\012\000\
\013\000\013\000\013\000\013\000\014\000\014\000\000\000"

let yylen = "\002\000\
\001\000\002\000\001\000\002\000\001\000\002\000\003\000\006\000\
\004\000\006\000\006\000\004\000\004\000\006\000\007\000\002\000\
\002\000\002\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\003\000\000\000\019\000\037\000\021\000\030\000\
\031\000\053\000\000\000\054\000\022\000\023\000\038\000\020\000\
\046\000\045\000\040\000\039\000\044\000\043\000\041\000\042\000\
\032\000\024\000\025\000\026\000\027\000\028\000\029\000\048\000\
\047\000\033\000\034\000\035\000\036\000\049\000\050\000\051\000\
\052\000\000\000\001\000\000\000\005\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\018\000\002\000\004\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\016\000\017\000\007\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\009\000\
\000\000\000\000\012\000\013\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\008\000\010\000\011\000\014\000\000\000\
\015\000"

let yydgoto = "\002\000\
\042\000\043\000\044\000\045\000\046\000\047\000\048\000\049\000\
\050\000\051\000\052\000\053\000\054\000\055\000"

let yysindex = "\002\000\
\000\255\000\000\000\000\216\254\000\000\000\000\000\000\000\000\
\000\000\000\000\151\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\039\255\000\000\076\255\000\000\152\255\153\255\154\255\
\155\255\156\255\157\255\158\255\159\255\160\255\040\255\162\255\
\000\000\000\000\000\000\123\255\124\255\125\255\126\255\127\255\
\128\255\129\255\130\255\000\000\000\000\000\000\170\255\171\255\
\172\255\173\255\176\255\177\255\175\255\179\255\139\255\000\000\
\140\255\141\255\000\000\000\000\142\255\143\255\182\255\186\255\
\187\255\188\255\189\255\000\000\000\000\000\000\000\000\145\255\
\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\191\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\113\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000"

let yygindex = "\000\000\
\000\000\151\000\138\000\152\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000"

let yytablesize = 196
let yytable = "\003\000\
\056\000\004\000\001\000\005\000\006\000\007\000\008\000\009\000\
\010\000\011\000\012\000\013\000\014\000\015\000\016\000\017\000\
\018\000\019\000\020\000\021\000\022\000\023\000\024\000\025\000\
\026\000\027\000\028\000\029\000\030\000\031\000\032\000\033\000\
\034\000\035\000\036\000\037\000\038\000\039\000\040\000\041\000\
\004\000\069\000\005\000\006\000\007\000\008\000\009\000\010\000\
\011\000\012\000\013\000\014\000\015\000\016\000\017\000\018\000\
\019\000\020\000\021\000\022\000\023\000\024\000\025\000\026\000\
\027\000\028\000\029\000\030\000\031\000\032\000\033\000\034\000\
\035\000\036\000\037\000\038\000\039\000\040\000\041\000\005\000\
\006\000\007\000\008\000\009\000\010\000\011\000\012\000\013\000\
\014\000\015\000\016\000\017\000\018\000\019\000\020\000\021\000\
\022\000\023\000\024\000\025\000\026\000\027\000\028\000\029\000\
\030\000\031\000\032\000\033\000\034\000\035\000\036\000\037\000\
\038\000\039\000\040\000\041\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\057\000\060\000\061\000\062\000\063\000\064\000\065\000\
\066\000\067\000\068\000\004\000\071\000\072\000\073\000\074\000\
\075\000\076\000\077\000\078\000\079\000\080\000\081\000\082\000\
\083\000\085\000\084\000\086\000\087\000\088\000\089\000\090\000\
\092\000\091\000\093\000\094\000\097\000\095\000\055\000\096\000\
\058\000\070\000\000\000\059\000"

let yycheck = "\000\001\
\041\001\002\001\001\000\004\001\005\001\006\001\007\001\008\001\
\009\001\010\001\011\001\012\001\013\001\014\001\015\001\016\001\
\017\001\018\001\019\001\020\001\021\001\022\001\023\001\024\001\
\025\001\026\001\027\001\028\001\029\001\030\001\031\001\032\001\
\033\001\034\001\035\001\036\001\037\001\038\001\039\001\040\001\
\002\001\002\001\004\001\005\001\006\001\007\001\008\001\009\001\
\010\001\011\001\012\001\013\001\014\001\015\001\016\001\017\001\
\018\001\019\001\020\001\021\001\022\001\023\001\024\001\025\001\
\026\001\027\001\028\001\029\001\030\001\031\001\032\001\033\001\
\034\001\035\001\036\001\037\001\038\001\039\001\040\001\004\001\
\005\001\006\001\007\001\008\001\009\001\010\001\011\001\012\001\
\013\001\014\001\015\001\016\001\017\001\018\001\019\001\020\001\
\021\001\022\001\023\001\024\001\025\001\026\001\027\001\028\001\
\029\001\030\001\031\001\032\001\033\001\034\001\035\001\036\001\
\037\001\038\001\039\001\040\001\004\001\005\001\006\001\007\001\
\008\001\009\001\010\001\011\001\012\001\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\029\001\030\001\031\001\
\032\001\033\001\034\001\035\001\036\001\037\001\038\001\039\001\
\040\001\003\001\003\001\003\001\003\001\003\001\003\001\003\001\
\003\001\003\001\003\001\002\001\042\001\042\001\042\001\042\001\
\042\001\042\001\042\001\042\001\003\001\003\001\003\001\003\001\
\001\001\003\001\002\001\001\001\042\001\042\001\042\001\042\001\
\003\001\043\001\001\001\001\001\044\001\002\001\000\000\003\001\
\042\000\056\000\255\255\044\000"

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
# 289 "parser.ml"
               : Instruction.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Instruction.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 20 "parser.mly"
                 (Elis (_1, _2))
# 297 "parser.ml"
               : Instruction.t))
; (fun __caml_parser_env ->
    Obj.repr(
# 22 "parser.mly"
    ( failwith
        (Printf.sprintf "parse error near line:%d characters %d-%d"
           ((Parsing.symbol_start_pos ()).pos_lnum)
           ((Parsing.symbol_start_pos ()).Lexing.pos_cnum-(Parsing.symbol_start_pos ()).Lexing.pos_bol)
           ((Parsing.symbol_end_pos ()).Lexing.pos_cnum-(Parsing.symbol_start_pos ()).Lexing.pos_bol)))
# 307 "parser.ml"
               : Instruction.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'labellis) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'ins) in
    Obj.repr(
# 30 "parser.mly"
                 ( Labelandins (_1, (Parsing.symbol_start_pos ()).pos_lnum, _2) )
# 315 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'ins) in
    Obj.repr(
# 31 "parser.mly"
               ( Exp (_1))
# 322 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 36 "parser.mly"
             ( Label (_1))
# 329 "parser.ml"
               : 'labellis))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'labellis) in
    Obj.repr(
# 37 "parser.mly"
                      ( Labellis (_1, _3))
# 337 "parser.ml"
               : 'labellis))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'rdRsRt) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 40 "parser.mly"
                            ( RdRsRt (_1, _2, _4, _6) )
# 347 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'rdRs) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 41 "parser.mly"
                   ( RdRs (_1, _2, _4) )
# 356 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'rdRtshamt) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 42 "parser.mly"
                              ( RdRtshamt (_1, _2, _4, _6) )
# 366 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'rtRsImm) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 43 "parser.mly"
                            ( RtRsImm (_1, _2, _4, _6) )
# 376 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'rtImm) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 44 "parser.mly"
                    ( RtImm (_1, _2, _4) )
# 385 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'loadLabel) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 45 "parser.mly"
                       ( LoadLabel (_1, _2, _4, (Parsing.symbol_start_pos ()).pos_lnum) )
# 394 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'rsRtOffset) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 46 "parser.mly"
                              ( RsRtOffset (_1, _2, _4, _6, (Parsing.symbol_start_pos ()).pos_lnum) )
# 404 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : 'rtOffsetBase) in
    let _2 = (Parsing.peek_val __caml_parser_env 5 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 47 "parser.mly"
                                   ( RtOffsetBase (_1, _2, _4, _6) )
# 414 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'inout) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 48 "parser.mly"
              ( InOut (_1, _2))
# 422 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'imm26) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 49 "parser.mly"
             ( Imm26 (_1, _2) )
# 430 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 50 "parser.mly"
           ( Jr (_2))
# 437 "parser.ml"
               : 'ins))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
        ( `Add )
# 443 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
                       ( `Sub )
# 449 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
                                      ( `And )
# 455 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
                                                    ( `Or )
# 461 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
                                                                  ( `Slt )
# 467 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
         ( `Fadd )
# 473 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
                          ( `Fsub )
# 479 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
                                           ( `Fmul )
# 485 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
                                                            ( `Fdiv )
# 491 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
                                                                            ( `Feq )
# 497 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
                                                                                           ( `Flt )
# 503 "parser.ml"
               : 'rdRsRt))
; (fun __caml_parser_env ->
    Obj.repr(
# 58 "parser.mly"
        ( `Sll )
# 509 "parser.ml"
               : 'rdRtshamt))
; (fun __caml_parser_env ->
    Obj.repr(
# 58 "parser.mly"
                       ( `Srl )
# 515 "parser.ml"
               : 'rdRtshamt))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "parser.mly"
        ( `Mtc )
# 521 "parser.ml"
               : 'rdRs))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "parser.mly"
                        ( `Sqrt )
# 527 "parser.ml"
               : 'rdRs))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "parser.mly"
                                          ( `Floor )
# 533 "parser.ml"
               : 'rdRs))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "parser.mly"
                                                            ( `Ftoi )
# 539 "parser.ml"
               : 'rdRs))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "parser.mly"
                                                                             ( `Itof )
# 545 "parser.ml"
               : 'rdRs))
; (fun __caml_parser_env ->
    Obj.repr(
# 64 "parser.mly"
         ( `Addi )
# 551 "parser.ml"
               : 'rtRsImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 64 "parser.mly"
                          ( `Slti )
# 557 "parser.ml"
               : 'rtRsImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 64 "parser.mly"
                                          ( `Ori )
# 563 "parser.ml"
               : 'rtRsImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 67 "parser.mly"
        ( `Lui )
# 569 "parser.ml"
               : 'rtImm))
; (fun __caml_parser_env ->
    Obj.repr(
# 70 "parser.mly"
         ( `Lahi )
# 575 "parser.ml"
               : 'loadLabel))
; (fun __caml_parser_env ->
    Obj.repr(
# 70 "parser.mly"
                          ( `Lalo )
# 581 "parser.ml"
               : 'loadLabel))
; (fun __caml_parser_env ->
    Obj.repr(
# 72 "parser.mly"
                  ( `Beq )
# 587 "parser.ml"
               : 'rsRtOffset))
; (fun __caml_parser_env ->
    Obj.repr(
# 72 "parser.mly"
                                 ( `Bne )
# 593 "parser.ml"
               : 'rsRtOffset))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
                   ( `Lw )
# 599 "parser.ml"
               : 'rtOffsetBase))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
                                ( `Sw )
# 605 "parser.ml"
               : 'rtOffsetBase))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
                                              ( `Lwc )
# 611 "parser.ml"
               : 'rtOffsetBase))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
                                                             ( `Swc )
# 617 "parser.ml"
               : 'rtOffsetBase))
; (fun __caml_parser_env ->
    Obj.repr(
# 76 "parser.mly"
              ( `Outc )
# 623 "parser.ml"
               : 'inout))
; (fun __caml_parser_env ->
    Obj.repr(
# 76 "parser.mly"
                               ( `Outi )
# 629 "parser.ml"
               : 'inout))
; (fun __caml_parser_env ->
    Obj.repr(
# 76 "parser.mly"
                                                 ( `Readi )
# 635 "parser.ml"
               : 'inout))
; (fun __caml_parser_env ->
    Obj.repr(
# 76 "parser.mly"
                                                                    ( `Readf )
# 641 "parser.ml"
               : 'inout))
; (fun __caml_parser_env ->
    Obj.repr(
# 78 "parser.mly"
           ( `J )
# 647 "parser.ml"
               : 'imm26))
; (fun __caml_parser_env ->
    Obj.repr(
# 78 "parser.mly"
                        ( `Jal )
# 653 "parser.ml"
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
