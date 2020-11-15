{
  open Parser
  open String

}

let digit = ['0' - '9']
let alpha = ['a' - 'z' 'A' - 'Z']
let symbol = '.' | '_' | '-'
let init = alpha | '.' | '_'
let id = init (digit | alpha | symbol)*
let sp = [' ' '\t' ]

rule token = parse
  | ":\n"         { COLON }
  | '\n'          { Lexing.new_line lexbuf; token lexbuf}
  | sp+            {token lexbuf}
  | "add"           { ADD }
  | "and"           { AND }
  | "jr"             { JR }
  | "or"             { OR }
  | "slt"           { SLT }
  | "sub"           { SUB }
  | "addi"             { ADDI }
  | "beq"               { BEQ }
  | "bne"               { BNE }
  | "j"                   { J }
  | "jal"               { JAL }
  | "lw"                 { LW }
  | "slti"             { SLTI }
  | "sw"                 { SW }
  | "lui"             { LUI }
  | "ori"             { ORI }
  | "lahi"            { LAHI }
  | "lalo"            { LALO }
  | "mtc1"            { MTC }
  | "add.s"           { FADD }
  | "sub.s"           { FSUB } 
  | "mul.s"           { FMUL }
  | "div.s"           { FDIV }
  | "swc1"            { SWC }
  | "lwc1"            { LWC }
  | "c.eq.s"          { FEQ }
  | "c.lt.s"          { FLT }
  | "sqrt"            { SQRT }
  | "floor"           { FLOOR }
  | "ftoi"            { FTOI }
  | "itof"            { ITOF }
  |  ","                { X }
  |  "("                { L }
  |  ")"                { R }
  | id as s                   { ID s }
  | digit+ as d               { INT (int_of_string d) }
  | '-' digit+ as d         { INT (int_of_string d) }
  | "$zero"               { REG 0 }
  | "$at"                 { REG 1 }
  | "$v0"                 { REG 2 }
  | "$v1"                 { REG 3 }
  | "$a0"                 { REG 4 }
  | "$a1"                 { REG 5 }
  | "$a2"                 { REG 6 }
  | "$a3"                 { REG 7 }
  | "$t0"                 { REG 8 }
  | "$t1"                 { REG 9 }
  | "$t2"                 { REG 10 }
  | "$t3"                 { REG 11 }
  | "$t4"                 { REG 12 }
  | "$t5"                 { REG 13 }
  | "$t6"                 { REG 14 }
  | "$t7"                 { REG 15 }
  | "$s0"                 { REG 16 }
  | "$s1"                 { REG 17 }
  | "$s2"                 { REG 18 }
  | "$s3"                 { REG 19 }
  | "$s4"                 { REG 20 }
  | "$s5"                 { REG 21 }
  | "$s6"                 { REG 22 }
  | "$s7"                 { REG 23 }
  | "$t8"                 { REG 24 }
  | "$t9"                 { REG 25 }
  | "$k0"                 { REG 26 }
  | "$k1"                 { REG 27 }
  | "$gp"                 { REG 28 }
  | "$sp"                 { REG 29 }
  | "$fp"                 { REG 30 }
  | "$ra"                 { REG 31 }
  | "$f0"                 { REG 0 }
  | "$f1"                 { REG 1 }
  | "$f2"                 { REG 2 }
  | "$f3"                 { REG 3 }
  | "$f4"                 { REG 4 }
  | "$f5"                 { REG 5 }
  | "$f6"                 { REG 6 }
  | "$f7"                 { REG 7 }
  | "$f8"                 { REG 8 }
  | "$f9"                 { REG 9 }
  | "$f10"                 { REG 10 }
  | "$f11"                 { REG 11 }
  | "$f12"                 { REG 12 }
  | "$f13"                 { REG 13 }
  | "$f14"                 { REG 14 }
  | "$f15"                 { REG 15 }
  | "$f16"                 { REG 16 }
  | "$f17"                 { REG 17 }
  | "$f18"                 { REG 18 }
  | "$f19"                 { REG 19 }
  | "$f20"                 { REG 20 }
  | "$f21"                 { REG 21 }
  | "$f22"                 { REG 22 }
  | "$f23"                 { REG 23 }
  | "$f24"                 { REG 24 }
  | "$f25"                 { REG 25 }
  | "$f26"                 { REG 26 }
  | "$f27"                 { REG 27 }
  | "$f28"                 { REG 28 }
  | "$f29"                 { REG 29 }
  | "$f30"                 { REG 30 }
  | "$fzero"                 { REG 31 }
  |  eof               { EOF }
  | _
    { failwith
        (Printf.sprintf "unknown token %s near line: %d"
           (Lexing.lexeme lexbuf)
           lexbuf.lex_curr_p.pos_lnum)
          }
