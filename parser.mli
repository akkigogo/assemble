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

val startexp :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Instruction.t
