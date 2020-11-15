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

val startexp :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Instruction.t
