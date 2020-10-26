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

val startexp :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Instruction.t
