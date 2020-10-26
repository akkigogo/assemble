%{
  open Instruction
%}

%token <int> INT
%token <string> ID
%token <int> REG

%token ADD ADDI AND J JR JAL OR SLT SLTI SUB SW LW BNE BEQ COLON X L R EOF

%start startexp
%type <Instruction.t> startexp

%%

startexp:
  | exp {E ($1)}
  | startexp exp {Elis ($1, $2)} 
  | error
    { failwith
        (Printf.sprintf "parse error near line:%d characters %d-%d"
           ((Parsing.symbol_start_pos ()).pos_lnum)
           ((Parsing.symbol_start_pos ()).Lexing.pos_cnum-(Parsing.symbol_start_pos ()).Lexing.pos_bol)
           ((Parsing.symbol_end_pos ()).Lexing.pos_cnum-(Parsing.symbol_start_pos ()).Lexing.pos_bol))}

exp:
  | ID COLON ins   { Label ($1, (Parsing.symbol_start_pos ()).pos_lnum, $3) } 
  | ins        { Exp ($1)}
  /* | EOF           { print_string "ok"; Eof () } */
;


ins:
  | rdRsRt REG X REG X REG  { RdRsRt ($1, $2, $4, $6) }
  | rtRsImm REG X REG X INT { RtRsImm ($1, $2, $4, $6) }
  | rsRtOffset REG X REG X ID { RsRtOffset ($1, $2, $4, $6, (Parsing.symbol_start_pos ()).pos_lnum) }
  | rtOffsetBase REG X INT L REG R { RtOffsetBase ($1, $2, $4, $6) }
  | imm26 ID { Imm26 ($1, $2) }
  | JR REG { Jr ($2)} 
  ;

rdRsRt:
  | ADD { `Add } | SUB { `Sub } | AND { `And } | OR { `Or } | SLT { `Slt }
;


rtRsImm:
  | ADDI { `Addi } | SLTI { `Slti } ;

rsRtOffset: | BEQ { `Beq } | BNE { `Bne } ;

rtOffsetBase: | LW { `Lw } | SW { `Sw } ;

imm26: | J { `J } | JAL { `Jal } ;