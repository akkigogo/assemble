(* let lis = ref [] *)

type pc = int
type label = string
type reg = int

type rdRsRt = [ `Add | `Sub | `And | `Or | `Slt ]
type rtRsImm = [ `Addi | `Slti ]
type rsRtOffset = [ `Beq | `Bne ]
type rtOffsetBase = [ `Lw | `Sw ]
type imm26 = [ `J | `Jal ]

type ins = 
  | RdRsRt of rdRsRt * reg * reg * reg
  | RtRsImm of rtRsImm * reg * reg * int
  | RtOffsetBase of rtOffsetBase * reg * int * reg
  | RsRtOffset of rsRtOffset * reg * reg * label * pc
  | Imm26 of imm26 * label
  | Jr of int

type exp = 
  | Label of label * pc * ins
  | Exp of ins
  | Eof of unit

type t = Elis of t * exp | E of exp

(* mainのprogram 以下編集用のタダのメモです*)
(* let rec f oc t = match t with
  | Elis (e1, t1) -> g oc e1; f oc t1
  | Elis (e1) -> g oc e1

let rec g oc e = match e with
  | Label (l1, pc1) -> Printf.fprintf oc ("label\n");(* メモしておく*)
  | Exp (ins1) -> h ins1


  
let h ins = match ins with
  | RdRsRt (Add, gp1, gp2, gp3) -> Printf.fprintf oc ("000000"); out_register oc gp1; out_register oc gp2; out_register oc gp3; Printf.fprintf oc ("0100000");
  | RdRsRt (Sub, gp1, gp2, gp3) -> Printf.fprintf oc ("000000"); out_register oc gp1; out_register oc gp2; out_register oc gp3; Printf.fprintf oc ("0100010");
  | _ -> () *)