open  Instruction

let label_list = ref []

let rec pow a n = 
  if n = 0 then 1
  else a * (pow a (n - 1))

let rec out_bit_plus oc n keta =
  if keta = 0 then () else (out_bit_plus oc (n / 2) (keta - 1); Printf.fprintf oc ("%d") (n mod 2))

let rec out_bit oc n keta =
  if n < 0 
  then out_bit_plus oc (n + (pow 2 keta)) keta
  else out_bit_plus oc n keta

 (* 機械語は op,rs,rt,rd,shamt,funct *)
(* 
浮動小数点命令は  rt  rs  rd
*)
let h oc ins = match ins with
  | RdRsRt (`Add, gp1, gp2, gp3) -> Printf.fprintf oc ("000000"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 0 5; Printf.fprintf oc ("100000\n");
  | RdRsRt (`Sub, gp1, gp2, gp3) -> Printf.fprintf oc ("000000"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 0 5; Printf.fprintf oc ("100010\n");
  | RdRsRt (`And, gp1, gp2, gp3) -> Printf.fprintf oc ("000000"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 0 5; Printf.fprintf oc ("100100\n");
  | RdRsRt (`Or, gp1, gp2, gp3) -> Printf.fprintf oc ("000000"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 0 5; Printf.fprintf oc ("100101\n");
  | RdRsRt (`Slt, gp1, gp2, gp3) -> Printf.fprintf oc ("000000"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 0 5; Printf.fprintf oc ("101010\n");
  | RdRsRt (`Fadd, gp1, gp2, gp3) -> Printf.fprintf oc ("010001"); out_bit oc 16 5; out_bit oc gp3 5; out_bit oc gp2 5; out_bit oc gp1 5; Printf.fprintf oc ("000000\n");
  | RdRsRt (`Fsub, gp1, gp2, gp3) -> Printf.fprintf oc ("010001"); out_bit oc 16 5; out_bit oc gp3 5; out_bit oc gp2 5; out_bit oc gp1 5; Printf.fprintf oc ("000001\n");
  | RdRsRt (`Fmul, gp1, gp2, gp3) -> Printf.fprintf oc ("010001"); out_bit oc 16 5; out_bit oc gp3 5; out_bit oc gp2 5; out_bit oc gp1 5; Printf.fprintf oc ("000010\n");
  | RdRsRt (`Fdiv, gp1, gp2, gp3) -> Printf.fprintf oc ("010001"); out_bit oc 16 5; out_bit oc gp3 5; out_bit oc gp2 5; out_bit oc gp1 5; Printf.fprintf oc ("000011\n");
  | RdRsRt (`Feq, gp1, gp2, gp3) -> Printf.fprintf oc ("010001"); out_bit oc 16 5; out_bit oc gp3 5; out_bit oc gp2 5; out_bit oc gp1 5; Printf.fprintf oc ("110010\n");
  | RdRsRt (`Flt, gp1, gp2, gp3) -> Printf.fprintf oc ("010001"); out_bit oc 16 5; out_bit oc gp3 5; out_bit oc gp2 5; out_bit oc gp1 5; Printf.fprintf oc ("111110\n");
  | RtRs (`Sqrt, gp1, gp2) -> Printf.fprintf oc ("010001"); out_bit oc 16 5; out_bit oc gp1 5; out_bit oc gp2 5; out_bit oc 0 5; Printf.fprintf oc ("000100\n");
  | RtRs (`Floor, gp1, gp2) -> Printf.fprintf oc ("010001"); out_bit oc 16 5; out_bit oc gp1 5; out_bit oc gp2 5; out_bit oc 0 5; Printf.fprintf oc ("000101\n");
  | RtRs (`Ftoi, gp1, gp2) -> Printf.fprintf oc ("010001"); out_bit oc 16 5; out_bit oc gp1 5; out_bit oc gp2 5; out_bit oc 0 5; Printf.fprintf oc ("000110\n");
  | RtRs (`Itof, gp1, gp2) -> Printf.fprintf oc ("010001"); out_bit oc 16 5; out_bit oc gp1 5; out_bit oc gp2 5; out_bit oc 0 5; Printf.fprintf oc ("000111\n");
  | RtRs (`Mtc, gp1, gp2) -> Printf.fprintf oc ("010001"); out_bit oc 4 5; out_bit oc gp1 5; out_bit oc gp2 5; out_bit oc 0 5; Printf.fprintf oc ("000000\n");
  | RtRsImm (`Addi, gp1, gp2, i) -> Printf.fprintf oc ("001000"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");
  | RtRsImm (`Slti, gp1, gp2, i) -> Printf.fprintf oc ("001010"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");
  | RtRsImm (`Ori, gp1, gp2, i) -> Printf.fprintf oc ("001101"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");
  | RtImm (`Lui, gp1, i) -> Printf.fprintf oc ("001111"); out_bit oc 0 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n"); 
  | LoadLabel (`Lahi, gp1, label, i) -> Printf.fprintf oc ("001111"); out_bit oc 0 5; out_bit oc gp1 5; out_bit oc (((List.assoc label !label_list) - 1) / (pow 2 16)) 16; Printf.fprintf oc ("\n");    (* 擬似命令 実際にはlabel上16ビットをlui *) 
  | LoadLabel (`Lalo, gp1, label, i) -> Printf.fprintf oc ("001101"); out_bit oc gp1 5; out_bit oc gp1 5; out_bit oc (((List.assoc label !label_list) - 1) mod (pow 2 16)) 16; Printf.fprintf oc ("\n");  (* 擬似命令 実際にはlabel下16ビットをori *)
  | RtOffsetBase (`Lw, gp1, i, gp2) -> Printf.fprintf oc ("100011"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");
  | RtOffsetBase (`Sw, gp1, i, gp2) -> Printf.fprintf oc ("101011"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");  
  | RtOffsetBase (`Lwc, gp1, i, gp2) -> Printf.fprintf oc ("110001"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");
  | RtOffsetBase (`Swc, gp1, i, gp2) -> Printf.fprintf oc ("111001"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");
  | RsRtOffset (`Beq, gp1, gp2, label, now_addr) -> Printf.fprintf oc ("000100"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc ((List.assoc label !label_list) - now_addr - 1) 16; Printf.fprintf oc ("\n");
  | RsRtOffset (`Bne, gp1, gp2, label, now_addr) -> Printf.fprintf oc ("000101"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc ((List.assoc label !label_list) - now_addr - 1) 16; Printf.fprintf oc ("\n");
  | Jr (gp1) -> Printf.fprintf oc ("000000"); out_bit oc gp1 5; out_bit oc 0 5; out_bit oc 0 5; out_bit oc 0 5; Printf.fprintf oc ("001000\n")
  | Imm26 (`J, label) -> Printf.fprintf oc ("000010"); out_bit oc ((List.assoc label !label_list) - 1) 26; Printf.fprintf oc ("\n")
  | Imm26 (`Jal, label) -> Printf.fprintf oc ("000011"); out_bit oc ((List.assoc label !label_list) - 1) 26; Printf.fprintf oc ("\n")

(* ここからlabel消去のためだけに存在 *)
let rec delete_label l pc = match l with
  | Label id1 -> label_list := (id1, pc)::(!label_list)
  | Labellis (id1, lrest) -> label_list := (id1, pc)::(!label_list); delete_label lrest pc

let rec g' oc e = match e with
  (* | Label (l1, pc1, ins1) -> label_list := (l1, pc1)::(!label_list); Label (l1, pc1, ins1)メモしておく *)
  | Labelandins (l1, pc1, ins1) -> delete_label l1 pc1; Labelandins (l1, pc1, ins1)
  | Exp (ins1) -> Exp (ins1)
  
let rec f' oc t =
  match t with
  | Elis (t1, e1) ->  Elis(f' oc t1, g' oc e1)
  | E (e1) -> E(g' oc e1)
(* ここまでlabel消去のためだけに存在 *)

let rec g oc e = match e with
  | Labelandins (l1, pc1, ins1) -> h oc ins1(* メモしておく*)
  | Exp (ins1) -> h oc ins1
  
let rec f oc t' =
  let t = (f' oc t') in
  match t with
  | Elis (t1, e1) ->  f oc t1; g oc e1
  | E (e1) -> g oc e1


