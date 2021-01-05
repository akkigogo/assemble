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
*)
let h oc ins = 
  match ins with
  | RdRsRt (`Add, gp1, gp2, gp3) -> Printf.fprintf oc ("000000"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 0 5; Printf.fprintf oc ("100000\n");
  | RdRsRt (`Sub, gp1, gp2, gp3) -> Printf.fprintf oc ("000000"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 0 5; Printf.fprintf oc ("100010\n");
  | RdRsRt (`And, gp1, gp2, gp3) -> Printf.fprintf oc ("000000"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 0 5; Printf.fprintf oc ("100100\n");
  | RdRsRt (`Or, gp1, gp2, gp3) -> Printf.fprintf oc ("000000"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 0 5; Printf.fprintf oc ("100101\n");
  | RdRsRt (`Slt, gp1, gp2, gp3) -> Printf.fprintf oc ("000000"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 0 5; Printf.fprintf oc ("101010\n");
  | RdRsRt (`Fadd, gp1, gp2, gp3) -> Printf.fprintf oc ("010001"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 16 5; Printf.fprintf oc ("000000\n");
  | RdRsRt (`Fsub, gp1, gp2, gp3) -> Printf.fprintf oc ("010001"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 16 5; Printf.fprintf oc ("000001\n");
  | RdRsRt (`Fmul, gp1, gp2, gp3) -> Printf.fprintf oc ("010001"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 16 5; Printf.fprintf oc ("000010\n");
  | RdRsRt (`Fdiv, gp1, gp2, gp3) -> Printf.fprintf oc ("010001"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 16 5; Printf.fprintf oc ("000011\n");
  | RdRsRt (`Feq, gp1, gp2, gp3) -> Printf.fprintf oc ("010001"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 16 5; Printf.fprintf oc ("110010\n");
  | RdRsRt (`Flt, gp1, gp2, gp3) -> Printf.fprintf oc ("010001"); out_bit oc gp2 5; out_bit oc gp3 5; out_bit oc gp1 5; out_bit oc 16 5; Printf.fprintf oc ("111100\n");
  | RdRs (`Sqrt, gp1, gp2) -> Printf.fprintf oc ("010001"); out_bit oc gp2 5; out_bit oc 0 5; out_bit oc gp1 5; out_bit oc 16 5; Printf.fprintf oc ("000100\n");
  | RdRs (`Floor, gp1, gp2) -> Printf.fprintf oc ("010001"); out_bit oc gp2 5; out_bit oc 0 5; out_bit oc gp1 5; out_bit oc 16 5; Printf.fprintf oc ("000101\n");
  | RdRs (`Ftoi, gp1, gp2) -> Printf.fprintf oc ("010001"); out_bit oc gp2 5; out_bit oc 0 5; out_bit oc gp1 5; out_bit oc 16 5; Printf.fprintf oc ("000110\n");
  | RdRs (`Itof, gp1, gp2) -> Printf.fprintf oc ("010001"); out_bit oc gp2 5; out_bit oc 0 5; out_bit oc gp1 5; out_bit oc 16 5; Printf.fprintf oc ("000111\n");
  | RdRtshamt (`Sll, gp1, gp2, i) -> Printf.fprintf oc ("000000"); out_bit oc 0 5; out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 5; Printf.fprintf oc ("000000\n");
  | RdRtshamt (`Srl, gp1, gp2, i) -> Printf.fprintf oc ("000000"); out_bit oc 0 5; out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 5; Printf.fprintf oc ("000010\n");
  | RtRsImm (`Addi, gp1, gp2, i) -> Printf.fprintf oc ("001000"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");
  | RtRsImm (`Slti, gp1, gp2, i) -> Printf.fprintf oc ("001010"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");
  | RtRsImm (`Ori, gp1, gp2, i) -> Printf.fprintf oc ("001101"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");
  | RtRsImm (`Fori, gp1, gp2, i) -> Printf.fprintf oc ("011101"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");
  | RtImm (`Lui, gp1, i) -> Printf.fprintf oc ("001111"); out_bit oc 0 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n"); 
  | RtImm (`Flui, gp1, i) -> Printf.fprintf oc ("011111"); out_bit oc 0 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");
  | RtOffsetBase (`Lw, gp1, i, gp2) -> Printf.fprintf oc ("100011"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");
  | RtOffsetBase (`Sw, gp1, i, gp2) -> Printf.fprintf oc ("101011"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");  
  | RtOffsetBase (`Lwc, gp1, i, gp2) -> Printf.fprintf oc ("110001"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");
  | RtOffsetBase (`Swc, gp1, i, gp2) -> Printf.fprintf oc ("111001"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc i 16; Printf.fprintf oc ("\n");
  | RsRtOffset (`Beq, gp1, gp2, label, now_addr) -> 
    (try (Printf.fprintf oc ("000100"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc ((List.assoc label !label_list) - now_addr - 1) 16; Printf.fprintf oc ("\n");)
      with Not_found -> Printf.fprintf stdout "%s\n" label)
  | RsRtOffset (`Bne, gp1, gp2, label, now_addr) -> 
    (try (Printf.fprintf oc ("000101"); out_bit oc gp2 5; out_bit oc gp1 5; out_bit oc ((List.assoc label !label_list) - now_addr - 1) 16; Printf.fprintf oc ("\n");)
      with Not_found -> Printf.fprintf stdout "%s\n" label)
  | InOut (`Outc, gp1) -> Printf.fprintf oc ("111110"); out_bit oc 0 5; out_bit oc gp1 5; out_bit oc 0 5; out_bit oc 0 5; Printf.fprintf oc ("000000\n")
  | InOut (`Outi, gp1) -> Printf.fprintf oc ("111111"); out_bit oc 0 5; out_bit oc gp1 5; out_bit oc 0 5; out_bit oc 0 5; Printf.fprintf oc ("000000\n")
  | InOut (`Readi, gp1) -> Printf.fprintf oc ("111101"); out_bit oc 0 5; out_bit oc gp1 5; out_bit oc 0 5; out_bit oc 0 5; Printf.fprintf oc ("000000\n")
  | InOut (`Readf, gp1) -> Printf.fprintf oc ("111100"); out_bit oc 0 5; out_bit oc gp1 5; out_bit oc 0 5; out_bit oc 0 5; Printf.fprintf oc ("000000\n")
  | Jr (gp1) -> Printf.fprintf oc ("000000"); out_bit oc gp1 5; out_bit oc 0 5; out_bit oc 0 5; out_bit oc 0 5; Printf.fprintf oc ("001000\n")
  | Imm26 (`J, label) -> 
  (try (Printf.fprintf oc ("000010"); out_bit oc ((List.assoc label !label_list) - 1) 26; Printf.fprintf oc ("\n"))
    with Not_found -> Printf.fprintf stdout "%s\n" label)
  | Imm26 (`Jal, label) -> 
  (try (Printf.fprintf oc ("000011"); out_bit oc ((List.assoc label !label_list) - 1) 26; Printf.fprintf oc ("\n"))
    with Not_found -> Printf.fprintf stdout "%s\n" label)
  | _ -> Printf.fprintf stdout "invalid instruction\n"
  
(* ここからlabel消去のためだけに存在 *)
let rec delete_label l pc = match l with
  | Label id1 -> label_list := (id1, pc)::(!label_list)
  | Labellis (id1, lrest) -> label_list := (id1, pc)::(!label_list); delete_label lrest pc

let rec g' oc e = match e with
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
  let _ = (f' oc t') in
  let rec f_sub oc  t'' =
    match t'' with
    | Elis (t1, e1) ->  f_sub oc t1; g oc e1
    | E (e1) -> g oc e1
  in
  f_sub oc t'


