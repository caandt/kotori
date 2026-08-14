(* minimal aarch64 decoder *)
Require Import Util.

Variant ityp :=
  | ignore
  | invalid
  | ADR (imm Rd: int)
  | ADRP (imm Rd: int)
  | Bcond (imm cond: int)
  | BR (Rn: int)
  | BLR (Rn: int)
  | RET (Rn: int)
  | B (imm: int)
  | BL (imm: int)
  | CBZ (sf op imm Rt: int)
  | TBZ (b5 op b40 imm Rt: int).

Definition dc_b_cond (n:int) :=
  let o0 := n:[4] in
  let o1 := n:[24] in
  if (o0 =? 0) && (o1 =? 0)
  then let imm := n:[5,19] in
       let cond := n:[0,4] in
       Bcond imm cond
  else ignore.
Definition dc_b_reg (n:int) :=
  let opc := n:[21,4] in
  let op2 := n:[16,5] in
  let op3 := n:[10,6] in
  let Rn := n:[5,5] in
  let op4 := n:[0,5] in
  if (op2 =? 31) then
    if (opc =? 0) then
      if (op3 =? 0) then
        if (op4 =? 0) then BR Rn
        else ignore
      else invalid
    else if (opc =? 1) then
      if (op3 =? 0) then
        if (op4 =? 0) then BLR Rn
        else ignore
      else invalid
    else if (opc =? 2) then
      if (op3 =? 0) then
        if (op4 =? 0) then RET Rn
        else ignore
      else invalid
    else invalid
  else ignore.
Definition dc_b_imm n :=
  let imm26 := n:[0,26] in
  let op := n:[31] in
  if (op =? 0)
  then B imm26
  else BL imm26.
Definition dc_cb n :=
  let sf := n:[31] in
  let op := n:[24] in
  let imm := n:[5,19] in
  let Rt := n:[0,5] in
  CBZ sf op imm Rt.
Definition dc_tb n :=
  let b5 := n:[31] in
  let op := n:[24] in
  let b40 := n:[19,5] in
  let imm := n:[5,14] in
  let Rt := n:[0,5] in
  TBZ b5 op b40 imm Rt.

Definition dc_b (n:int) :=
  let op0 := n:[29,3] in
  if (op0 =? 2) then
    if (n:[25] =? 0)
    then dc_b_cond n
    else ignore
  else if (op0 =? 6) then
    if (n:[25] =? 1)
    then dc_b_reg n
    else ignore
  else if (op0 =? 0) || (op0 =? 4) then
    dc_b_imm n
  else if (op0 =? 1) || (op0 =? 5) then
    if (n:[25] =? 0)
    then dc_cb n
    else dc_tb n
  else ignore.
Definition dc_pcr n :=
  let op := n:[31] in
  let immlo := n:[29,2] in
  let immhi := n:[5,19] in
  let Rd := n:[0,5] in
  let imm := immhi << 2 lor immlo in
  if (op =? 0)
  then ADR imm Rd
  else ADRP imm Rd.
Definition dc_dpi n :=
  let op0 := n:[23,3] in
  if (op0 =? 0) || (op0 =? 1)
  then dc_pcr n
  else ignore.
Definition decode n :=
  let op0 := n:[25,4] in
  if (op0 =? 10) || (op0 =? 11)
  then dc_b n
  else if (op0 =? 8) || (op0 =? 9)
       then dc_dpi n
       else ignore.
