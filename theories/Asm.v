From Kotori Require Import Util.
From Stdlib Require Import Sint63 Lia ZifyUint63.

Module Encode.
  Definition Bcond imm19 cond :=
    (84 << 24) lor (imm19 << 5) lor (cond).
  Definition B imm26 :=
    (5 << 26) lor (imm26).
  Definition BL imm26 :=
    (1 << 31) lor (5 << 26) lor (imm26).
  Definition ADR immlo immhi Rd :=
    (immlo << 29) lor (16 << 24) lor (immhi << 5) lor (Rd).
  Definition ADRP immlo immhi Rd :=
    (1 << 31) lor (immlo << 29) lor (16 << 24) lor (immhi << 5) lor (Rd).
  Definition MOVK sf hw imm16 Rd :=
    (sf << 31) lor (0xe5 << 23) lor (hw << 21) lor (imm16 << 5) lor (Rd).
  Definition MOVZ sf hw imm16 Rd :=
    (sf << 31) lor (0xa5 << 23) lor (hw << 21) lor (imm16 << 5) lor (Rd).
  Definition CBZ sf op imm19 Rt :=
    (sf << 31) lor (0x34 << 24) lor (op << 24) lor (imm19 << 5) lor (Rt).
  Definition TBZ b5 op b40 imm14 Rt :=
    (b5 << 31) lor (0x36 << 24) lor (op << 24) lor (b40 << 19) lor (imm14 << 5) lor (Rt).
  Definition UBFX sf N immr imms Rn Rd :=
    (sf << 31) lor (0xa6 << 23) lor (N << 22) lor (immr << 16) lor (imms << 10) lor (Rn << 5) lor (Rd).
  Definition LDR_r size Rm option S Rn Rt :=
    (size << 30) lor (0x1c3 << 21) lor (Rm << 16) lor (option << 13) lor (S << 12) lor (2 << 10) lor (Rn << 5) lor (Rt).
  Definition LDR_STR size opc imm9 pre(*aka bit11*) Rn Rt :=
    (size << 30) lor (0x38 << 24) lor (opc << 22) lor (imm9 << 12) lor (pre << 10) lor (Rn << 5) lor (Rt).
  Definition LDP_STP opc pre(*aka bit23*) L imm7 Rt2 Rn Rt :=
    (opc << 30) lor (0x51 << 23) lor (pre << 24) lor (L << 22) lor (imm7 << 15) lor (Rt2 << 10) lor (Rn << 5) lor (Rt).
  Definition EOR sf shift Rm imm6 Rn Rd :=
    (sf << 31) lor (0x4a << 24) lor (shift << 22) lor (Rm << 16) lor (imm6 << 10) lor (Rn << 5) lor (Rd).
End Encode.
Definition bounded x bw :=
  let bound := 1<<(bw-1) in
  if ((-bound <=? x) && (x <? bound))%sint63
  then Some (x land (1<<bw-1))
  else None.
Definition Bcond src dst cond :=
  bounded (dst - src) 19 <&> λ imm19, Encode.Bcond imm19 cond.
Definition B src dst :=
  bounded (dst - src) 26 <&> Encode.B.
Definition BL src dst :=
  bounded (dst - src) 26 <&> Encode.BL.
Definition CBZ sf op src dst Rt :=
  bounded (dst - src) 19 <&> λ imm19, Encode.CBZ sf op imm19 Rt.
Definition TBZ b5 op b40 src dst Rt :=
  bounded (dst - src) 14 <&> λ imm14, Encode.TBZ b5 op b40 imm14 Rt.
Definition ADR i imm Rd :=
  let dist := imm - i<<2 in
  bounded dist 21 <&> λ imm21, Encode.ADR (imm21:[0,2]) (imm21:[2,19]) Rd.
Definition ADRP i imm Rd :=
  let dist := asr imm 12 - i>>10 in
  bounded dist 21 <&> λ imm21, Encode.ADRP (imm21:[0,2]) (imm21:[2,19]) Rd.
Definition UDF := 0.
Definition NOP := 0xd503201f.
Definition UBFX is64 Rd Rn lsb width :=
  Encode.UBFX (b2i is64) (b2i is64) lsb (lsb+width-1) Rn Rd.
Definition LDR_r64 Xt Xn Xm :=
  Encode.LDR_r 3 Xm 3 1 Xn Xt.
Definition STP_pre64 Xt1 Xt2 Xn imm :=
  bounded (imm>>3) 7 <&> λ imm7, Encode.LDP_STP 2 1 0 imm7 Xt2 Xn Xt1.
Definition LDP_post64 Xt1 Xt2 Xn imm :=
  bounded (imm>>3) 7 <&> λ imm7, Encode.LDP_STP 2 0 1 imm7 Xt2 Xn Xt1.
Definition STR_pre64 Xt Xn imm :=
  bounded imm 9 <&> λ imm9, Encode.LDR_STR 3 0 imm9 3 Xn Xt.
Definition LDR_post64 Xt Xn imm :=
  bounded imm 9 <&> λ imm9, Encode.LDR_STR 3 1 imm9 1 Xn Xt.
Definition PUSH Xt1 := STR_pre64 Xt1 31 (-8) orelse 0.
Definition POP Xt1 := LDR_post64 Xt1 31 (8) orelse 0.
Definition PUSH2 Xt1 Xt2 := STP_pre64 Xt1 Xt2 31 (-0x10) orelse 0.
Definition POP2 Xt1 Xt2 := LDP_post64 Xt1 Xt2 31 (0x10) orelse 0.
Definition EOR_lsr Rd Rn Rm shift :=
  Encode.EOR 1 1 Rm shift Rn Rd.
