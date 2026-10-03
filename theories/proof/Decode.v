From Picinae Require Import armv8_lifter_rework.
From Picinae Require Import armv8.
From Picinae.simplifier Require Import base.
From Kotori Require Import Asm.
From Kotori Require Import proof.Util.
From Stdlib Require Import NArith.
From Stdlib Require Import Sint63 Lia ZifyUint63.
From Kotori Require Import proof.I2N.
Open Scope N_scope.
Import Lia.

(*when x is lower than the range you're looking for*)
Lemma xbits_decode : 
forall x a b c, (toN x) < 2^b ->
xbits ♮(a lor x)%sint63 b c = xbits ♮(a)%sint63 b c.
Proof.
intros. nify. rewrite xbits_lor. rewrite xbits_above with (n:= (toN x)).
rewrite N.lor_0_r. reflexivity. assumption.
Qed.

(*when a is above than the range you're looking for*)
Lemma xbits_decode1 : 
forall x a b c, (xbits ♮a b c) = 0 ->
xbits ♮(a lor x)%sint63 b c = xbits ♮(x)%sint63 b c.
Proof.
intros. nify. rewrite xbits_lor. rewrite H. reflexivity.
Qed.

Lemma bit_mask_decode1 :
    forall n k i y, i+k < y ->
    N.odd (xbits n (i+k) (N.succ (i+k))) = false
    -> (N.land (xbits n k y) (2 ^ (i)) =? 0)=true.
Proof.
intros. rewrite N.eqb_eq. 
apply N.bits_inj_0. intros.
rewrite N.land_spec. rewrite N.pow2_bits_eqb. 
destruct (i =? n0) eqn:E.
rewrite N.eqb_eq in E. 
rewrite <- E. 
rewrite xbits_spec. apply N.ltb_lt in H. rewrite H.
repeat rewrite andb_true_r. rewrite <- testbit_xbits in H0. assumption. 
apply andb_false_r.
Qed.

Lemma bit_mask_decode_pos :
    forall n k i y, i+k < y ->
    N.odd (xbits n (i+k) (N.succ (i+k))) = true
    -> (N.land (xbits n k y) (2 ^ (i)) =? 2^i)=true.
Proof.
intros. rewrite N.eqb_eq.
apply N.bits_inj. intro.
rewrite N.land_spec, N.pow2_bits_eqb.
destruct (i =? n0) eqn:E.
rewrite N.eqb_eq in E. subst. rewrite xbits_spec. apply N.ltb_lt in H. rewrite H.
repeat rewrite andb_true_r. rewrite <- testbit_xbits in H0. assumption.
apply andb_false_r.
Qed.

Lemma land_pow2_small : forall a k, a < 2 ^ k -> N.land a (2 ^ k) = 0.
Proof.
  intros a k Ha.
  apply N.bits_inj_0; intro m.
  rewrite N.land_spec, N.pow2_bits_eqb.
  destruct (N.eqb_spec k m) as [<- | _].
  - rewrite <- (N.mod_small a (2 ^ k) Ha).
    rewrite N.mod_pow2_bits_high; [reflexivity | apply N.le_refl].
  - apply andb_false_r.
Qed.

Local Ltac decode_hammer:=
repeat try first[
progress repeat rewrite xbits_lor |
progress repeat rewrite andb_false_l|
progress rewrite N.mod_small|
progress rewrite N.lor_0_l| 
progress rewrite N.lor_0_r| 
progress vm_compute (_-_)|
progress rewrite xbits_shiftl|
progress rewrite xbits_0_j|
progress rewrite N.shiftl_0_r|
progress rewrite N.shiftl_0_l|
progress rewrite I2N.inj_lsl|
progress rewrite I2N.inj_land|
reflexivity| 
progress psimpl |rewrite N.shiftl_mul_pow2;lia ]. 

Create HintDb decode_db.

#[local] Hint Rewrite
  xbits_lor andb_false_l
  N.lor_0_l N.lor_0_r
  xbits_shiftl xbits_0_j
  N.shiftl_0_r N.shiftl_0_l
  I2N.inj_lsl I2N.inj_land 
  : decode_db.

Local Ltac decode_hammer1 :=
  repeat try first [
    progress autorewrite with decode_db|
    progress vm_compute (_-_)|
    reflexivity|
    progress psimpl|
    rewrite N.shiftl_mul_pow2;lia
  ].

Lemma shiftr_bdes:
forall a b, a < 2^b*2->
(N.shiftr a b) = 0 \/ (N.shiftr a b )= 1.
Proof.
intros.
rewrite N.shiftr_div_pow2. apply N.div_lt_upper_bound in H.
lia. lia.
Qed.

Local Ltac simpl_sf H2:=
rewrite I2N.inj_lsl, N.shiftl_mul_pow2;
rewrite N.mod_small by lia; rewrite xbits_below; [reflexivity |
destruct H2; rewrite H2; reflexivity] .

Lemma decode_Bcond:
forall imm19 cond, 
(toN imm19) < 2^19 -> (toN cond < 2^4) -> 
arm_decode (toN (Encode.Bcond imm19 cond)) = ARM_B_COND (toN cond)(toN imm19).
Proof.
intros. unfold Encode.Bcond.
unfold arm_decode. repeat rewrite xbits_decode by lia. repeat vm_compute ( _ =? _). psimpl.
unfold branch_exc. repeat rewrite xbits_decode by lia. vm_compute (xbits _ 29 32). psimpl.  
rewrite bit_mask_decode1; [|lia|rewrite xbits_decode by lia; vm_compute; reflexivity ].

unfold cond_branch. 
repeat rewrite xbits_decode by lia. vm_compute (N.succ _); vm_compute (xbits _ 24 25); psimpl.
nify. decode_hammer.
Qed.

Lemma decode_B:
forall imm26 , 
(toN imm26) < 2^26 ->
arm_decode (toN (Encode.B imm26)) = ARM_B (toN imm26).
Proof.
intros. pose proof H as H'.
change (2^26) with (2^25*2) in H. apply shiftr_bdes in H.
unfold Encode.B. nify.
unfold arm_decode. rewrite xbits_lor. change (xbits (N.shiftl ♮5 ♮26 mod 2 ^ 63) 25 29) with 10.  
unfold xbits. change (29-25) with 4. rewrite N.mod_small. 
- destruct H; rewrite H. decode_hammer.
all: unfold branch_exc; decode_hammer. 
all: abstract ( unfold uncond_b_imm; decode_hammer).
- psimpl. lia.
Qed.


Lemma decode_ADR:
forall immlo immhi Rd,
(toN immhi < 2^19)->
(toN immlo < 2^2) ->
(toN Rd < 2^5)->
arm_decode(toN (Encode.ADR immlo immhi Rd)) = ARM_ADR_IMM.
Proof.
intros.
unfold Encode.ADR. unfold arm_decode. 
repeat rewrite xbits_decode by lia.
rewrite xbits_decode1.
change (xbits ♮(16 << 24)%sint63 25 29) with 8. psimpl.
unfold dp_imm. 
repeat rewrite xbits_decode by lia. nify.
rewrite xbits_lor. repeat rewrite <- I2N.inj_lsl.
rewrite <- I2N.inj_lor.
rewrite xbits_decode1. change (xbits ♮(16 << 24)%sint63 23 26) with 0. decode_hammer.
pose proof (shiftr_bdes ♮immhi 18 ltac:(lia)) as Hb.
destruct Hb; rewrite H2; psimpl. 
unfold pc_rel. repeat rewrite xbits_decode by lia. 
nify. decode_hammer. 
unfold pc_rel. repeat rewrite xbits_decode by lia. 
nify. decode_hammer.
all:
rewrite I2N.inj_lsl; 
rewrite N.mod_small by (rewrite N.shiftl_mul_pow2; lia); change ♮29 with 29.
all: psimpl; reflexivity.
Qed.

Lemma decode_ADRP:
forall immlo immhi Rd,
(toN immhi < 2^19)->
(toN immlo < 2^2) ->
(toN Rd < 2^5)->
arm_decode(toN (Encode.ADRP immlo immhi Rd)) = ARM_ADRP_IMM.
Proof.
intros.
unfold Encode.ADRP. unfold arm_decode. 
repeat rewrite xbits_decode by lia.
rewrite xbits_decode1.
change (xbits ♮(16 << 24)%sint63 25 29) with 8. psimpl.
change (1 << 31) with 2147483648%uint63.
unfold dp_imm.
repeat rewrite xbits_decode by lia. nify.
do 2 rewrite xbits_lor. repeat rewrite <- I2N.inj_lsl.
rewrite <- I2N.inj_lor.
rewrite xbits_decode1. change (xbits ♮(16 << 24)%sint63 23 26) with 0. decode_hammer.
pose proof (shiftr_bdes ♮immhi 18 ltac:(lia)) as Hb.
destruct Hb; rewrite H2; psimpl. 
unfold pc_rel. repeat rewrite xbits_decode by lia. 
nify. decode_hammer. 
unfold pc_rel. repeat rewrite xbits_decode by lia. 
nify. decode_hammer. reflexivity.

rewrite xbits_decode1.
assert (♮immlo=0\/♮immlo=1\/♮immlo=2\/♮immlo=3) by lia. 
rewrite I2N.inj_lsl.
destruct H2 as [-> | [-> | [-> | ->]]]. 
all: psimpl; reflexivity.
Admitted. (*Qed*)

Lemma decode_BL:
forall imm26,
(toN imm26) < 2^26 ->
arm_decode (toN (Encode.BL imm26)) = ARM_BL (toN imm26).
Proof.
intros. pose proof H as H'.
change (2^26) with (2^25*2) in H. apply shiftr_bdes in H.
unfold Encode.BL. nify. 
change (N.lor (N.shiftl ♮1 ♮31 mod 2 ^ 63)
(N.shiftl ♮5 ♮26 mod 2 ^ 63)) with 2483027968.
unfold arm_decode. rewrite xbits_lor.
change ((xbits 2483027968 25 29)) with 10.
unfold xbits. psimpl (_-_).
destruct H; rewrite H; psimpl.
all: unfold branch_exc; decode_hammer.
all: unfold uncond_b_imm; decode_hammer.
Qed.


Lemma decode_MOVK :
forall sf hw imm16 Rd,
(toN imm16) < 2^16 ->
(toN Rd) < 2^4 ->
(toN hw) < 2^2 ->
(toN sf) < 2^1 -> 
((toN sf) = 0 -> toN hw < 2^1) ->
arm_decode (toN (Encode.MOVK sf hw imm16 Rd)) = 
ARM_MOVE_IMM ARM_MOVK_IMM (toN Rd) (toN imm16) 
(if toN sf =? 0 then 32 else 64) (toN hw).
Proof.
intros. pose proof H2 as H2'.
change (2^1) with (2^0*2) in H2. apply shiftr_bdes in H2. rewrite N.shiftr_0_r in H2.
unfold Encode.MOVK. vm_compute (229 << 23). 

unfold arm_decode. repeat rewrite xbits_decode by lia. rewrite xbits_decode1 by simpl_sf H2.
change (xbits ♮1920991232 25 29) with 9. psimpl.

unfold dp_imm. repeat rewrite xbits_decode by lia. rewrite xbits_decode1 by simpl_sf H2. 
change (xbits ♮1920991232 23 26) with 5. psimpl.

unfold move_wide_imm. repeat rewrite xbits_decode by lia. repeat rewrite xbits_decode1 by simpl_sf H2.
vm_compute (N.succ 31). 
change (xbits ♮1920991232 29 31) with 3. psimpl.

repeat rewrite I2N.inj_lor. repeat rewrite I2N.inj_lsl. repeat rewrite xbits_decode by lia.
destruct H2; rewrite H2. psimpl. decode_hammer. pose proof H2 as H10.

apply H3 in H2. 
assert (♮hw < 2 ^ 1 -> ♮hw <> 2 ->  (N.land ♮hw 2 =? 2) = false). intros.
change (2^1) with (2^0*2) in H4. apply shiftr_bdes in H4. 
rewrite N.shiftr_0_r in H4. destruct H4; rewrite H4; reflexivity. 
rewrite H4.  reflexivity. apply H3. assumption. lia. 

change (xbits (N.shiftl 1 ♮31 mod 2 ^ 63) 31 32) with 1. psimpl.
decode_hammer.
Qed.


Lemma decode_MOVZ :
forall sf hw imm16 Rd,
(toN imm16) < 2^16 ->
(toN Rd) < 2^4 ->
(toN hw) < 2^2 ->
(toN sf) < 2^1 -> 
((toN sf) = 0 -> toN hw < 2^1) ->
arm_decode (toN (Encode.MOVZ sf hw imm16 Rd)) = 
ARM_MOVE_IMM ARM_MOVZ_IMM (toN Rd) (toN imm16) 
(if toN sf =? 0 then 32 else 64) (toN hw).
Proof.
intros. pose proof H2 as H2'.
change (2^1) with (2^0*2) in H2. apply shiftr_bdes in H2. rewrite N.shiftr_0_r in H2.
unfold Encode.MOVZ. vm_compute (165 << 23). 

unfold arm_decode. repeat rewrite xbits_decode by lia. rewrite xbits_decode1 by simpl_sf H2.
change (xbits ♮1384120320 25 29) with 9. psimpl.

unfold dp_imm. repeat rewrite xbits_decode by lia. rewrite xbits_decode1 by simpl_sf H2. 
change (xbits ♮1384120320 23 26) with 5. psimpl.

unfold move_wide_imm. repeat rewrite xbits_decode by lia. repeat rewrite xbits_decode1 by simpl_sf H2.
vm_compute (N.succ 31). 
change (xbits ♮1384120320 29 31) with 2. psimpl.

repeat rewrite I2N.inj_lor. repeat rewrite I2N.inj_lsl. repeat rewrite xbits_decode by lia.
destruct H2; rewrite H2. psimpl. decode_hammer. pose proof H2 as H10.

apply H3 in H2. 
assert (♮hw < 2 ^ 1 -> ♮hw <> 2 ->  (N.land ♮hw 2 =? 2) = false). intros.
change (2^1) with (2^0*2) in H4. apply shiftr_bdes in H4. 
rewrite N.shiftr_0_r in H4. destruct H4; rewrite H4; reflexivity. 
rewrite H4.  reflexivity. apply H3. assumption. lia. 

change (xbits (N.shiftl 1 ♮31 mod 2 ^ 63) 31 32) with 1. psimpl.
decode_hammer.
Qed.

Lemma decode_CBZ:
forall sf op imm19 Rt,
(toN imm19) < 2^19 ->
(toN Rt) < 2^5 ->
(toN op) = 0 ->
(toN sf) < 2^1 -> 
arm_decode (toN (Encode.CBZ sf op imm19 Rt)) =
ARM_CBZ (toN Rt) (toN imm19) (if toN sf =? 0 then 32 else 64) .
Proof.
intros. pose proof H2 as H2'.
change (2^1) with (2^0*2) in H2. apply shiftr_bdes in H2. rewrite N.shiftr_0_r in H2. 

unfold Encode.CBZ. vm_compute (52 << 24). 
unfold arm_decode.  repeat rewrite xbits_decode by lia. rewrite xbits_decode1 by simpl_sf H2.
change (xbits ♮872415232 25 29) with 10. psimpl.

unfold branch_exc. repeat rewrite xbits_decode by lia.
repeat rewrite I2N.inj_lor, xbits_lor;
rewrite I2N.inj_lsl. 
destruct H2; rewrite H2; decode_hammer.
all: change (xbits ♮872415232 29 32) with 1; psimpl.
all: rewrite H1; psimpl.
all: rewrite N.shiftr_div_pow2; rewrite land_pow2_small by lia; psimpl.
all: unfold comp_and_b; decode_hammer.

Qed. (*Qed*)

Lemma decode_TBZ:
forall b5 op b40 imm14 Rt,
(toN imm14) < 2^14 ->
(toN Rt) < 2^5 ->
(toN op) = 0 ->
(toN b5) <2^1 ->
(toN b40) < 2^4 -> 
arm_decode (toN (Encode.TBZ b5 op b40 imm14 Rt)) =
ARM_TBZ (toN Rt) (toN imm14) (toN b5) (toN b40) .
Proof.
intros. 
pose proof H2 as H2'.
change (2^1) with (2^0*2) in H2. apply shiftr_bdes in H2. rewrite N.shiftr_0_r in H2. 

unfold Encode.TBZ. vm_compute (54 << 24). 
unfold arm_decode.  repeat rewrite xbits_decode by lia. rewrite xbits_decode1 by simpl_sf H2.
change (xbits ♮905969664 25 29) with 11. psimpl.

unfold branch_exc. repeat rewrite xbits_decode by lia.
repeat rewrite I2N.inj_lor, xbits_lor;
rewrite I2N.inj_lsl. 
destruct H2; rewrite H2; decode_hammer.
all: change (xbits ♮905969664 29 32) with 1; psimpl.
all: rewrite H1; psimpl. 
all: change (N.lor ♮905969664 (N.shiftl 1 ♮24)) with 922746880;
change (xbits ♮905969664 12 26) with 8192;
change (N.lor 8192 (2 ^ 12)) with 12288.
all: decode_hammer. 

all: unfold test_and_b; decode_hammer.
Qed. (*Qed*)

Lemma decode_UBFX:
(*alias: UBFM*)
forall sf N immr imms Rn Rd,
(toN immr) < 2^5 ->
(toN imms) <2^5 ->
(toN N) < 2^1 ->
(toN sf) < 2^1 ->
(toN sf = toN N)->
(toN Rn) < 2^4 -> 
(toN Rd) < 2^5 -> 
arm_decode (toN (Encode.UBFX sf N immr imms Rn Rd)) =
ARM_LOGICAL_IMM (ARM_UBFM_IMM) (toN Rn) (toN Rd) (toN immr) (toN imms) (toN sf) (toN N) .
Proof.
intros. 
pose proof H2 as H2'.
change (2^1) with (2^0*2) in H2. apply shiftr_bdes in H2. rewrite N.shiftr_0_r in H2.

unfold Encode.UBFX. vm_compute (166 << 23).
unfold arm_decode. repeat rewrite xbits_decode by lia. rewrite xbits_decode1 by simpl_sf H2.
change (xbits ♮1392508928 25 29) with 9. psimpl.

unfold dp_imm. repeat rewrite xbits_decode by lia. rewrite xbits_decode1 by simpl_sf H2.
change (xbits ♮1392508928 23 26) with 6. psimpl.

unfold bitfield. change (N.succ 31) with 32.
repeat rewrite xbits_decode by lia. rewrite xbits_decode1 by simpl_sf H2.
change ((xbits ♮1392508928 29 31)) with 2. psimpl.
repeat rewrite I2N.inj_lor, xbits_lor;
rewrite I2N.inj_lsl. 
destruct H2; rewrite H2; psimpl; change(N.succ 22) with 23. 
all:  decode_hammer; rewrite H2 in H3; rewrite <- H3.
all: (reflexivity|| lia). 

Qed. (*Qed*)


Lemma decode_EOR:
forall sf shift Rm imm6 Rn Rd,
toN imm6 < 2^6 ->
toN shift < 2^2 ->
toN Rn < 2^5 ->
toN sf < 2^1 ->
(toN sf = 0 -> toN imm6 < 2^5) ->
toN Rd < 2^5 ->
toN Rm < 2^5 ->
arm_decode (toN (Encode.EOR sf shift Rm imm6 Rn Rd)) =
ARM_LOG_SHIFTED ARM_EOR_LOG_REG (toN sf) (toN shift) (toN Rm) (toN imm6) (toN Rn) (toN Rd).
Proof.
intros.
pose proof H2 as H2'.
change (2^1) with (2^0*2) in H2. apply shiftr_bdes in H2. rewrite N.shiftr_0_r in H2.

unfold Encode.EOR. vm_compute (74 << 24).
unfold arm_decode. repeat rewrite xbits_decode by lia. rewrite xbits_decode1 by simpl_sf H2.
change (xbits ♮1241513984 25 29) with 5. psimpl.

unfold dp_reg. change (N.succ 30) with 31. repeat rewrite xbits_decode by lia. repeat rewrite xbits_decode1 by simpl_sf H2.
change (xbits ♮1241513984 30 31) with 1. psimpl. 
change (N.succ 28) with 29. repeat rewrite xbits_decode by lia.
rewrite xbits_decode1 by simpl_sf H2. 
change( xbits ♮1241513984 28 29) with 0. psimpl.
repeat rewrite xbits_decode by lia.
change 8 with (2^3).
rewrite land_pow2_small. psimpl.
2: { 
rewrite xbits_decode1.
2:{ rewrite xbits_decode1. reflexivity. rewrite I2N.inj_lsl.
destruct H2; rewrite H2. reflexivity. reflexivity.
}
unfold xbits.
rewrite I2N.inj_lsl. rewrite N.shiftl_mul_pow2.
psimpl.
assert (♮shift=0\/♮shift=1\/♮shift=2\/♮shift=3) by lia. 
destruct H6 as [-> | [-> | [-> | ->]]]. 
all: vm_compute;reflexivity.
}

unfold data_proc_logical. nify. decode_hammer.
destruct H2; rewrite H2. apply H3 in H2.
all: change (xbits ♮1241513984 29 31) with 2; psimpl; reflexivity.

Qed. (*Qed*)
 

Lemma decode_LDR_r:
(*alias: UBFM*)
forall size Rm option S Rn Rt,
(toN Rm) <2^5 ->
(toN option) < 2^3 ->
(toN S) < 2^1 ->
(toN size) = 2 \/ (toN size = 3)->
(toN Rn) < 2^5 -> 
(toN Rt) < 2^5 -> 
((N.land ♮option 2 =? 0) = false) -> (*page C6-981,*)
arm_decode (toN (Encode.LDR_r size Rm option S Rn Rt)) =
ARM_LD_STR_REG (ARM_LDR_REG) (toN Rn) (toN Rm) (toN Rt) (toN option)    
(if toN size =?2 then 32 else 64) (toN S).
Proof.
intros.
pose proof H1 as H'.
change (2^1) with (2^0*2) in H1. apply shiftr_bdes in H1. rewrite N.shiftr_0_r in H1.

unfold Encode.LDR_r. vm_compute (451 << 21).
unfold arm_decode. repeat rewrite xbits_decode by lia.  
rewrite xbits_decode1 by simpl_sf H2.
change (xbits ♮945815552 25 29) with 12. psimpl.

unfold load_store. repeat rewrite xbits_decode by lia.
vm_compute (N.succ _). 
nify. destruct H2; rewrite H2. 
change (xbits (N.lor (N.shiftl 2 ♮30 mod 2 ^ 63) ♮945815552) 28 32) with 11.
change (xbits (N.lor (N.shiftl 3 ♮30 mod 2 ^ 63) ♮945815552) 28 32) with 15.
all: psimpl; autorewrite with decode_db; vm_compute (_ - _).
all: destruct H1; rewrite H1; psimpl;
vm_compute (xbits ♮2 0 2); psimpl.
all: change (xbits ♮945815552 16 22) with 32; change (xbits ♮945815552 28 32 mod 4) with 3.
all: rewrite N.land_lor_distr_l; replace (N.land ♮Rm 32) with 0; psimpl;
 try( 
  symmetry;
  change 32 with (2^5); apply land_pow2_small; assumption
).
all: unfold load_store_reg_off; decode_hammer;rewrite H5;
change (xbits ♮945815552 22 24) with 1;psimpl; reflexivity.

Qed. (*Qed*)

(*All Admitteds are Qeds just takes a while to run*)

Lemma decode_LDR_STR:
forall size opc imm9 pre(*aka bit11*) Rn Rt,
(toN size) = 3 ->
((toN opc) = 0 /\ (toN pre = 3))\/ ((toN opc)=1 /\ (toN pre)=1) ->
(toN imm9) < 2^9 ->
(toN Rn) < 2^5 ->
(toN Rt) < 2^5 ->
arm_decode (toN (Encode.LDR_STR size opc imm9 pre Rn Rt)) =
if ((toN opc) =? 0) then ARM_INDEXED ARM_STR_IMM (toN Rn) (toN Rt) (toN imm9) 64 true true false else ARM_INDEXED ARM_LDR_IMM (toN Rn) (toN Rt) (toN imm9) 64 true true true.
Proof.
intros.

unfold Encode.LDR_STR. nify. rewrite H.
destruct H0; destruct H0; rewrite H0, H4; psimpl;decode_hammer.
all: unfold arm_decode;
autorewrite with decode_db; vm_compute (_-_); 
change (xbits ♮56 1 5) with 12; decode_hammer. 
all: unfold load_store; decode_hammer; change (xbits ♮56 4 8) with 3; change 32 with (2^5); rewrite land_pow2_small; psimpl.
2,4 : rewrite N.shiftr_div_pow2; change (2^5) with (2^9/2^4); lia.
unfold load_store_reg_imm_pre; decode_hammer.
unfold load_store_reg_imm_poi; decode_hammer.

Qed. (*Qed*)

Lemma decode_LDP_STP:
forall opc pre(*aka bit23*) L imm7 Rt2 Rn Rt,
(toN opc = 2)->
((toN pre) = 1 /\(toN L) = 0)\/((toN pre) = 0 /\(toN L) = 1)->
(toN imm7) < 2^7 ->
(toN Rt2) < 2^5 ->
(toN Rn) < 2^5 ->
(toN Rt) < 2^5 ->
arm_decode (toN (Encode.LDP_STP opc pre L imm7 Rt2 Rn Rt)) =
if ((toN pre) =? 0) then ARM_LD_STR_REG_PAIR ARM_LDP (toN Rn) (toN Rt) (toN Rt2) (toN imm7) 3 true true
else ARM_LD_STR_REG_PAIR ARM_STP (toN Rn) (toN Rt) (toN Rt2) (toN imm7) 3 true false.
Proof.
intros.

unfold Encode.LDP_STP. nify. rewrite H.
destruct H0; destruct H0; rewrite H0, H5; psimpl;decode_hammer.
all: unfold arm_decode
; decode_hammer;
change (xbits ♮81 2 6) with 4; psimpl. 
change (N.lor (N.lor (N.shiftl 2 ♮30) (N.shiftl ♮81 ♮23))
(N.shiftl 1 ♮24)) with 2843738112.
2: change (N.lor (N.lor (N.shiftl 2 ♮30) (N.shiftl ♮81 ♮23))
(N.shiftl 1 ♮22)) with 2831155200.
all: unfold load_store; decode_hammer.
unfold load_store_pre_indx_pair; decode_hammer. 
unfold load_store_post_indx_pair; decode_hammer.
Qed.

(*Execution Lemmas*)

