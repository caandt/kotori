From Kotori Require Import proof.Util proof.Decode proof.I2N.
From Kotori Require Import proof.Decode.
From Stdlib Require Import ZArith.
From Picinae Require Import armv8 armv8_lifter_rework.
Open Scope N_scope.
Require Import Lia.

(*Why do we have this here?*)

Notation "x ⊕ y" := ((x+y) mod 2^64) (at level 50, left associativity).
Notation "x ⊖ y" := (msub 64 x y) (at level 50, left associativity).
Notation "x ⊗ y" := ((x*y) mod 2^64) (at level 40, left associativity).
Notation "x << y" := (N.shiftl x y) (at level 30, y constr at next level) : N_scope.
Notation "x >> y" := (N.shiftr x y) (at level 30, y constr at next level) : N_scope.
Notation "f .[ x := y ]" := (update f x y) (at level 50, left associativity, format "f .[ x  :=  y ]") .

Lemma cmod_canonical:
  forall w z, Sint63.cmod z (2^w) = canonicalZ w z.
Proof.
  unfold Sint63.cmod, canonicalZ. intros. destruct w.
  - lia.
  - rewrite <-(Z.pow_1_r 2) at 2 5. rewrite <-Z.pow_sub_r; lia.
  - rewrite !Z.pow_neg_r; lia.
Qed.
Lemma canonicalZ_widen:
  forall z w w'
    (W: (0 < w < w')%Z)
    (Z: (-2 ^ Z.pred w <= canonicalZ w' z < 2 ^ Z.pred w)%Z),
  canonicalZ w z = canonicalZ w' z.
Proof.
  intros. pose proof (Z.pow_le_mono_r 2 (Z.pred w) (Z.pred w')).
  replace w with (Z.min w w') by lia.
  rewrite <-canonicalZ_involutive by lia.
  erewrite canonicalZ_id; auto. split; rewrite ?N2Z.inj_pred, Z2N.id; lia.
Qed.
Definition wBis: wB = (2 ^ 63)%Z := eq_refl.
Lemma bounded_toZ:
  forall x w b
    (W: (w <? 63 = true)%uint63)
    (W': (0 <? w = true)%uint63)
    (B: Asm.bounded x w = Some b),
  toZ ♮w ♮b = Sint63.to_Z x.
Proof.
  intros. repeat so B. subst. nify.
  rewrite I2N.inj_ones, ones_mod_pow2', N.land_ones, N.min_l, toZ_mod_pow2 by lia.
  rewrite andb_true_iff, Sint63.ltb_spec, Sint63.leb_spec, Z.compare_le_iff, Z.compare_lt_iff in oe.
  rewrite !Sint63.to_Z_cmodwB, !wBis, !cmod_canonical in *.
  unfold toZ, toN. rewrite !Z2N.id by lia. erewrite canonicalZ_widen; auto. lia.
  eqapply oe;
  erewrite ?opp_spec, I2Z.inj_lsl, Z.shiftl_mul_pow2, Z.mul_1_l, wBis, ?canonicalZ_mod_pow2, ?Z.mod_small, canonicalZ_id;
  repeat f_equal; try split; simpl; lia with (Z.pow_lt_mono_r 2 (to_Z (w-1)) 62).
Qed.
Lemma toZ_lsl:
  forall w s n, Z.shiftl (toZ w n) (Z.of_N s) = toZ (w + s) (n << s).
Proof.
  intros. destruct w.
  - by erewrite toZ_0_l, N.add_0_l, Z.shiftl_0_l, N.shiftl_mul_pow2, <-toZ_mod_pow2, N.Div0.mod_mul, toZ_0_r.
  - rewrite toZ_shiftl, !Z.shiftl_mul_pow2 by lia. unfold toZ, canonicalZ.
    by rewrite N2Z.inj_add, <-Z.add_pred_l, !Z.pow_add_r, <-Z.mul_add_distr_r, Z.mul_mod_distr_r, Z.mul_sub_distr_r by lia.
Qed.
Lemma canonicalZ_lsl:
  forall w s n, (0 < w -> 0<=s -> Z.shiftl (canonicalZ w n) s = canonicalZ (w + s) (Z.shiftl n s))%Z.
Proof.
  intros. rewrite !Z.shiftl_mul_pow2 by lia. unfold canonicalZ.
  by rewrite <-Z.add_pred_l, !Z.pow_add_r, <-Z.mul_add_distr_r, Z.mul_mod_distr_r, Z.mul_sub_distr_r by lia.
Qed.
Lemma ExecMovz:
  forall s s' c' x a r imm hw
    (I: (imm <? 1 << 16 = true)%uint63)
    (H: (hw <? 4 = true)%uint63)
    (R: (r <? 31 = true)%uint63)
    (XS: exec_stmt arm8typctx s
      (arm2il a (arm_decode ♮(Asm.Encode.MOVZ 1 hw imm r))) c' s' x),
    reset_temps s s' = s.[R_PC := a mod 2^64].[
      arm_varid ♮r := ♮imm << (♮hw<<4)
    ] /\ x = None.
Proof.
  intros. rewrite decode_MOVZ in XS. 
  unfold arm2il, arm_mov_imm2il, arm_varid in XS.
  simpl in *. remember (_ mod _).
  remember (_<<_).
  repeat case_match; step_stmt XS ;by destruct XS.
  1-2: admit.
  apply Uint63.ltb_spec in H.
  unfold toN.
  change (2^2 ) with 4.
  apply Uint63.ltb_spec in H.
  Search (_=true).
  all: easy.
Admitted.
Lemma ExecMovk:
  forall s s' c' x a r imm hw
    (I: (imm <? 1 << 16 = true)%uint63)
    (H: (hw <? 4 = true)%uint63)
    (R: (r <? 31 = true)%uint63)
    (XS: exec_stmt arm8typctx s
      (arm2il a (arm_decode ♮(Asm.Encode.MOVK 1 hw imm r))) c' s' x),
    reset_temps s s' = s.[R_PC := a mod 2^64].[
      arm_varid ♮r :=
        N.lor
          (N.land
            (s (arm_varid ♮r))
            (N.lnot (N.ones 16 << (♮hw << 4)) 64))
          (♮imm << (♮hw << 4))
     ] /\ x = None.
Proof.
  intros. rewrite decode_MOVK in XS.
  unfold arm2il, arm_mov_imm2il, arm_varid, XtoVar in XS.
  simpl in *. remember (_ mod _).
  remember (N.lnot _ _). remember (♮_ << (_ << _)).
  repeat case_match; step_stmt XS. 
Admitted.
Lemma ExecBL:
  forall {s s' x a c m imm26}
    (IMM: Asm.bounded m 26 = Some imm26)
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.Encode.BL imm26))) c s' x),
    reset_temps s s' = s.[R_PC := a mod 2^64].[R_X30 := a ⊕ 4] /\ x = Some (Addr (a ⊕ ofZ 64 (Sint63Axioms.to_Z m * 4))).
Proof.
(**  intros. pose proof IMM. so IMM. case_match; try done. so IMM. apply bounded_toZ in H; try lia.
  rewrite decode_BL in XS by (subst'' IMM; rewrite I2N.inj_land, I2N.inj_ones, N.mod_small, N.land_ones; lia with (ones_bound ♮26)).
  unfold arm2il, arm_bl2il in XS. remember (_ mod _). remember (scast _ _ _). step_stmt XS.
  subst. unfold scast in XS.
  rewrite !N.Div0.add_mod_idemp_l, <-(toZ_lsl ♮26 2), H, Z.shiftl_mul_pow2 in XS by lia.
  by destruct XS.**)
Admitted.
Lemma ExecADR:
forall {immlo immhi Rd c' s s' x a}
(RD: (toN Rd) <2^5)
(IMMHI: (toN immhi) < 2 ^ 19)
(IMMLO: (toN immlo) < 2 ^ 2 )
    (XS: exec_stmt arm8typctx s
      (arm2il a (arm_decode ♮(Asm.Encode.ADR immlo immhi Rd))) c' s' x),
    reset_temps s s' = s.[R_PC := a mod 2^64].[arm_varid ♮Rd := (a mod 2^64) ⊕ (scast 21 64 (N.lor (♮immhi << 2) ♮immlo))].
      
Proof.
intros. rewrite decode_ADR in XS. unfold arm2il in XS.
unfold arm_adr2il in XS. 
remember (_ mod _). 
remember (scast _ _ _). all:try assumption. 

unfold arm_varid in XS.  repeat case_match;
step_stmt XS; destruct XS as [[XS _]_];
try assumption.
Qed.
Lemma ExecADRP:
forall {immlo immhi Rd c' s s' x a}
(RD: (toN Rd) <2^5)
(IMMHI: (toN immhi) < 2 ^ 19)
(IMMLO: (toN immlo) < 2 ^ 2 )
    (XS: exec_stmt arm8typctx s
      (arm2il a (arm_decode ♮(Asm.Encode.ADRP immlo immhi Rd))) c' s' x),
    reset_temps s s' = s.[R_PC := a mod 2^64] /\
      x = Some (Raise 0).
      
Proof.
intros. rewrite decode_ADRP in XS. unfold arm2il in XS.
unfold arm_adrp2il in XS.
remember (_ mod _). remember (scast _ _ _).
step_stmt XS. destruct XS. all: assumption.
Qed.
Ltac destruct_match_e :=
repeat
match goal with
| |- context [ match ?x with
| _ => _
end ] => destruct x eqn:?
end.

Lemma cbz_helper_sp_branch:
forall {n n1 s c' s' x n0 RB}
(XS: exec_stmt arm8typctx (s.[R_PC := n])
(if if s RB mod 2 ^ n1 =? 0 then 1 else 0
then Nop
else
If (UnOp OP_NOT (BinOp OP_EQ (Var R_nRW) (Word 1 1)))
(Jmp (BinOp OP_PLUS (Var R_PC) (Word n0 64))) (Exn 0)) c' s' x ∧ True
),
(reset_temps s s' = (s.[R_PC := n])).
Proof.
intros. 
destruct XS as [XS _]; destruct (if s RB mod 2 ^ n1 =? 0 then 1 else 0); 
step_stmt XS; destruct XS as [XS _].
destruct XS as [XS _]. assumption.
destruct ( s R_nRW =? 1); psimpl in XS; step_stmt XS;
destruct XS as [[XS _]_]; assumption.
Qed.

Lemma cbz_helper_x_branch:
forall {n n1 s c' s' x n0 RB}
(Heqb : (s R_nRW =? 1) = true)
(Heqn:( s RB mod 2 ^ n1 =? 0) = true)
(H_STATE: s.[R_PC := n] R_nRW = s R_nRW)
(XS: exec_stmt arm8typctx (s.[R_PC := n])
(if if s RB mod 2 ^ n1 =? 0 then 1 else 0
then Nop
else
If (UnOp OP_NOT (BinOp OP_EQ (Var R_nRW) (Word 1 1)))
(Jmp (BinOp OP_PLUS (Var R_PC) (Word n0 64))) (Exn 0)) c' s' x ∧ True
),
(x = Some (Raise 0)).
Proof.
intros. rewrite Heqn in XS. remember (s.[R_PC := n]). destruct XS as [XS _]. 
step_stmt XS. rewrite Heqb in XS. psimpl in XS. destruct XS as [XS _].
step_stmt XS. destruct XS. destruct H. eassumption.
Qed.

Lemma cbz_helper_x_branch_None:
forall {n n1 s c' s' x n0 RB}

(Heqn:( s RB mod 2 ^ n1 =? 0) = false)
(H_STATE: s.[R_PC := n] R_nRW = s R_nRW)
(XS: exec_stmt arm8typctx (s.[R_PC := n])
(if if s RB mod 2 ^ n1 =? 0 then 1 else 0
then Nop
else
If (UnOp OP_NOT (BinOp OP_EQ (Var R_nRW) (Word 1 1)))
(Jmp (BinOp OP_PLUS (Var R_PC) (Word n0 64))) (Exn 0)) c' s' x ∧ True
),
(x = None).
Proof.
intros. rewrite Heqn in XS. remember (s.[R_PC := n]). destruct XS as [XS _]. 
step_stmt XS. 
 destruct XS. destruct H. eassumption.
Qed.

Lemma ExecCBZ:
  forall {sf op imm19 Rt c' s s' x a}
    (RD: toN Rt < 2^5) (IMM: toN imm19 < 2^19) (SF: toN sf < 2^1) (OP: ♮op = 0)
    (XS: exec_stmt arm8typctx s
           (arm2il a (arm_decode ♮(Asm.Encode.CBZ sf op imm19 Rt))) c' s' x),
  let s0 := s.[R_PC := a mod 2^64] in
  reset_temps s s' = s0 ∧
  x = if (s (arm_varid ♮Rt)) mod 2 ^ (if ♮sf =? 0 then 32 else 64) =? 0 then
        if s R_nRW =? 1 then Some (Raise 0)
        else Some (Addr ((a mod 2^64) ⊕ scast 21 64 (♮imm19 << 2)))
      else None.
Proof.
intros.
assert (H_STATE: s.[R_PC := a mod 2 ^ 64] R_nRW = s R_nRW).
rewrite update_frame. reflexivity. discriminate.
repeat destruct_match_e.

 
all: rewrite decode_CBZ in XS; unfold arm2il in XS;
unfold arm_cbz2il in XS.
all: try assumption; remember (_ mod _);
remember (scast _ _ (♮_ << _)) as n0;
remember(if ♮sf =? 0 then 32 else 64).

1,2: unfold XtoVar in XS; repeat case_match; step_stmt XS; split.
all: try eapply cbz_helper_sp_branch. all: try eassumption.
all: try eapply cbz_helper_x_branch. all: try eassumption.
all: try eapply cbz_helper_x_branch_None. all: try eassumption.

1-124: unfold arm_varid in Heqb; rewrite Heqb in XS; destruct XS as [XS _];
step_stmt XS; rewrite Heqb0 in XS; psimpl in XS; destruct XS as [XS _];
step_stmt XS; destruct XS as [[XS XS1]_].  

all: try assumption.


unfold XtoVar in XS; repeat case_match; step_stmt XS; split.
all: try eapply cbz_helper_sp_branch. all: try eassumption.
all: try eapply cbz_helper_x_branch_None. all: try eassumption.

Qed.

Local Ltac clean_up XS n1:=
  repeat match type of XS with
  | context [_ mod 2 ^ ?k] =>
      replace k with 1 in XS
        by (transitivity (N.succ n1 - n1); [lia | reflexivity])
  end;
  simpl in XS.

(*fix lifter it shouldnt be raising an exception*)
Lemma ExecTBZ:
  forall {b5 op b40 imm14 Rt c' s s' x a}
    (RD: toN Rt < 2^5) (IMM: toN imm14 < 2^14) (SF: toN b5 < 2^1) (OP: ♮op = 0)
    (B40: ♮b40 <2^4)
    (XS: exec_stmt arm8typctx s
           (arm2il a (arm_decode ♮(Asm.Encode.TBZ b5 op b40 imm14 Rt))) c' s' x),
  let s0 := s.[R_PC := a mod 2^64] in
  reset_temps s s' = s0 ∧ 
  ( x = Some (Raise 0) \/
  x =Some (Addr ((a mod 2^64) ⊕ scast 16 64 (♮imm14 << 2))) \/
  x=None).
Proof.
intros.


all: rewrite decode_TBZ in XS; unfold arm2il in XS;
unfold arm_tbz2il in XS. 
 remember (_ mod _).
remember (scast _ _ (♮_ << _)) as n0.
remember (cbits _ _ _).

all: try assumption.
split.

-- 

unfold XtoVar in XS. repeat case_match;
step_stmt XS; clean_up XS n1.

all: destruct (s _ >> n1 mod 2 ^ 1 =? 0);
destruct XS as [XS _];
step_stmt XS; destruct XS as [XS _];
 [(destruct (s R_nRW =? 1); step_stmt XS; destruct XS as [[XS _]_];
subst s0; assumption)
 | destruct XS; subst s0; assumption].


--

unfold XtoVar in XS. repeat case_match;
step_stmt XS; clean_up XS n1. 

destruct XS as [XS _]; destruct (s _ >> n1 mod 2 ^ 1 =? 0); try
destruct XS as [XS _].
step_stmt XS. destruct XS as [XS _].


all: destruct XS as [XS _]; destruct (s _ >> n1 mod 2 ^ 1 =? 0); try
destruct XS as [XS _];
step_stmt XS; destruct XS as [XS _];
destruct (s R_nRW =? 1); try step_stmt XS; try destruct XS as [[_ XS]_]. 

all: try first [
left; assumption|
right; left; assumption| destruct XS; right; right; assumption]. 

Qed.

Lemma ExecEOR:
forall {sf shift imm6 Rm Rn Rd c' s s' x a}
    (RD: toN sf < 2^1) (IMM: toN imm6 < 2^6) (SHFT: toN shift < 2^1) 
    (RM: toN Rm < 2^5) (RN: toN Rn < 2^5) (RD: toN Rd < 2^5)
    (XS: exec_stmt arm8typctx s
           (arm2il a (arm_decode ♮(Asm.Encode.EOR sf shift Rm imm6 Rn Rd))) c' s' x),
  let s0 := s.[R_PC := a mod 2^64] in
  reset_temps s s' = s0 ∧
  x = if (s (arm_varid ♮Rd)) mod 2 ^ (if ♮sf =? 0 then 32 else 64) =? 0 then
        if s R_nRW =? 1 then Some (Raise 0)
        else Some (Addr ((a mod 2^64) ⊕ scast 21 64 (♮imm6 << 2)))
      else None.
Proof.
intros.