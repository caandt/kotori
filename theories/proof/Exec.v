From Kotori Require Import proof.Util proof.Decode proof.I2N.
From Stdlib Require Import ZArith.
From Picinae Require Import armv8 armv8_lifter_rework.
Open Scope N_scope.

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
  intros. rewrite decode_MOVZ in XS by lia.
  unfold arm2il, arm_mov_imm2il, arm_varid in XS.
  simpl in *. remember (_ mod _).
  remember (_<<_).
  repeat case_match; step_stmt XS; by destruct XS.
Qed.
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
  intros. rewrite decode_MOVK in XS by lia.
  unfold arm2il, arm_mov_imm2il, arm_varid, XtoVar in XS.
  simpl in *. remember (_ mod _).
  remember (N.lnot _ _). remember (♮_ << (_ << _)).
  repeat case_match; step_stmt XS; by destruct XS.
Qed.
Lemma ExecBL:
  forall {s s' x a c m imm26}
    (IMM: Asm.bounded m 26 = Some imm26)
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.Encode.BL imm26))) c s' x),
    reset_temps s s' = s.[R_PC := a mod 2^64].[R_X30 := a ⊕ 4] /\ x = Some (Addr (a ⊕ ofZ 64 (Sint63Axioms.to_Z m * 4))).
Proof.
  intros. pose proof IMM. so IMM. case_match; try done. so IMM. apply bounded_toZ in H; try lia.
  rewrite decode_BL in XS by (subst'' IMM; rewrite I2N.inj_land, I2N.inj_ones, N.mod_small, N.land_ones; lia with (ones_bound ♮26)).
  unfold arm2il, arm_bl2il in XS. remember (_ mod _). remember (scast _ _ _). step_stmt XS.
  subst. unfold scast in XS.
  rewrite !N.Div0.add_mod_idemp_l, <-(toZ_lsl ♮26 2), H, Z.shiftl_mul_pow2 in XS by lia.
  by destruct XS.
Qed.
