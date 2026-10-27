From Kotori Require Decode.
From Kotori Require Import proof.Util proof.Decode proof.I2N.
From Stdlib Require Import ZArith ZifySint63 ZifyUint63.
From Picinae Require Import armv8 armv8_lifter_rework.
From coqutil Require Import prove_Zeq_bitwise.
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
Ltac step XS := step_stmt XS;
  repeat match goal with
  | H: _ /\ True |- _ => destruct H as [H _]
  | H: reset_temps _ _ = _ /\ _ = _ |- _ =>
      let S := fresh "S" in
      let X := fresh "X" in
      destruct H as [S X]
  end.
Lemma ExecMovz:
  forall s s' c' x a r imm hw
    (I: (imm <? 1 << 16 = true)%uint63)
    (H: (hw <? 4 = true)%uint63)
    (R: (r <? 32 = true)%uint63)
    (XS: exec_stmt arm8typctx s
      (arm2il a (arm_decode ♮(Asm.Encode.MOVZ 1 hw imm r))) c' s' x),
    reset_temps s s' = s.[
      arm_varid ♮r := ♮imm << (♮hw<<4)
    ] /\ x = None.
Proof.
  intros. rewrite decode_MOVZ in XS by lia.
  unfold arm2il, arm_mov_imm2il, arm_varid in XS.
  simpl in *. remember (_ mod _).
  remember (_<<_). repeat case_match; by step XS.
Qed.
Lemma ExecMovk:
  forall s s' c' x a r imm hw
    (I: (imm <? 1 << 16 = true)%uint63)
    (H: (hw <? 4 = true)%uint63)
    (R: (r <? 32 = true)%uint63)
    (XS: exec_stmt arm8typctx s
      (arm2il a (arm_decode ♮(Asm.Encode.MOVK 1 hw imm r))) c' s' x),
    reset_temps s s' = s.[
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
  repeat case_match; by step XS.
Qed.
Lemma ExecBL:
  forall {s s' x a c m imm26}
    (IMM: Asm.bounded m 26 = Some imm26)
    (XS: exec_stmt arm8typctx s (arm2il (a*4) (arm_decode ♮(Asm.Encode.BL imm26))) c s' x),
    reset_temps s s' = s.[R_X30 := a * 4 ⊕ 4] /\ x = Some (Addr (ofZ 62 (Z.of_N a + Sint63Axioms.to_Z m) * 4)).
Proof.
  intros. pose proof IMM. so IMM. case_match; try done. so IMM. apply bounded_toZ in H; try lia.
  rewrite decode_BL in XS by (subst'' IMM; rewrite I2N.inj_land, I2N.inj_ones, N.mod_small, N.land_ones; lia with (ones_bound ♮26)).
  unfold arm2il, arm_bl2il in XS. remember (_ mod _). remember (scast _ _ _). step XS.
  subst. rewrite S. unfold scast.
  rewrite !N.Div0.add_mod_idemp_l, <-(toZ_lsl ♮26 2), H, Z.shiftl_mul_pow2 by lia.
  split. done. do 2 f_equal. rewrite add_sbop.
  rewrite toZ_ofZ by (split;simpl;lia). unfold ofZ. f_equal. rewrite <-Z.add_mod_idemp_l by lia.
  rewrite mod_pow2_toZ; lia.
Qed.
Tactic Notation "simp" uconstr(x) :=
  let X := fresh in
  let H := fresh in
  remember x as X eqn:H; cbv in H; subst X.
Lemma ltb_case:
  forall i j, ((i <? j = true) -> i = j-1 \/  i <? j-1 = true)%uint63.
Proof. intros. rewrite <-I2N.inj_iff. lia. Qed.
Ltac destruct_ltb H :=
  match type of H with
  | (_ <? 0 = true)%uint63 => clear -H; lia
  | (?x <? ?n = true)%uint63 =>
      let H1 := fresh in
      pose proof (ltb_case x n H) as H1; clear H; destruct H1 as [H|H]; simp (n-1)%uint63; [|destruct_ltb H]
  end.
(* The lifted address computation of LDR (register, LSL #3). *)
Lemma ldr_offset:
  forall b i, b ⊕ N.lor (((i mod 2 ^ 64) >> 0 mod 2 ^ 61) << 3) 0 = b ⊕ i * 8.
Proof.
  intros.
  rewrite N.lor_0_r, N.shiftr_0_r, mp2_mod_mod_min, <-(N.land_ones _ 61), N.shiftl_land.
  change (N.ones 61 << _) with (N.lnot (N.ones 3) 64).
  rewrite <-N.Div0.add_mod_idemp_r, <-N_land_mod_pow2_moveout, <-N_land_mod_pow2_move.
  rewrite <-ldiff_land_low2, N.ldiff_ones_r by lia.
  rewrite <-(N.Div0.add_mod_idemp_r _ (_*8)).
  erewrite <-(recompose_bytes 3 (_⊗8)).
  by rewrite mp2_mod_mod_min, N.Div0.mod_mul, N.lor_0_l, !N.shiftl_mul_pow2.
Qed.
Lemma ExecLDR64:
  forall {s s' x a c rn rt}
    (N: (rn <? 32 = true)%uint63)
    (T: (rt <? 32 = true)%uint63)
    (AL: ♮rt = 31 -> s R_SP mod 16 = 0)
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.LDR_r64 rn rt rn))) c s' x),
    reset_temps s s' = s.[arm_varid ♮rn :=
    getmem 64 LittleE 8 (s V_MEM64) (s (arm_varid ♮rt) ⊕ s (arm_varid ♮rn) * 8)
    ] /\ x = None.
Proof.
  unfold Asm.LDR_r64. intros. rewrite decode_LDR_r in XS by lia.
  unfold arm2il, arm_ldr_reg2il, arm_ldr_reg2il_size_signed, ExtendReg' in XS.
  rewrite <-ldr_offset.
  (* the base register is SP (CheckSPAlignment, discharged by AL) or not (Nop) *)
  destruct (toN rt =? 31)%N eqn:B31.
  all: simp (N.min _ _); simpl in XS; simp (_>>_); simp (_-_).
  all: remember (_ mod _) in XS.
  - (* base register 31: discharge the SP alignment check with AL *)
    apply N.eqb_eq in B31. specialize (AL B31). assert (rt = 31%uint63) by (apply I2N.inj_iff; rewrite B31; reflexivity). subst rt.
    destruct_ltb N; subst rn; step XS;
    remember (N.land _ _) as al eqn:Hal; rewrite AL in Hal; cbn in Hal;
    replace (N.lnot 1 1) with 0 in Hal by reflexivity;
    rewrite N.land_0_r in Hal; subst al;
    step XS; by destruct XS.
  - destruct_ltb N; destruct_ltb T; subst rn rt; step XS; by destruct XS.
Qed.

Lemma I2Nlandones_bound:
  forall n m,
  ♮(n land ones m) < 2 ^ ♮m.
Proof.
  intros. destruct (N.lt_decidable ♮m 63).
  - rewrite I2N.inj_land, I2N.inj_ones, N.mod_small, N.land_ones;
    apply N.lt_le_incl, (N.pow_le_mono_r 2) in H; lia with (ones_bound ♮m).
  - remember (_ land _). lia with (N.pow_le_mono_r 2 63 ♮m).
Qed.
Lemma ExecB:
  forall {s s' x a c m imm26}
    (IMM: Asm.bounded m 26 = Some imm26)
    (XS: exec_stmt arm8typctx s (arm2il (a*4) (arm_decode ♮(Asm.Encode.B imm26))) c s' x),
    reset_temps s s' = s /\ x = Some (Addr (ofZ 62 (Z.of_N a + Sint63Axioms.to_Z m) * 4)).
Proof.
  intros. pose proof IMM. so IMM. case_match; try done. so IMM. apply bounded_toZ in H; try lia. subst'' IMM.
  rewrite decode_B in XS by apply I2Nlandones_bound.
  unfold arm2il, arm_b2il in XS. remember (_ mod _). remember (scast _ _ _). step XS.
  subst. rewrite S. unfold scast.
  rewrite !N.Div0.add_mod_idemp_l, <-(toZ_lsl ♮26 2), H, Z.shiftl_mul_pow2 by lia.
  split. done. do 2 f_equal. rewrite add_sbop.
  rewrite toZ_ofZ by (split;simpl;lia). unfold ofZ. rewrite <-Z.add_mod_idemp_l by lia.
  rewrite mod_pow2_toZ; lia.
Qed.
Lemma ExecCBZ:
  forall {s s' x a c m imm19 sf op r}
    (O: (op <? 2 = true)%uint63)
    (S: (sf <? 2 = true)%uint63)
    (R: (r <? 32 = true)%uint63)
    (IMM: Asm.bounded m 19 = Some imm19)
    (XS: exec_stmt arm8typctx s (arm2il (a*4) (arm_decode ♮(Asm.Encode.CBZ sf op imm19 r))) c s' x),
    reset_temps s s' = s /\ (x = Some (Addr (ofZ 62 (Z.of_N a + Sint63Axioms.to_Z m) * 4)) \/ x = None).
Proof.
  intros. pose proof IMM. so IMM. case_match; try done. so IMM. apply bounded_toZ in H; try lia. subst'' IMM.
  rewrite decode_CBZ in XS by (apply I2Nlandones_bound || lia).
  replace (Addr _) with (Addr (a ⊗ 4 ⊕ (scast 21 64 (♮(m land ones 19) << 2)))).
  repeat case_match;
  unfold arm2il, arm_cbz2il, arm_cbnz2il, XtoVar in XS; remember (_ mod _); remember (scast _ _ _);
  repeat case_match; step XS; case_match; step XS; split; auto; left.
  subst; unfold scast; do 2 f_equal; rewrite add_sbop, <-(toZ_lsl ♮19 2), H, Z.shiftl_mul_pow2 by lia;
  rewrite toZ_ofZ by (split;simpl;lia); unfold ofZ; rewrite <-Z.add_mod_idemp_l by lia;
  rewrite mod_pow2_toZ; lia.
Qed.
Lemma forget_cond:
  forall c s q1 e q2 q3 c' s' x,
    exec_stmt c s (q1 $; If e q2 q3) c' s' x ->
    exec_stmt c s (q1 $; If (Unknown 1) q2 q3) c' s' x.
Proof.
  intros. inversion H.
    now constructor.
    subst. eapply XSeq2.
      apply XS1.
      inversion XS0. destruct b; [apply XIf with (b:=0)|apply XIf with (b:=1)]; now try constructor.
Qed.
Lemma ExecTBZ:
  forall {s s' x a c m imm14 b5 op b40 r}
    (O: (op <? 2 = true)%uint63)
    (B: (b5 <? 2 = true)%uint63)
    (B: (b40 <? 16 = true)%uint63)
    (R: (r <? 32 = true)%uint63)
    (IMM: Asm.bounded m 14 = Some imm14)
    (XS: exec_stmt arm8typctx s (arm2il (a*4) (arm_decode ♮(Asm.Encode.TBZ b5 op b40 imm14 r))) c s' x),
    reset_temps s s' = s /\ (x = Some (Addr (ofZ 62 (Z.of_N a + Sint63Axioms.to_Z m) * 4)) \/ x = None).
Proof.
  intros. pose proof IMM. so IMM. case_match; try done. so IMM. apply bounded_toZ in H; try lia. subst'' IMM.
  rewrite decode_TBZ in XS by (apply I2Nlandones_bound || lia).
  replace (Addr _) with (Addr (a ⊗ 4 ⊕ (scast 16 64 (♮(m land ones 14) << 2)))).
  repeat case_match;
  unfold arm2il, arm_tbz2il, arm_tbnz2il, XtoVar in XS; remember (_ mod _); apply forget_cond in XS;
  remember (scast _ _ _); simpl in XS; step XS; case_match; step XS; split; auto.
  subst; unfold scast; do 2 f_equal; rewrite add_sbop, <-(toZ_lsl ♮14 2), H, Z.shiftl_mul_pow2 by lia;
  rewrite toZ_ofZ by (split;simpl;lia); unfold ofZ; rewrite <-Z.add_mod_idemp_l by lia;
  rewrite mod_pow2_toZ; lia.
Qed.
Lemma ExecBcond:
  forall {s s' x a c m imm19 cond}
    (C: (cond <? 16 = true)%uint63)
    (IMM: Asm.bounded m 19 = Some imm19)
    (XS: exec_stmt arm8typctx s (arm2il (a*4) (arm_decode ♮(Asm.Encode.Bcond imm19 cond))) c s' x),
    reset_temps s s' = s /\ (x = Some (Addr (ofZ 62 (Z.of_N a + Sint63Axioms.to_Z m) * 4)) \/ x = None).
Proof.
  intros. pose proof IMM. so IMM. case_match; try done. so IMM. apply bounded_toZ in H; try lia. subst'' IMM.
  rewrite decode_Bcond in XS by (apply I2Nlandones_bound || lia).
  unfold arm2il, arm_b_cond2il in XS. apply forget_cond in XS.
  remember (_ mod _). remember (scast _ _ _). step XS. case_match; step XS; split; auto.
  subst. left. repeat f_equal. unfold scast. rewrite add_sbop, <-(toZ_lsl ♮19 2), H, Z.shiftl_mul_pow2 by lia.
  rewrite toZ_ofZ by (split;simpl;lia). unfold ofZ. rewrite <-Z.add_mod_idemp_l by lia.
  rewrite mod_pow2_toZ; lia.
Qed.

From Stdlib Require Import NArith.   

Lemma plusminus62:
  forall a b
    (A: a < 2^62)
    (B: (b <? 1<<62 = true)%uint63),
  ofZ 62 (Z.of_N a + Sint63.to_Z (b - ♯a)) = ♮b.
Proof.
  intros. unfold ofN, ofZ. rewrite Sint63.to_Z_sub, Sint63.of_Z_spec.
  - rewrite Sint63.cmod_small, Zplus_minus, Sint63.to_Z_cmodwB, Sint63.cmod_small, Z.mod_small; lia.
  - cbn. rewrite Sint63.of_Z_spec, Sint63.to_Z_cmodwB, !Sint63.cmod_small; lia.
Qed.

Lemma ExecADR:
  forall {s s' x a c imm21 m Rd}
    (IMM: Asm.bounded m 21 = Some imm21)
    (R: (Rd <? 32 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.Encode.ADR (imm21:[0,2]) (imm21:[2,19]) Rd))) c s' x),
    reset_temps s s' = s.[arm_varid ♮Rd := ofZ 64 (Z.of_N a + Sint63.to_Z m)] /\ x = None.
Proof.
  intros. pose proof IMM. so IMM. case_match; try done. so IMM. apply bounded_toZ in H; try lia.
  rewrite decode_ADR in XS by (lia || rewrite I2N.inj_xb; apply xbits_bound).
  replace (ofZ _ _) with (a mod 2 ^ 64 ⊕ scast 21 64 (N.lor (♮(imm21:[2, 19]) << 2) ♮(imm21:[0, 2]))).
  unfold arm2il, arm_adr2il, arm_varid in XS. remember (scast _ _ _). remember (_ mod _).
  repeat case_match; step XS; auto.
  rewrite add_sbop. rewrite toZ_mod_pow2 by done. unfold scast. rewrite toZ_ofZ by by eapply signed_range_mono_l, toZ_bounds.
  rewrite <-H.
  unfold ofZ. rewrite <-Zplus_mod_idemp_l, <-(Zplus_mod_idemp_l (Z.of_N _)).
  rewrite mod_pow2_toZ, N2Z.inj_mod by lia. repeat f_equal.
  by rewrite <-IMM, N.lor_comm, !I2N.inj_xb, xbits_0_i, xbits_equiv, (N.mod_small _ (2^21)), recompose_bytes by apply I2Nlandones_bound.
Qed.

Lemma ExecADRP:
  forall {s s' x a c imm21 m Rd}
    (IMM: Asm.bounded m 21 = Some imm21)
    (R: (Rd <? 32 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.Encode.ADRP (imm21:[0,2]) (imm21:[2,19]) Rd))) c s' x),
    reset_temps s s' = s.[arm_varid ♮Rd := ((a mod 2^64) >> 12) << 12 mod 2 ^ 64 ⊕ (scast 33 64 (N.lor (♮(imm21:[2, 19]) << 2) ♮(imm21:[0, 2]) <<
12))] /\ x = None.
Proof.
  intros. pose proof IMM. so IMM. case_match; try done. so IMM. apply bounded_toZ in H; try lia.
  rewrite decode_ADRP in XS by (lia || rewrite I2N.inj_xb; apply xbits_bound).
  unfold arm2il, arm_adrp2il, arm_varid in XS. remember (scast _ _ _). remember (_ mod _).
  repeat case_match; step XS. all: auto.
Qed.

Lemma ExecPOP2:
  forall {s s' c a Xt1 x Xt2}
  (XT: (Xt1 <? 32 =  true)%uint63)
  (XT2:( Xt2 <? 32 = true)%uint63)
  (NEQ: (♮Xt1 =? ♮Xt2) = false)
  (AL  : s R_SP mod 16 = 0)
  (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.POP2 Xt1 Xt2 ))) c s' x),

   reset_temps s s' = s.[arm_varid ♮Xt1 := getmem 64 LittleE 8 (s V_MEM64) (s R_SP)].[arm_varid ♮Xt2 :=
   getmem 64 LittleE 8 (s V_MEM64) (s R_SP ⊕ 8)].[R_SP := s R_SP ⊕ 16] /\ x = None.
Proof.
  intros.
  unfold Asm.POP2,Asm.LDP_post64 in XS. replace (Asm.bounded (asr 16 3) 7) with (Some 2%uint63) in XS.
  simpl in XS. rewrite decode_LDP_STP in XS. simpl in XS. all: try lia.

  unfold arm2il,arm_ldp2il in XS. 
  simpl in XS.
  -- 
  destruct_ltb XT;subst Xt1; cbn in XS;
  
  (
  unfold arm_ldp2il_constr in XS; cbn in XS;
  replace (1 << 3) with 8 in XS by auto;
  remember (_ << _) in XS;
  remember (_ mod _) in XS;
  cbv in Heqn; subst n; replace (16 mod 2^64) with 16 in XS by auto);
  try ( 
  destruct_ltb XT2; subst Xt2; cbn in XS;
  replace (8 << 3) with 64 in XS by auto;
  try (step XS; remember (N.land _ _);
  rewrite AL in Heqn; cbn in Heqn;
  replace (N.lnot 1 1) with 0 in Heqn by reflexivity; rewrite N.land_0_r in Heqn; subst n;
  step XS; destruct XS; simpl arm_varid; assumption); try lia).
  -- cbn. reflexivity.
  Qed.

Lemma ExecPUSH2:
  forall {s s' c a Xt1 x Xt2}
  (XT: (Xt1 <? 32 =  true)%uint63)
  (XT2:( Xt2 <? 32 = true)%uint63)
  (NEQ: (♮Xt1 =? ♮Xt2) = false)
  (AL  : s R_SP mod 16 = 0)
  (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.PUSH2 Xt1 Xt2 ))) c s' x),
let off := (scast 7 64 126 << 3) mod 2 ^ 64 in
  reset_temps s s' =
    s.[V_MEM64 := setmem 64 LittleE 8
                    (setmem 64 LittleE 8 (s V_MEM64) (s R_SP ⊕ off)
                       (s (arm_varid ♮Xt1) mod 2 ^ 64))
                    (s R_SP ⊕ off ⊕ 8)
                    (s (arm_varid ♮Xt2) mod 2 ^ 64)]
     .[R_SP := s R_SP ⊕ off]
  /\ x = None.

Proof.
  intros.
  unfold Asm.PUSH2, Asm.STP_pre64 in XS.
  replace (Asm.bounded (asr 9223372036854775792 3) 7) with (Some 126%uint63) in XS.
  simpl in XS. rewrite decode_LDP_STP in XS. simpl in XS. all: try lia.
  2: cbn; reflexivity.

  unfold arm2il ,arm_stp2il in XS. simpl in XS.
  destruct_ltb XT;subst Xt1; cbn in XS.
  all: unfold arm_stp2il_constr in XS; cbn in XS;
  remember (_ << _);
  replace (1<<3 ) with 8 in XS by auto;
  replace (8*8) with 64 in XS by auto;
  remember (_ mod _) in XS;
  remember (_ mod _) in XS;
  cbv in Heqn;
  destruct_ltb XT2;
  subst Xt2; cbn in XS; try (step XS; remember (N.land _ _); rewrite AL in Heqn2; cbn in Heqn2;
  replace (N.lnot 1 1) with 0 in Heqn2 by reflexivity; rewrite N.land_0_r in Heqn2; subst n2;
  step XS; destruct XS; unfold off;
  rewrite <- Heqn1; try
  assumption); try lia.
  Qed.
   
Lemma tmask_ones:
  forall lsb width
    (L: (lsb <? 1<<5 = true)%uint63)
    (W: (width-1 <? 1<<5 = true)%uint63),
  tmask 1 ♮(lsb + width - 1) ♮lsb false 64 = N.ones ♮width.
Proof.
  intros. unfold tmask, DecodeBitMasks.
  replace (N.pred _) with 6. unfold Replicate. simpl.
  rewrite ones_mod_pow2'. f_equal.
  unfold sbop2. rewrite <-msub_sbop, !N.land_ones, !N.mod_small, msub_sub, xbits_0_i; lia.
  unfold cbits. rewrite N.size_log2, N.pred_succ, N.log2_lor by now rewrite N.lor_eq_0_iff.
  rewrite N.max_l; auto. apply N.log2_le_mono. apply N.lt_le_incl, lnot_bound. lia.
Qed.
Lemma ExecUBFX:
  forall {s s' x a c Rd lsb width}
    (L: (lsb <? 1<<5 = true)%uint63)
    (W: (width-1 <? 1<<5 = true)%uint63)
    (W': (lsb+width-1 <? 1<<5 = true)%uint63)
    (D: (Rd <? 1<<5-1 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.UBFX true Rd Rd lsb width))) c s' x),
  exists n, reset_temps s s' = s.[arm_varid ♮Rd := n] /\ x = None /\ n < 2^♮width.
Proof.
  intros. unfold Asm.UBFX in XS. rewrite decode_UBFX in XS by (simpl;lia).
  unfold arm2il, arm_log_imm2il, arm_ubfm_imm2il in XS. simpl in XS.
  case_match; try lia.
  unfold RORExp, XtoVar, arm_varid in XS.
  remember (_ mod _). cbn in XS.
  remember ♮lsb. remember ♮(_-_). remember (tmask _ _ _ _ _).
  remember (wmask _ _ _ _ _).
  repeat case_match; step XS; subst;
  (repeat eexists; [apply S|rewrite N.land_comm, (tmask_ones _ _ L W); apply land_bound, ones_bound]).
Qed.
Lemma ExecEOR:
  forall {s s' a c x r sft}
    (R: (r <? 1<<5 = true)%uint63)
    (S: (sft <? 1<<6 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.EOR_lsr r r r sft))) c s' x),
  exists n, reset_temps s s' = s.[arm_varid ♮r := n] /\ x = None.
Proof.
  intros. unfold Asm.EOR_lsr in XS. rewrite decode_EOR in XS by lia.
  unfold arm2il, arm_logshft_reg2il, arm_data_r_shiftc in XS. simpl in XS.
  unfold arm_assign_R, ShiftReg, ShiftC, arm64_R, arm_varid in XS. simpl in XS.
  remember (_ mod _). remember ♮sft.
  repeat case_match; step XS; subst x; repeat eexists; apply S0.
Qed.
Lemma ExecNOP:
  forall {s s' a c x}
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.NOP))) c s' x),
  reset_temps s s' = s /\ x = None.
Proof.
  intros. simp (arm_decode _). unfold arm2il in XS. by step XS.
Qed.
Lemma ExecUDF:
  forall {s s' a c x}
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.UDF))) c s' x),
  reset_temps s s' = s /\ x = Some (Raise 4).
Proof.
  intros. simp (arm_decode _). unfold arm2il in XS. by step XS.
Qed.

(* Original (unrewritten) BR / RET words. *)
Lemma decode_BR:
  forall Rn, toN Rn < 2^5 ->
  arm_decode (toN (Asm.Encode.BR Rn)) = ARM_BR (toN Rn).
Proof.
  intros Rn H. assert (R: (Rn <? 32 = true)%uint63) by (I2N.nify; lia). clear H.
  destruct_ltb R; subst Rn; vm_compute; reflexivity.
Qed.

Lemma decode_RET:
  forall Rn, toN Rn < 2^5 ->
  arm_decode (toN (Asm.Encode.RET Rn)) = ARM_RET (toN Rn).
Proof.
  intros Rn H. assert (R: (Rn <? 32 = true)%uint63) by (I2N.nify; lia). clear H.
  destruct_ltb R; subst Rn; vm_compute; reflexivity.
Qed.

(* A field test of Kotori's decoder, as a fact about the bits of ♮n. *)
Lemma xb_eqb:
  forall n i w k, (n:[i, w] =? k)%uint63 = true -> xbits ♮n ♮i (♮i + ♮w) = ♮k.
Proof.
  intros. apply eqb_correct in H. subst k. by rewrite I2N.inj_xb.
Qed.

(* Kotori's decoder fixes every bit of a branch-to-register word except Rn,
   so a word it classifies (and that fits in 32 bits) is the encoding. *)
Lemma word_of_decode_BR:
  forall n Rn
    (D: Kotori.Decode.decode n = Kotori.Decode.BR Rn)
    (B: ♮n < 2^32),
  ♮n = ♮(Asm.Encode.BR Rn) /\ (Rn <? 32 = true)%uint63.
Proof.
  intros.
  unfold Kotori.Decode.decode, Kotori.Decode.dc_b, Kotori.Decode.dc_b_reg,
    Kotori.Decode.dc_dpi, Kotori.Decode.dc_pcr, Kotori.Decode.dc_b_cond,
    Kotori.Decode.dc_b_imm, Kotori.Decode.dc_cb, Kotori.Decode.dc_tb in D.
  cbv zeta in D.
  repeat (case_match; try discriminate).
  injection D as D.
  assert (F1: ♮Rn = xbits ♮n 5 10) by (rewrite <-D, I2N.inj_xb; reflexivity).
  apply xb_eqb in H1, H2, H3, H4, H5, H6.
  assert (F0: xbits ♮n 0 5 = 0) by exact H6.
  assert (F2: xbits ♮n 10 16 = 0) by exact H5.
  assert (F3: xbits ♮n 16 21 = 31) by exact H3.
  assert (F4: xbits ♮n 21 25 = 0) by exact H4.
  assert (F5: xbits ♮n 25 26 = 1) by exact H2.
  assert (F7: xbits ♮n 29 32 = 6) by exact H1.
  (* op0 is 10 or 11, and bit 25 is set, so it is 11 *)
  assert (F6: xbits ♮n 25 29 = 11).
  { apply orb_true_iff in H as [H|H]; apply xb_eqb in H; [|exact H].
    exfalso. change (xbits ♮n 25 29 = 10) in H.
    rewrite (xbits_split 25 26 29), F5 in H by lia.
    apply (f_equal (fun z => N.testbit z 0)) in H.
    rewrite N.lor_spec, N.shiftl_spec_low in H by lia. discriminate. }
  assert (RB: ♮Rn < 32) by (rewrite F1; apply (xbits_bound ♮n 5 10)).
  assert (R: (Rn <? 32 = true)%uint63) by (I2N.nify; lia).
  split; [|exact R].
  rewrite <-(N.mod_small ♮n (2^32)) by exact B. rewrite <-xbits_0_i.
  rewrite (xbits_split 0 5 32), (xbits_split 5 10 32), (xbits_split 10 16 32),
    (xbits_split 16 21 32), (xbits_split 21 25 32), (xbits_split 25 29 32) by lia.
  rewrite F0, <-F1, F2, F3, F4, F6, F7.
  clear - R. destruct_ltb R; subst Rn; vm_compute; reflexivity.
Qed.

Lemma word_of_decode_RET:
  forall n Rn
    (D: Kotori.Decode.decode n = Kotori.Decode.RET Rn)
    (B: ♮n < 2^32),
  ♮n = ♮(Asm.Encode.RET Rn) /\ (Rn <? 32 = true)%uint63.
Proof.
  intros.
  unfold Kotori.Decode.decode, Kotori.Decode.dc_b, Kotori.Decode.dc_b_reg,
    Kotori.Decode.dc_dpi, Kotori.Decode.dc_pcr, Kotori.Decode.dc_b_cond,
    Kotori.Decode.dc_b_imm, Kotori.Decode.dc_cb, Kotori.Decode.dc_tb in D.
  cbv zeta in D.
  repeat (case_match; try discriminate).
  injection D as D.
  assert (F1: ♮Rn = xbits ♮n 5 10) by (rewrite <-D, I2N.inj_xb; reflexivity).
  repeat match goal with H: (_ =? _)%uint63 = true |- _ => apply xb_eqb in H end.
  assert (F0: xbits ♮n 0 5 = 0) by assumption.
  assert (F2: xbits ♮n 10 16 = 0) by assumption.
  assert (F3: xbits ♮n 16 21 = 31) by assumption.
  assert (F4: xbits ♮n 21 25 = 2) by assumption.
  assert (F5: xbits ♮n 25 26 = 1) by assumption.
  assert (F7: xbits ♮n 29 32 = 6) by assumption.
  assert (F6: xbits ♮n 25 29 = 11).
  { match goal with H0: (_ || _)%bool = true |- _ =>
      apply orb_true_iff in H0 as [H0|H0]; apply xb_eqb in H0; [|exact H0];
      exfalso; change (xbits ♮n 25 29 = 10) in H0;
      rewrite (xbits_split 25 26 29), F5 in H0 by lia;
      apply (f_equal (fun z => N.testbit z 0)) in H0;
      rewrite N.lor_spec, N.shiftl_spec_low in H0 by lia; discriminate
    end. }
  assert (RB: ♮Rn < 32) by (rewrite F1; apply (xbits_bound ♮n 5 10)).
  assert (R: (Rn <? 32 = true)%uint63) by (I2N.nify; lia).
  split; [|exact R].
  rewrite <-(N.mod_small ♮n (2^32)) by exact B. rewrite <-xbits_0_i.
  rewrite (xbits_split 0 5 32), (xbits_split 5 10 32), (xbits_split 10 16 32),
    (xbits_split 16 21 32), (xbits_split 21 25 32), (xbits_split 25 29 32) by lia.
  rewrite F0, <-F1, F2, F3, F4, F6, F7.
  clear - R. destruct_ltb R; subst Rn; vm_compute; reflexivity.
Qed.

Lemma ExecBR:
  forall {s s' x a c Rn}
    (R: (Rn <? 32 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.Encode.BR Rn))) c s' x),
  reset_temps s s' = s /\ x = Some (Addr (s (arm_varid ♮Rn))).
Proof.
  intros. rewrite decode_BR in XS by (I2N.nify; lia).
  unfold arm2il, arm_br2il in XS.
  destruct_ltb R; subst Rn; step XS; (split; [exact S | rewrite X; reflexivity]).
Qed.

Lemma ExecRET:
  forall {s s' x a c Rn}
    (R: (Rn <? 32 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.Encode.RET Rn))) c s' x),
  reset_temps s s' = s /\ x = Some (Addr (s (arm_varid ♮Rn))).
Proof.
  intros. rewrite decode_RET in XS by (I2N.nify; lia).
  unfold arm2il, arm_ret2il in XS.
  destruct_ltb R; subst Rn; step XS; (split; [exact S | rewrite X; reflexivity]).
Qed.

(* Original (unrewritten) BLR words; BLR Xn lxor (1<<21) is BR Xn. *)
Lemma decode_BLR:
  forall Rn, toN Rn < 2^5 ->
  arm_decode (toN (Asm.Encode.BLR Rn)) = ARM_BLR (toN Rn).
Proof.
  intros Rn H. assert (R: (Rn <? 32 = true)%uint63) by (I2N.nify; lia). clear H.
  destruct_ltb R; subst Rn; vm_compute; reflexivity.
Qed.

Lemma BLR_lxor_BR:
  forall Rn, (Rn <? 32 = true)%uint63 ->
  (Asm.Encode.BLR Rn lxor (1 << 21))%uint63 = Asm.Encode.BR Rn.
Proof.
  intros Rn R. destruct_ltb R; subst Rn; vm_compute; reflexivity.
Qed.

Lemma ExecBLR:
  forall {s s' x a c Rn}
    (R: (Rn <? 32 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.Encode.BLR Rn))) c s' x),
  exists v, reset_temps s s' = s.[R_X30 := v] /\ v < 2^64 /\ x = Some (Addr (s (arm_varid ♮Rn))).
Proof.
  intros. rewrite decode_BLR in XS by (I2N.nify; lia).
  unfold arm2il, arm_blr2il in XS.
  remember (a mod 2 ^ 64) as pc in XS.
  destruct_ltb R; subst Rn; step XS.
  all: exists (pc ⊕ 4); split; [exact S|split; [apply N.mod_lt; discriminate|rewrite X; reflexivity]].
Qed.

Lemma word_of_decode_BLR:
  forall n Rn
    (D: Kotori.Decode.decode n = Kotori.Decode.BLR Rn)
    (B: ♮n < 2^32),
  ♮n = ♮(Asm.Encode.BLR Rn) /\ (Rn <? 32 = true)%uint63.
Proof.
  intros.
  unfold Kotori.Decode.decode, Kotori.Decode.dc_b, Kotori.Decode.dc_b_reg,
    Kotori.Decode.dc_dpi, Kotori.Decode.dc_pcr, Kotori.Decode.dc_b_cond,
    Kotori.Decode.dc_b_imm, Kotori.Decode.dc_cb, Kotori.Decode.dc_tb in D.
  cbv zeta in D.
  repeat (case_match; try discriminate).
  injection D as D.
  assert (F1: ♮Rn = xbits ♮n 5 10) by (rewrite <-D, I2N.inj_xb; reflexivity).
  repeat match goal with H: (_ =? _)%uint63 = true |- _ => apply xb_eqb in H end.
  assert (F0: xbits ♮n 0 5 = 0) by assumption.
  assert (F2: xbits ♮n 10 16 = 0) by assumption.
  assert (F3: xbits ♮n 16 21 = 31) by assumption.
  assert (F4: xbits ♮n 21 25 = 1) by assumption.
  assert (F5: xbits ♮n 25 26 = 1) by assumption.
  assert (F7: xbits ♮n 29 32 = 6) by assumption.
  assert (F6: xbits ♮n 25 29 = 11).
  { match goal with H0: (_ || _)%bool = true |- _ =>
      apply orb_true_iff in H0 as [H0|H0]; apply xb_eqb in H0; [|exact H0];
      exfalso; change (xbits ♮n 25 29 = 10) in H0;
      rewrite (xbits_split 25 26 29), F5 in H0 by lia;
      apply (f_equal (fun z => N.testbit z 0)) in H0;
      rewrite N.lor_spec, N.shiftl_spec_low in H0 by lia; discriminate
    end. }
  assert (RB: ♮Rn < 32) by (rewrite F1; apply (xbits_bound ♮n 5 10)).
  assert (R: (Rn <? 32 = true)%uint63) by (I2N.nify; lia).
  split; [|exact R].
  rewrite <-(N.mod_small ♮n (2^32)) by exact B. rewrite <-xbits_0_i.
  rewrite (xbits_split 0 5 32), (xbits_split 5 10 32), (xbits_split 10 16 32),
    (xbits_split 16 21 32), (xbits_split 21 25 32), (xbits_split 25 29 32) by lia.
  rewrite F0, <-F1, F2, F3, F4, F6, F7.
  clear - R. destruct_ltb R; subst Rn; vm_compute; reflexivity.
Qed.

(* Exec lemmas in the shape produced by Asm.ADR / Asm.ADRP words: used by
   ExecIimm in Soundness. ExecADR/ExecADRP above use the byte-distance form. *)
(* Legacy shape: matches Asm.ADR's word, Encode.ADR (imm land 3) imm19 Rd. *)
Lemma ExecADR19:
  forall {s s' x a c imm19 m Rd low}
    (IMM: Asm.bounded m 19 = Some imm19)
    (L: (low <? 4 = true)%uint63)
    (R: (Rd <? 32 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il (a*4) (arm_decode ♮(Asm.Encode.ADR low imm19 Rd))) c s' x),
    reset_temps s s' = s.[arm_varid ♮Rd := ofZ 62 (Z.of_N a + Sint63.to_Z m) * 4 + ♮low] /\ x = None.
Proof.
  intros. pose proof IMM. so IMM. case_match; try done. so IMM. apply bounded_toZ in H; try lia.
  rewrite decode_ADR in XS by (lia || subst; apply I2Nlandones_bound).
  replace (_ + ♮low) with (a ⊗ 4 ⊕ scast 21 64 (N.lor (♮imm19 << 2) ♮low)).
  unfold arm2il, arm_adr2il, arm_varid in XS. remember (scast _ _ _). remember (_ mod _).
  repeat case_match; step XS; auto.
  rewrite add_sbop.
  unfold scast. rewrite toZ_ofZ by by eapply signed_range_mono_l, toZ_bounds.
  rewrite <-H.
  rewrite toZ_lor.
  rewrite <-(toZ_lsl ♮19 2).
  rewrite (proj1 (toZ_nonneg 21 _)) by (repeat simp (2^_); lia).
  rewrite <-numbers.Z.add_nocarry_lor.
  rewrite Z.shiftl_mul_pow2 by lia.
  unfold ofZ. rewrite <-Z.add_mod_idemp_l, mod_pow2_toZ by lia. lia.
  remember (Z.of_N (_ mod _)).
  replace z with (z mod 2^2)%Z by lia.
  rewrite <-Z.land_ones by lia. clear. prove_Zeq_bitwise.
Qed.

(* The ADRP result in the old (page-index) shape equals the current formula. *)
Lemma adrp_old_new:
  forall a m imm21
    (IMM: Asm.bounded m 21 = Some imm21),
  ofZ 52 (Z.of_N (a>>10) + Sint63.to_Z m) << 12 =
  (a ⊗ 4) >> 12 << 12 mod 2 ^ 64 ⊕
    (scast 33 64 (N.lor (♮(imm21:[2, 19]) << 2) ♮(imm21:[0, 2]) << 12)).
Proof.
  intros.
  rewrite N.Div0.add_mod_idemp_l by lia.
  pose proof IMM. apply bounded_toZ in H; try lia. unfold scast.
  rewrite <-(toZ_lsl ♮21 12), !I2N.inj_xb, N.lor_comm, <-xbits_split, xbits_0_i by lia.
  repeat so IMM. rewrite (N.mod_small _ (2^21)) by (subst;apply I2Nlandones_bound).
  rewrite H, ofZ_shiftl, N.Div0.add_mod_idemp_r.
  rewrite !N.shiftl_mul_pow2, <-N.mul_add_distr_r.
  rewrite <-N.Div0.mul_mod_idemp_l, add_sbop.
  rewrite toZ_ofZ by (split; simpl; lia).
  rewrite (proj1 (toZ_nonneg _ _)) by (rewrite N.shiftr_div_pow2; simp (2^N.pred _); lia).
  rewrite !N.shiftr_div_pow2. unfold ofZ. lia.
Qed.

Lemma ExecADRP19:
  forall {s s' x a c m imm21 Rd}
    (IMM: Asm.bounded m 21 = Some imm21)
    (R: (Rd <? 32 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il (a*4) (arm_decode ♮(Asm.Encode.ADRP (imm21:[0,2]) (imm21:[2,19]) Rd))) c s' x),
    reset_temps s s' = s.[arm_varid ♮Rd := ofZ 52 (Z.of_N (a>>10) + Sint63.to_Z m) << 12] /\ x = None.
Proof.
  intros. apply (ExecADRP IMM R) in XS as [S' X']. split; [|exact X'].
  rewrite S'. f_equal. symmetry. apply adrp_old_new, IMM.
Qed.

(* 6-bit-range versions of tmask_ones / ExecUBFX (lsb, width up to 63). *)
Lemma tmask_ones6:
  forall lsb width
    (L: (lsb <? 1<<6 = true)%uint63)
    (W: (width-1 <? 1<<6 = true)%uint63)
    (W': (lsb+width-1 <? 1<<6 = true)%uint63),
  tmask 1 ♮(lsb + width - 1) ♮lsb false 64 = N.ones ♮width.
Proof.
  intros. unfold tmask, DecodeBitMasks.
  replace (N.pred _) with 6. unfold Replicate. simpl.
  rewrite ones_mod_pow2'. f_equal.
  unfold sbop2. rewrite <-msub_sbop, !N.land_ones, !N.mod_small, msub_sub, xbits_0_i; lia.
  unfold cbits. rewrite N.size_log2, N.pred_succ, N.log2_lor by now rewrite N.lor_eq_0_iff.
  rewrite N.max_l; auto. apply N.log2_le_mono. apply N.lt_le_incl, lnot_bound. lia.
Qed.
Lemma ExecUBFX6:
  forall {s s' x a c Rd lsb width}
    (L: (lsb <? 1<<6 = true)%uint63)
    (W: (width-1 <? 1<<6 = true)%uint63)
    (W': (lsb+width-1 <? 1<<6 = true)%uint63)
    (D: (Rd <? 1<<5-1 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.UBFX true Rd Rd lsb width))) c s' x),
  exists n, reset_temps s s' = s.[arm_varid ♮Rd := n] /\ x = None /\ n < 2^♮width.
Proof.
  intros. unfold Asm.UBFX in XS. rewrite decode_UBFX in XS by (simpl;lia).
  unfold arm2il, arm_log_imm2il, arm_ubfm_imm2il in XS. simpl in XS.
  case_match; try lia.
  unfold RORExp, XtoVar, arm_varid in XS.
  remember (_ mod _). cbn in XS.
  remember ♮lsb. remember ♮(_-_). remember (tmask _ _ _ _ _).
  remember (wmask _ _ _ _ _).
  repeat case_match; step XS; subst;
  (repeat eexists; [apply S|rewrite N.land_comm, (tmask_ones6 _ _ L W W'); apply land_bound, ones_bound]).
Qed.

(* Instructions of the hash-table lookup sequence. *)
(* PUSH2 Xt1, XZR either raises the alignment exception or falls through. *)
Lemma ExecPUSH2g:
  forall {s s' c a Xt1 x}
    (XT: (Xt1 <? 2 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.PUSH2 Xt1 31))) c s' x),
  x = Some (Raise 0) \/ x = None.
Proof.
  intros. unfold Asm.PUSH2, Asm.STP_pre64 in XS.
  replace (Asm.bounded (asr 9223372036854775792 3) 7) with (Some 126%uint63) in XS by (cbn; reflexivity).
  simpl in XS. rewrite decode_LDP_STP in XS. simpl in XS. all: try lia.
  unfold arm2il, arm_stp2il in XS. simpl in XS.
  destruct_ltb XT; subst Xt1; cbn in XS.
  all: unfold arm_stp2il_constr in XS; cbn in XS.
  all: remember (scast 7 64 126 << 3 mod 2 ^ 64) as off in XS.
  all: remember (a mod 2 ^ 64) as pc in XS.
  all: step XS.
  all: remember (N.land _ _) as cnd in XS.
  all: destruct cnd as [|p]; cbn in XS; repeat step XS.
  all: try (left; assumption). all: try (right; assumption).
  all: right; exact (proj2 (proj1 XS)).
Qed.
(* POP2 Xt1, XZR either raises the alignment exception or updates exactly the
   two destination registers and SP; it never branches. *)
Lemma ExecPOP2g:
  forall {s s' c a Xt1 x}
    (XT: (Xt1 <? 2 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il a (arm_decode ♮(Asm.POP2 Xt1 31))) c s' x),
  x = Some (Raise 0) \/
  exists A B C, reset_temps s s' = s.[arm_varid ♮Xt1 := A].[arm_varid 31 := B].[R_SP := C] /\ x = None.
Proof.
  intros. unfold Asm.POP2, Asm.LDP_post64 in XS.
  replace (Asm.bounded (asr 16 3) 7) with (Some 2%uint63) in XS.
  simpl in XS. rewrite decode_LDP_STP in XS. simpl in XS. all: try lia.
  2: cbn; reflexivity.
  unfold arm2il, arm_ldp2il in XS. simpl in XS.
  destruct_ltb XT; subst Xt1; cbn in XS.
  all: unfold arm_ldp2il_constr in XS; cbn in XS.
  all: replace (1 << 3) with 8 in XS by auto.
  all: remember (a mod 2 ^ 64) as pc in XS.
  all: replace (scast 7 64 2 << 3 mod 2 ^ 64) with 16 in XS by (vm_compute; reflexivity).
  all: step XS.
  all: remember (N.land _ _) as cnd in XS.
  all: destruct cnd as [|p]; cbn in XS; repeat step XS.
  all: first [ (left; assumption) | (right; eexists _, _, _; exact (proj1 XS)) ].
Qed.

(* Index of a general-purpose register variable; inverts arm_varid below 32
   (register 31 is XZR, which has index 31). *)
Definition varid_idx v :=
  match v with
  | R_X0 => 0 | R_X1 => 1 | R_X2 => 2 | R_X3 => 3 | R_X4 => 4 | R_X5 => 5 | R_X6 => 6 | R_X7 => 7
  | R_X8 => 8 | R_X9 => 9 | R_X10 => 10 | R_X11 => 11 | R_X12 => 12 | R_X13 => 13 | R_X14 => 14 | R_X15 => 15
  | R_X16 => 16 | R_X17 => 17 | R_X18 => 18 | R_X19 => 19 | R_X20 => 20 | R_X21 => 21 | R_X22 => 22 | R_X23 => 23
  | R_X24 => 24 | R_X25 => 25 | R_X26 => 26 | R_X27 => 27 | R_X28 => 28 | R_X29 => 29 | R_X30 => 30
  | _ => 31
  end.
Lemma varid_idx_inv:
  forall r, (r <? 32 = true)%uint63 -> varid_idx (arm_varid ♮r) = ♮r.
Proof. intros r R. destruct_ltb R; subst r; reflexivity. Qed.
Lemma varid_neq:
  forall r1 r2, (r1 <? 32 = true)%uint63 -> (r2 <? 32 = true)%uint63 ->
  r1 <> r2 -> arm_varid ♮r1 <> arm_varid ♮r2.
Proof.
  intros r1 r2 R1 R2 NE E. apply (f_equal varid_idx) in E.
  rewrite !varid_idx_inv in E by assumption. apply NE. I2N.nify. lia.
Qed.
Lemma varid_neq_v:
  forall r v, (r <? 31 = true)%uint63 -> varid_idx v = 31 -> arm_varid ♮r <> v.
Proof.
  intros r v R V E. subst v. rewrite varid_idx_inv in V by lia. I2N.nify. lia.
Qed.
