From Kotori Require Import Decode proof.Util proof.I2N proof.Decode proof.Exec.
From Picinae Require Import armv8 armv8_lifter_rework.
From Stdlib Require Import NArith.
Import ARM8Arch.

(* Connect the minimal decoder to Picinae's decoder and execution semantics.
   An instruction classified as ignore can fall through or raise an exception,
   but cannot explicitly transfer control to an address. *)
Definition nonbranch i : Prop :=
  match i with
  | ARM_B_COND _ _ | ARM_BR _ | ARM_BLR _ | ARM_RET _
  | ARM_B _ | ARM_BL _ | ARM_CBZ _ _ _ | ARM_CBNZ _ _ _
  | ARM_TBZ _ _ _ _ | ARM_TBNZ _ _ _ _ => False
  | _ => True
  end.
Local Ltac unfold_head a :=
  match a with
  | ?x ?y => unfold_head x
  | _ => unfold a
  end.
Local Ltac instruction_head i :=
  lazymatch i with ?f ?x => instruction_head f | _ => i end.
Local Ltac nonbranch_decoder :=
  repeat match goal with |- nonbranch ?i =>
    first [let h := instruction_head i in is_constructor h; exact I |
      unfold_head i |
      lazymatch i with (if ?b then _ else _) => destruct b eqn:? end]
  end.
Lemma nonbranch_dp_imm : forall n, nonbranch (dp_imm n).
Proof. intros. nonbranch_decoder. Qed.
Lemma nonbranch_dp_reg : forall n, nonbranch (dp_reg n).
Proof. intros. nonbranch_decoder. Qed.
Lemma nonbranch_load_store : forall n, nonbranch (load_store n).
Proof. intros. nonbranch_decoder. Qed.
Lemma nonbranch_dp_fp_simd : nonbranch dp_fp_simd.
Proof. intros. nonbranch_decoder. Qed.
Lemma land_xbits_full : forall n a b,
 N.land (xbits n a b) (N.ones (b-a)) = xbits n a b.
Proof. intros. rewrite N.land_ones. apply N.mod_small, xbits_bound. Qed.
Local Ltac full_masks :=
 repeat match goal with
 | |- context [N.land (xbits ?n ?a ?b) ?m] =>
   let w := eval compute in (b-a)%N in
   let v := eval compute in (N.ones w) in
   unify m v;
   change (N.land (xbits n a b) m) with (N.land (xbits n a b) (N.ones (b-a)));
   rewrite land_xbits_full
 end.
Lemma nonbranch_cond_ignore : forall n,
 Decode.dc_b_cond n = Decode.ignore -> nonbranch (cond_branch (toN n)).
Proof.
 intros n H. unfold Decode.dc_b_cond in H.
 rewrite <- !I2N.inj_eqb, !I2N.inj_xb in H.
 repeat match type of H with
 | context [toN ?c] => tryif is_var c then fail else idtac; let v := eval vm_compute in (toN c) in change (toN c) with v in H
 | context [(?a + ?b)%N] => is_ground a; is_ground b; let v := eval compute in (a+b)%N in change (a+b)%N with v in H
 end.
 unfold cond_branch. full_masks. nonbranch_decoder. unfold nonbranch.
 assert (G : (xbits (toN n) 4 5 =? 0)%N && (xbits (toN n) 24 25 =? 0)%N = true) by (rewrite andb_comm; exact Heqb).
 rewrite G in H. discriminate.
Qed.
Lemma nonbranch_reg_ignore : forall n,
 Decode.dc_b_reg n = Decode.ignore -> nonbranch (uncond_b_reg (toN n)).
Proof.
 intros n H. unfold Decode.dc_b_reg in H.
 rewrite <- !I2N.inj_eqb, !I2N.inj_xb in H.
 repeat match type of H with
 | context [toN ?c] => tryif is_var c then fail else idtac; let v := eval vm_compute in (toN c) in change (toN c) with v in H
 | context [(?a + ?b)%N] => is_ground a; is_ground b; let v := eval compute in (a+b)%N in change (a+b)%N with v in H
 end.
 unfold uncond_b_reg. full_masks.
 nonbranch_decoder.
 all: unfold nonbranch; repeat match goal with E : _ && _ = true |- _ => apply andb_true_iff in E as [? ?] end.
 all: repeat match goal with E : ?b = true |- _ => progress rewrite E in H end.
 all: repeat match goal with E : (_ =? _)%N = true |- _ => apply N.eqb_eq in E end.
 all: repeat match goal with E : xbits _ _ _ = _ |- _ => progress rewrite E in H end.
 all: discriminate H.
Qed.
Lemma nonbranch_exc_gen : forall n, nonbranch (exc_gen n).
Proof. intros; nonbranch_decoder. Qed.
Lemma nonbranch_hints : forall n, nonbranch (hints n).
Proof. intros; nonbranch_decoder. Qed.
Lemma nonbranch_barriers : forall n, nonbranch (barriers n).
Proof. intros; nonbranch_decoder. Qed.
Lemma nonbranch_pstate : forall n, nonbranch (pstate n).
Proof. intros; nonbranch_decoder. Qed.
Lemma nonbranch_sys_inst : forall n, nonbranch (sys_inst n).
Proof. intros; nonbranch_decoder. Qed.
Lemma nonbranch_sys_reg_move : forall n, nonbranch (sys_reg_move n).
Proof. intros; nonbranch_decoder. Qed.
Local Ltac nify_constants H :=
 repeat match type of H with
 | context [toN ?c] => tryif is_var c then fail else idtac;
   let v := eval vm_compute in (toN c) in change (toN c) with v in H
 | context [(?a + ?b)%N] => is_ground a; is_ground b;
   let v := eval compute in (a+b)%N in change (a+b)%N with v in H
 end.
Local Ltac decoder_constants :=
 repeat match goal with
 | |- context [N.land ?x ?y] =>
   let hx := instruction_head x in is_constructor hx;
   let hy := instruction_head y in is_constructor hy;
   let v := eval vm_compute in (N.land x y) in change (N.land x y) with v
 | |- context [N.mul ?x ?y] =>
   let hx := instruction_head x in is_constructor hx;
   let hy := instruction_head y in is_constructor hy;
   let v := eval vm_compute in (N.mul x y) in change (N.mul x y) with v
 | |- context [N.eqb ?x ?y] =>
   let hx := instruction_head x in is_constructor hx;
   let hy := instruction_head y in is_constructor hy;
   let v := eval vm_compute in (N.eqb x y) in change (N.eqb x y) with v
 end; cbv beta iota zeta delta [andb orb negb].
Lemma branch_ignore : forall n, Decode.dc_b n=Decode.ignore -> nonbranch (branch_exc (toN n)).
Proof.
 intros n H. unfold Decode.dc_b in H.
 rewrite <-!I2N.inj_eqb, !I2N.inj_xb in H. nify_constants H.
 pose proof (xbits_bound (toN n) 29 32) as HI.
 pose proof (xbits_bound (toN n) 25 26) as BT.
 remember (xbits (toN n) 29 32) as hi eqn:HIGH.
 remember (xbits (toN n) 25 26) as bt eqn:BIT.
 assert (MASK : N.land (xbits (toN n) 12 26) 8192 = (bt*8192)%N).
 { assert (B : bt=0%N \/ bt=1%N) by (change (bt<2)%N in BT;lia).
   destruct B as [B|B]; rewrite B in *.
   - apply N.eqb_eq, (bit_mask_decode1 (toN n) 12 13 26); [lia|]. change (N.odd (xbits (toN n) 25 26)=false). rewrite <-BIT. reflexivity.
   - apply N.eqb_eq, (bit_mask_decode_pos (toN n) 12 13 26); [lia|]. change (N.odd (xbits (toN n) 25 26)=true). rewrite <-BIT. reflexivity. }
 assert (HIC : hi=0%N \/ hi=1%N \/ hi=2%N \/ hi=3%N \/ hi=4%N \/ hi=5%N \/ hi=6%N \/ hi=7%N) by (change (hi<8)%N in HI;lia).
 assert (BTC : bt=0%N \/ bt=1%N) by (change (bt<2)%N in BT;lia).
 unfold branch_exc. full_masks. rewrite <-HIGH, MASK, !N.land_0_r, !andb_true_r.
 destruct HIC as [HC|[HC|[HC|[HC|[HC|[HC|[HC|HC]]]]]]]; rewrite HC in *; destruct BTC as [BC|BC]; rewrite BC in *;
 cbn -[nonbranch dc_b_cond dc_b_reg dc_b_imm dc_cb dc_tb xb exc_gen hints barriers pstate sys_inst sys_reg_move cond_branch uncond_b_reg uncond_b_imm comp_and_b test_and_b toN xbits] in H |- *;
 try discriminate H.
 all: decoder_constants.
 all: try (unfold dc_b_imm in H; destruct (n:[31] =? 0)%uint63; discriminate H).
 all: repeat first [
   match goal with |- nonbranch ?i => let h := instruction_head i in is_constructor h; exact I end |
   match goal with |- nonbranch (cond_branch ?x) => apply nonbranch_cond_ignore; exact H end |
   match goal with |- nonbranch (uncond_b_reg ?x) => apply nonbranch_reg_ignore; exact H end |
   match goal with |- nonbranch (if ?b then _ else _) => destruct b end |
   match goal with |- nonbranch (exc_gen ?x) => exact (nonbranch_exc_gen x) end |
   match goal with |- nonbranch (hints ?x) => exact (nonbranch_hints x) end |
   match goal with |- nonbranch (barriers ?x) => exact (nonbranch_barriers x) end |
   match goal with |- nonbranch (pstate ?x) => exact (nonbranch_pstate x) end |
   match goal with |- nonbranch (sys_inst ?x) => exact (nonbranch_sys_inst x) end |
   match goal with |- nonbranch (sys_reg_move ?x) => exact (nonbranch_sys_reg_move x) end ].
Qed.
Lemma nonbranch_decode_ignore : forall n,
 Decode.decode n=Decode.ignore -> nonbranch (arm_decode (toN n)).
Proof.
 intros n H. unfold Decode.decode in H.
 rewrite <-!I2N.inj_eqb, !I2N.inj_xb in H. nify_constants H.
 pose proof (xbits_bound (toN n) 25 29) as B.
 remember (xbits (toN n) 25 29) as op eqn:OP.
 assert (OPS : op=0%N \/ op=1%N \/ op=2%N \/ op=3%N \/
 op=4%N \/ op=5%N \/ op=6%N \/ op=7%N \/
 op=8%N \/ op=9%N \/ op=10%N \/ op=11%N \/
 op=12%N \/ op=13%N \/ op=14%N \/ op=15%N) by (change (op<16)%N in B;lia).
 unfold arm_decode. full_masks. rewrite <-OP.
 destruct OPS as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]; rewrite E in *;
 cbn -[nonbranch dc_b dc_dpi dp_imm branch_exc load_store dp_reg dp_fp_simd toN xbits] in H.
 all: decoder_constants.
 all: first [
 match goal with |- nonbranch UDF => exact I end |
 match goal with |- nonbranch (dp_imm ?x) => exact (nonbranch_dp_imm x) end |
 match goal with |- nonbranch (branch_exc ?x) => apply branch_ignore; exact H end |
 match goal with |- nonbranch (load_store ?x) => exact (nonbranch_load_store x) end |
 match goal with |- nonbranch (dp_reg ?x) => exact (nonbranch_dp_reg x) end |
 match goal with |- nonbranch dp_fp_simd => exact nonbranch_dp_fp_simd end].
Qed.

Fixpoint nojumps q : Prop :=
  match q with
  | Jmp _ => False
  | Seq q1 q2 | If _ q1 q2 => nojumps q1 /\ nojumps q2
  | Rep _ q => nojumps q
  | _ => True
  end.
Lemma nojumps_iter : forall n q, nojumps q -> nojumps (N.iter n (Seq q) Nop).
Proof.
  intros n q NJ. induction n using N.peano_ind.
  - exact I.
  - rewrite N.iter_succ. simpl. tauto.
Qed.
Lemma nojumps_exec :
  forall c s q c' s' x (XS: exec_stmt c s q c' s' x),
  nojumps q -> match x with Some (Addr _) => False | _ => True end.
Proof.
  intros c s q c' s' x XS. induction XS; simpl; intros NJ; try tauto.
  - destruct b; simpl in IHXS; tauto.
  - apply IHXS, nojumps_iter, NJ.
Qed.
Lemma nonbranch_arm2il :
  forall a i, nonbranch i -> nojumps (arm2il a i).
Proof.
  intros a i NB. destruct i; cbn [nonbranch] in NB; try contradiction;
  repeat first [done | split | case_match |
    match goal with |- nojumps ?q => unfold_head q; cbn [nojumps] end].
Qed.
