From coqutil Require Import Tactics.fwd autoforward.
From Stdlib Require Import ZArith ZifySint63.
From stdpp Require Import list list_basics.
From Kotori Require Import Rewrite proof.Util proof.Rewrite proof.Decode proof.Exec proof.ControlFlow proof.I2N.
From Picinae Require Import armv8 armv8_lifter_rework.
Import ARM8Arch.

Unset Default Goal Selector.
Lemma N_land_shiftl:
  forall a b c, N.land a (b << c) = N.land (a >> c) b << c.
Proof.
  intros. rewrite N.shiftl_land. apply N.bits_inj. intro.
  rewrite !N.land_spec. destruct (N.lt_ge_cases n c).
  - by rewrite N.shiftl_spec_low, !andb_false_r.
  - rewrite !N.shiftl_spec_high, N.shiftr_spec by lia. repeat f_equal. lia.
Qed.
Lemma rbits_0:
  forall n i m w, xbits n i (i+w) = 0 -> rbits n i m w = N.lor n ((m mod 2^w) << i).
Proof.
  unfold rbits, xbits. intros. f_equal.
  rewrite ldiff_sub. eqapply (N.sub_0_r n).
  replace (_-_) with w in H by lia.
  by rewrite N_land_shiftl, N.land_ones, H, N.shiftl_0_l.
Qed.
Lemma rbits_0':
  forall n i m w, xbits n i (i+w) = 0 -> rbits n i m w = n + ((m mod 2^w) << i).
Proof.
  intros. rewrite rbits_0, lor_plus; auto.
  rewrite <-shiftr_mod_xbits in H.
  by rewrite N_land_shiftl, <-N_land_mod_pow2_move, H, N.land_0_l, N.shiftl_0_l.
Qed.
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
Lemma plusminus52:
  forall a b
    (A: a < 2^52)
    (B: (b <? 1<<52 = true)%uint63),
  ofZ 52 (Z.of_N a + Sint63.to_Z (b - ♯a)) = ♮b.
Proof.
  intros. unfold ofN, ofZ. rewrite Sint63.to_Z_sub, Sint63.of_Z_spec.
  - rewrite Sint63.cmod_small, Zplus_minus, Sint63.to_Z_cmodwB, Sint63.cmod_small, Z.mod_small; lia.
  - cbn. rewrite Sint63.of_Z_spec, Sint63.to_Z_cmodwB, !Sint63.cmod_small; lia.
Qed.
Lemma recompose_bytes':
  forall x w, (x >> w) << w + N.land x (N.ones w) = x.
Proof.
  intros. rewrite <-N.ldiff_ones_r.
  rewrite <-lor_plus.
  apply N.lor_ldiff_and.
  by rewrite (N.land_comm x), N.land_assoc, N.land_ldiff.
Qed.
Lemma landones:
  forall i j, (j <? 63 = true -> i land ones j <? 1<<j = true)%uint63.
Proof.
  intros. nify. rewrite I2N.inj_ones, N.shiftl_mul_pow2, N.mul_1_l.
  rewrite !N.mod_small. rewrite N.land_ones. lia.
  apply N.pow_lt_mono_r; lia.
  eapply N.lt_trans. apply ones_bound. apply N.pow_lt_mono_r; lia.
Qed.
Lemma land16:
  forall x, (x land 65535 = x mod 65536)%uint63.
Proof.
  intro. I2N.nify. change ♮65535 with (N.ones 16). rewrite N.land_ones. lia.
Qed.
Lemma land3:
  forall x, (x land 3 = x mod 4)%uint63.
Proof.
  intro. I2N.nify. change ♮3 with (N.ones 2). rewrite N.land_ones. lia.
Qed.

(* The new ExecMovk result: replace the 16-bit field at bit s. *)
Lemma movk_val:
  forall v w s,
    v < 2^64 -> w < 2^16 ->
    N.lor (N.land v (N.lnot (N.ones 16 << s) 64)) (w << s) =
    v - N.land v (N.ones 16 << s) + (w << s).
Proof.
  intros v w s V W.
  rewrite <-(ldiff_land_low2 v (N.ones 16 << s) 64 V).
  rewrite lor_plus, ldiff_sub; [reflexivity|].
  apply N.bits_inj_0. intro n.
  rewrite N.land_spec, N.ldiff_spec.
  destruct (N.lt_ge_cases n s) as [LT|GE].
  - rewrite !(N.shiftl_spec_low _ _ _ LT). by destruct (N.testbit v n).
  - rewrite (N.shiftl_spec_high' _ _ _ GE), (N.shiftl_spec_high' _ _ _ GE).
    destruct (N.lt_ge_cases (n - s) 16) as [L16|G16].
    + rewrite (N.ones_spec_low _ _ L16).
      by destruct (N.testbit v n), (N.testbit w (n - s)).
    + rewrite <-(N.mod_small w (2^16) W), N.mod_pow2_bits_high by exact G16.
      by rewrite andb_false_r.
Qed.

(* arithmetic form of a MOVK update at bit s *)
Lemma movk_arith:
  forall v w s,
    v < 2^64 -> w < 2^16 ->
    N.lor (N.land v (N.lnot (N.ones 16 << s) 64)) (w << s) =
    v - ((v / 2^s) mod 2^16) * 2^s + w * 2^s.
Proof.
  intros v w s V W. rewrite movk_val by assumption.
  rewrite N_land_shiftl, N.land_ones, N.shiftr_div_pow2, !N.shiftl_mul_pow2. reflexivity.
Qed.

(* ADRP (page) then MOVK #(imm land 0xffff), LSL 0 *)
Lemma movk_adrp:
  forall X: int,
  N.lor (N.land (♮(X >> 12) << 12) (N.lnot (N.ones 16 << (♮0 << 4)) 64))
        (♮(X land 65535) << (♮0 << 4)) = ♮X.
Proof.
  intros X. assert (XB: ♮X < 2^63) by lia.
  replace (♮0%uint63 << 4) with 0 by reflexivity.
  rewrite movk_arith.
  - rewrite land16. I2N.nify. change ♮12 with 12. change ♮65536 with 65536.
    rewrite !N.shiftr_div_pow2, !N.shiftl_mul_pow2. change (2^0) with 1. lia.
  - I2N.nify. change ♮12 with 12.
    rewrite !N.shiftr_div_pow2, !N.shiftl_mul_pow2. lia.
  - rewrite land16. I2N.nify. change ♮65536 with 65536. lia.
Qed.

(* MOVZ #(imm >> 16), LSL 16 then MOVK #(imm land 0xffff), LSL 0 *)
Lemma movk_z1:
  forall X: int,
  N.lor (N.land (♮(X >> 16) << 16) (N.lnot (N.ones 16 << (♮0 << 4)) 64))
        (♮(X land 65535) << (♮0 << 4)) = ♮X.
Proof.
  intros X. assert (XB: ♮X < 2^63) by lia.
  replace (♮0%uint63 << 4) with 0 by reflexivity.
  rewrite movk_arith.
  - rewrite land16. I2N.nify. change ♮16 with 16. change ♮65536 with 65536.
    rewrite !N.shiftr_div_pow2, !N.shiftl_mul_pow2. change (2^0) with 1. lia.
  - I2N.nify. change ♮16 with 16.
    rewrite !N.shiftr_div_pow2, !N.shiftl_mul_pow2. lia.
  - rewrite land16. I2N.nify. change ♮65536 with 65536. lia.
Qed.

(* Side conditions of the movk lemmas: bounds on shifted/masked ints. *)
Local Ltac mnn :=
  rewrite ?land16; I2N.nify;
  try change ♮32 with 32; try change ♮16 with 16; try change ♮65536 with 65536;
  rewrite ?N.shiftr_div_pow2, ?N.shiftl_mul_pow2; lia.
(* MOVZ #((imm >> 32) land 0xffff), LSL 32; MOVK #((imm >> 16) land 0xffff), LSL 16;
   MOVK #(imm land 0xffff), LSL 0 *)
Lemma movk_z2:
  forall X: int, ♮X < 2^48 ->
  N.lor
    (N.land
       (N.lor
          (N.land (♮(X >> 32 land 65535) << 32) (N.lnot (N.ones 16 << 16) 64))
          (♮(X >> 16 land 65535) << 16))
       (N.lnot (N.ones 16 << (♮0 << 4)) 64))
    (♮(X land 65535) << (♮0 << 4)) = ♮X.
Proof.
  intros X B. assert (XB: ♮X < 2^63) by lia.
  replace (♮0%uint63 << 4) with 0 by reflexivity.
  rewrite (movk_arith (♮(X >> 32 land 65535) << 32) (♮(X >> 16 land 65535)) 16)
    by mnn.
  rewrite (movk_arith _ (♮(X land 65535)) 0) by mnn.
  mnn.
Qed.

(* Exec.v now takes the range hypotheses before IMM for these three; the
   chunk_cases proofs below pass IMM first and discharge the rest as side goals. *)
Lemma ExecBcond':
  forall {s s' x a c m imm19 cond}
    (IMM: Asm.bounded m 19 = Some imm19)
    (C: (cond <? 16 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il (a*4) (arm_decode ♮(Asm.Encode.Bcond imm19 cond))) c s' x),
    reset_temps s s' = s /\ (x = Some (Addr (ofZ 62 (Z.of_N a + Sint63Axioms.to_Z m) * 4)) \/ x = None).
Proof. intros. exact (ExecBcond C IMM XS). Qed.
Lemma ExecCBZ':
  forall {s s' x a c m imm19 sf op r}
    (IMM: Asm.bounded m 19 = Some imm19)
    (O: (op <? 2 = true)%uint63)
    (S: (sf <? 2 = true)%uint63)
    (R: (r <? 32 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il (a*4) (arm_decode ♮(Asm.Encode.CBZ sf op imm19 r))) c s' x),
    reset_temps s s' = s /\ (x = Some (Addr (ofZ 62 (Z.of_N a + Sint63Axioms.to_Z m) * 4)) \/ x = None).
Proof. intros. exact (ExecCBZ O S R IMM XS). Qed.
Lemma ExecTBZ':
  forall {s s' x a c m imm14 b5 op b40 r}
    (IMM: Asm.bounded m 14 = Some imm14)
    (O: (op <? 2 = true)%uint63)
    (B: (b5 <? 2 = true)%uint63)
    (B': (b40 <? 16 = true)%uint63)
    (R: (r <? 32 = true)%uint63)
    (XS: exec_stmt arm8typctx s (arm2il (a*4) (arm_decode ♮(Asm.Encode.TBZ b5 op b40 imm14 r))) c s' x),
    reset_temps s s' = s /\ (x = Some (Addr (ofZ 62 (Z.of_N a + Sint63Axioms.to_Z m) * 4)) \/ x = None).
Proof. intros. exact (ExecTBZ O B B' R IMM XS). Qed.

Definition arm8_prog s a :=
  match a mod 4, xbits (s UXN) (a mod 2^64) (N.succ (a mod 2^64)) with
  | 0, 0 => Some (4, arm2il a (arm_decode (getmem 64 LittleE 4 (s V_MEM64) a)))
  | _, _ => None end.

Theorem welltyped_arm8_prog: welltyped_prog arm8typctx arm8_prog.
Proof.
  intros s a. unfold arm8_prog.
  destruct (a mod 4); try done. destruct (xbits (s UXN) _ _); try done.
  exists arm8typctx. apply welltyped_arm82il.
Qed.
Notation a64prog := arm8_prog.
Notation a64lift := arm2il.
Notation a64dec := arm_decode.

(* Ltac fwd_rewrites ::= fwd_rewrites_autorewrite. *)

(* automatically convert nat to N *)
Coercion N.of_nat : nat >-> N.
(* implicit conversion makes differentiating between nat and N comparisons difficult without explicit notations *)
Infix "<ₒ" := lt (at level 70).
Infix "≤ₒ" := le (at level 70).
Infix ">ₒ" := gt (at level 70).
Infix "≥ₒ" := ge (at level 70).
Infix "<ₙ" := N.lt (at level 70).
Infix "≤ₙ" := N.le (at level 70).
Infix ">ₙ" := N.gt (at level 70).
Infix "≥ₙ" := N.ge (at level 70).
(* avoids an extra pair of parentheses in some cases *)
Notation "4( x )" := (x * 4) (at level 1, only parsing).

Notation lensC c := (nlen (flat_map cd c)).
Notation "lensC[: n ] c" := (lensC (take n c)) (at level 10, format "lensC[: n ]  c").
Notation lensT t := (nlen (flat_map tblcontent t)).
Notation "lensT[: n ] t" := (lensT (take n t)) (at level 10, format "lensT[: n ]  t").
Fixpoint startschunk c b a :=
  match c with
  | c::tail =>
      let l := @length int c.(cd) in
      if a =? b * 4
      then true
      else startschunk tail (b + l) a
  | nil => false
  end.
Lemma startschunk_idx:
  forall c b a (A: startschunk c b a = true),
  exists n, n <ₒ length c ∧ 4(b + lensC[:n] c) = a.
Proof.
  induction c.
  - discriminate.
  - cbn [startschunk]. intros. case_match.
    + exists O. cbn. lia.
    + apply IHc in A. inversion A. exists (S x). simpl.
      rewrite nlen_length, length_app in *. lia.
Qed.

Lemma xbits_inner:
  forall n a b c d,
  c <= a -> b <= d ->
    xbits n a b = xbits (xbits n c d) (a - c) (b - c).
Proof.
  intros. apply N.bits_inj. intro. rewrite !xbits_spec. replace (_ + _ + _) with (n0 + a) by lia. lia.
Qed.
Definition mus q :=
  match q with
  | Move V_MEM64 (Store (Var V_MEM64) _ _ _ _ ) => True
  | Move V_MEM64 _ => False
  | _ => True
  end.
Definition mem_uses_store q := forall_stmts_in_stmt mus q.
Theorem forall_stmts_in_rep:
  forall q e P (FA: forall_stmts_in_stmt P (Rep e q)),
  forall_stmts_in_stmt P q.
Proof.
  intros. unfold forall_stmts_in_stmt, stmts_in_stmt in FA.
  destruct FA as [_ Pq].
  try assumption.
Qed.
Theorem forall_stmts_head:
  forall P q (FA: forall_stmts_in_stmt P q), P q.
Proof.
  intros; destruct q; cbv in FA; easy.
Qed.

Theorem forall_stmts_in_iter:
  forall P q n (FA: forall_stmts_in_stmt P q) (NOP: P Nop)
    (SEQSPLIT: forall q1 q2, P q1 -> P q2 -> P (Seq q1 q2)),
  forall_stmts_in_stmt P (N.iter n (Seq q) Nop).
Proof.
  intros. induction n using N.strong_induction_le.
  - assumption.
  - rewrite N.iter_succ. repeat split; try apply H; try easy.
    apply SEQSPLIT; try easy.
    + now apply forall_stmts_head.
    + now apply forall_stmts_head, H.
Qed.


Lemma nth_zip:
  forall A B C (f: A -> B -> C) a b da db n,
  nth n (zip_with f a b) (f (nth n a da) (nth n b db)) = f (nth n a da) (nth n b db).
Proof.
  induction a, b, n; auto. simpl. apply IHa.
Qed.
Lemma mus_var:
  forall i x, mus (Move (arm_varid i) x).
Proof.
  intros. unfold arm_varid. by repeat case_match.
Qed.
Ltac unfold_rec a :=
  match a with
  | ?x ?y => unfold_rec x
  | _ => unfold a
  end.
Lemma mus_arm2il {a i}: mem_uses_store (arm2il a i).
Proof.
  intros. repeat first [ split | done | apply mus_var | case_match | match goal with |- stmts_in_stmt and mus ?a => unfold_rec a end ].
Qed.

Lemma nonwritable_byte:
  forall {c s q c' s' x i w}
    (XS: exec_stmt c s q c' s' x)
    (MUS: mem_uses_store q)
    (NAW: noassign A_WRITE q)
    (NW: N.testbit (s A_WRITE) i = false)
    (I: i < 2^w),
    getbyte (s V_MEM64) i w = getbyte (s' V_MEM64) i w.
Proof.
  intros. induction XS; auto.
  - destruct v; try now rewrite update_frame by discriminate.
    destruct e; try destruct e1; try done; destruct v; try done. inversion E; inversion E1; subst.
    rewrite update_updated. unfold getbyte. rewrite setmem_frame_byte.
    + reflexivity.
    + intro. cbv[mem_writable] in W. destruct (N.le_gt_cases w1 (msub w2 (i mod 2 ^ w) a)).
      * assumption.
      * specialize (W _ H0). rewrite (N.mod_small i) in W, H by assumption. unfold msub in W.
        rewrite <-N.Div0.add_mod_idemp_l, N.Div0.add_mod_idemp_r, N.add_assoc, N.add_sub_assoc, 2N.add_sub_swap, N.sub_diag, N.add_0_l in W by lia.
        now rewrite <-N.Div0.add_mod_idemp_r, N.Div0.mod_same, N.add_0_r, N.mod_small, NW in W by assumption.
  - destruct MUS. inversion NAW. now apply IHXS.
  - destruct MUS as [_ [A B]]. inversion NAW.
    apply (noassign_stmt_same A_WRITE _ AA1) in XS1; inversion XS1.
    specialize (IHXS1 A AA1 NW). rewrite H2 in NW. now rewrite (IHXS2 B AA2 NW) in IHXS1.
  - destruct MUS as [_ [A B]]. inversion NAW. apply IHXS; now destruct b.
  - apply forall_stmts_in_rep in MUS. inversion NAW. apply IHXS.
    + now apply forall_stmts_in_iter.
    + unfold noassign. generalize n. apply N.peano_ind.
      * constructor.
      * intros. rewrite N.iter_succ. now constructor.
    + assumption.
Qed.
Lemma varid_not_awrite:
  forall n, arm_varid n <> A_WRITE.
Proof.
  intros. unfold arm_varid. by repeat case_match.
Qed.
Lemma noassign_awrite_arm2il {a i}: noassign A_WRITE (arm2il a i).
Proof.
  intros. unfold noassign.
  repeat first [done | apply varid_not_awrite | case_match | constructor | match goal with |- allassigns _ ?a => unfold_rec a end ].
Qed.
Lemma varid_not_uxn:
  forall n, arm_varid n <> UXN.
Proof.
  intros. unfold arm_varid. by repeat case_match.
Qed.
Lemma noassign_uxn_arm2il {a i}: noassign UXN (arm2il a i).
Proof.
  intros. unfold noassign.
  repeat first [done | apply varid_not_uxn | case_match | constructor | match goal with |- allassigns _ ?a => unfold_rec a end ].
Qed.
Definition nonwritable_byte_arm2il {c s a i c' s' x j w}
  (XS: exec_stmt c s (arm2il a i) c' s' x)
  (NW: N.testbit (s A_WRITE) j = false)
  (J: j < 2^w) : getbyte (s V_MEM64) j w = getbyte (s' V_MEM64) j w := nonwritable_byte XS mus_arm2il noassign_awrite_arm2il NW J.
Lemma nonwritable_mem_arm2il:
  forall c s a i c' s' x j w e len
    (XS: exec_stmt c s (arm2il a i) c' s' x)
    (NW: forall k, msub w k j < len -> N.testbit (s A_WRITE) k = false),
    getmem w e len (s V_MEM64) j = getmem w e len (s' V_MEM64) j.
Proof.
  intros. apply getmem_frame_mem. intros.
  rewrite <-getbyte_mod_l, <-(getbyte_mod_l (s' _)).
  eapply nonwritable_byte_arm2il. apply XS. apply NW. now rewrite msub_mod_l by easy.
  lia with (N.mod_lt a' (2^w)).
Qed.
Lemma mapi_length:
  forall A B sz (acc: list B) i f (l: list A),
  length (_mapi sz acc i f l) = (length acc + length l)%nat.
Proof.
  intros A B sz acc i f l. revert acc i. induction l; intros; simpl.
  - rewrite <-rev_alt, length_rev. lia.
  - rewrite IHl. simpl. lia.
Qed.
Definition metadata {A} (c:chunk A) := setd c ().
Lemma metadata_relax : forall a l,
 map metadata (relax a l) = map metadata l.
Proof.
 intros a l. unfold relax. destruct makerel. rewrite map_map.
 apply map_ext. intros []. reflexivity.
Qed.
Lemma metadata_stage3 : forall a l,
 map metadata (stage3 a l) = map metadata l.
Proof.
 intros. unfold stage3. induction (nrelax a); [reflexivity|].
 simpl. rewrite metadata_relax. exact IHn.
Qed.
Lemma metadata_stage2 : forall a l,
 map metadata (stage2 a l) = l.
Proof.
 intros. unfold stage2. rewrite map_map.
 induction l as [|[] l IH]; cbn; [reflexivity|]. destruct cd. by rewrite IH.
Qed.
(* A chunk whose instructions cannot relax keeps its original instruction sizes. *)
Lemma relax_stable_chunk : forall a cs n c,
  ith cs n = Some c ->
  (forall rel ip inst, In inst c.(cd) -> relaxi rel ip inst = inst) ->
  ith (relax a cs) n = Some c.
Proof.
  intros a cs n c NTH STABLE. unfold relax. destruct makerel.
  rewrite ith_map, NTH. cbn [option_map]. f_equal.
  assert (ID : forall code ip,
    (forall ip inst, In inst code -> relaxi i ip inst = inst) ->
    instmapi ip (relaxi i) code = code).
  { induction code as [|inst code IH]; intros ip ST; [reflexivity|].
    unfold instmapi in *. rewrite mapi_cons. cbn. rewrite ST by by left.
    f_equal. apply IH. intros. apply ST. by right. }
  rewrite ID by (intros; apply STABLE; assumption).
  destruct c. reflexivity.
Qed.
Lemma stage3_stable_chunk : forall a cs n c,
  ith cs n = Some c ->
  (forall rel ip inst, In inst c.(cd) -> relaxi rel ip inst = inst) ->
  ith (stage3 a cs) n = Some c.
Proof.
  intros a cs n c NTH STABLE. unfold stage3.
  induction (nrelax a); [exact NTH|]. cbn.
  apply relax_stable_chunk; assumption.
Qed.
Section SourceMetadata.
Variables (a:args) (d:data).
Variable D: rw_hook a id = Some d.
Lemma chunks_metadata : map metadata d.(chunks) = stage1 a.
Proof.
 repeat so D. rewrite <-D. simpl. rewrite metadata_stage3, metadata_stage2. reflexivity.
Qed.
Lemma arg_same : d.(arg)=a.
Proof. repeat so D. rewrite <-D. reflexivity. Qed.
Lemma source_bound : (toN a.(Rewrite.bi) + N.of_nat (length a.(code)) < 2^63)%N.
Proof.
 assert (F: forall l k, fold_left (fun n (_:int)=>N.succ n) l k = (k + N.of_nat (length l))%N).
 { induction l; intros; cbn; [lia|]. rewrite IHl. lia. }
 repeat so D. unfold source_fits in *. rewrite F in *. apply N.ltb_lt in Heqb. exact Heqb.
Qed.
Lemma ai_bound : (toN d.(Rewrite.ai)<2^61)%N.
Proof. repeat so D. rewrite <-D. simpl. nify. lia. Qed.
Lemma chunks_count : length d.(chunks) = length a.(code).
Proof.
 rewrite <-(length_map metadata), chunks_metadata.
 unfold stage1, mapi. rewrite mapi_length. reflexivity.
Qed.
Lemma source_nth : forall n c,
 ith d.(chunks) n = Some c ->
 c.(ci) = (a.(Rewrite.bi) + ofNat n)%uint63 /\
 Decode.decode c.(cn) = c.(ct) /\
 c.(cp) = a.(Rewrite.pol) c.(ci) /\
 c.(cl) = (ofNat n =? len a.(code)-1)%uint63 /\
 (n < length a.(code))%nat.
Proof.
 intros n c H.
 assert (B : (n < length d.(chunks))%nat) by (apply ith_Some; congruence). rewrite chunks_count in B.
 pose proof (f_equal (option_map metadata) H) as M.
 rewrite <-ith_map,chunks_metadata,ith_nth_error in M.
 unfold stage1 in M. apply mapi_nth with (d:=0%uint63) in M.
 unfold metadata,setd in M. inversion M. repeat split; congruence.
Qed.
Lemma not_last_has_next : forall n c,
 ith d.(chunks) n=Some c -> c.(cl)=false -> (S n < length d.(chunks))%nat.
Proof.
 intros n c N CL.
 destruct (source_nth n c N) as (CI&DEC&CP&LAST&LT).
 rewrite chunks_count. rewrite LAST in CL.
 pose proof source_bound as B.
 rewrite len_length in CL by lia.
 destruct (Nat.eq_dec (S n) (length a.(code))) as [E|E]; [|lia].
 assert (ofNat n = (ofNat (length a.(code))-1)%uint63) as EQ by lia.
 rewrite EQ,Uint63.eqb_refl in CL. discriminate.
Qed.
End SourceMetadata.
Lemma startschunk_at : forall l b n,
 (n < length l)%nat -> startschunk l b ((b+nlen(flat_map cd (take n l)))*4) = true.
Proof.
 induction l as [|c l IH]; intros b n LT; [cbn in LT;lia|].
 destruct n; simpl; [by rewrite N.add_0_r,N.eqb_refl|].
 case_match; [reflexivity|].
 rewrite !nlen_length,length_app,Nat2N.inj_add.
 replace ((b+(N.of_nat (length c.(cd))+N.of_nat (length (flat_map cd (take n l)))))*4)
 with ((b+N.of_nat(length c.(cd))+nlen(flat_map cd(take n l)))*4)
 by (rewrite nlen_length;lia).
 apply IH. simpl in LT. lia.
Qed.
Lemma pad_to_ge10 : forall x, (toN x<2^62)%N -> (toN x<=toN(pad_to x 10))%N.
Proof.
 intros x LT.
 assert (P : (toN (padding x 10) <= 1023)%N).
 { unfold padding. nify. apply N.land_le_r. }
 unfold pad_to. nify. lia.
Qed.
Lemma fallthrough_not_last : forall (c:chunk unit), isfallthrough c=true -> c.(cl)=false.
Proof.
 intros [cn ci ct cp cl []] H. destruct cp as [b|b j| |lbl]; try destruct b; cbn in H; try discriminate; by destruct cl.
Qed.
Lemma isdirect_false_fallthrough : forall (c:chunk unit) target,
  isdirect c false target = true -> isfallthrough c = true.
Proof.
  intros [cn ci ct cp last []] target DIR.
  destruct cp as [b|b dest| |lbl]; try destruct b; destruct last; cbn in *; congruence.
Qed.

(* Address materialization only falls through or raises an exception. *)
Definition straightline l := Forall (fun inst => nonbranch (arm_decode (toN inst))) l.
Lemma decoded_ADR_register : forall cn imm rd,
 Decode.decode cn=Decode.ADR imm rd -> (toN rd<32)%N.
Proof.
 intros cn imm rd DEC.
 unfold Decode.decode, Decode.dc_b, Decode.dc_dpi, Decode.dc_pcr,
 Decode.dc_b_cond, Decode.dc_b_reg, Decode.dc_b_imm, Decode.dc_cb, Decode.dc_tb in DEC.
 repeat match type of DEC with (if ?b then _ else _) = _ => destruct b eqn:?; try discriminate DEC end.
 all: inversion DEC; subst rd.
 all: rewrite I2N.inj_xb; apply xbits_bound.
Qed.
Lemma decoded_ADRP_register : forall cn imm rd,
 Decode.decode cn=Decode.ADRP imm rd -> (toN rd<32)%N.
Proof.
 intros cn imm rd DEC.
 unfold Decode.decode, Decode.dc_b, Decode.dc_dpi, Decode.dc_pcr,
 Decode.dc_b_cond, Decode.dc_b_reg, Decode.dc_b_imm, Decode.dc_cb, Decode.dc_tb in DEC.
 repeat match type of DEC with (if ?b then _ else _) = _ => destruct b eqn:?; try discriminate DEC end.
 all: inversion DEC; subst rd.
 all: rewrite I2N.inj_xb; apply xbits_bound.
Qed.
Lemma decoded_BR_register : forall cn rn,
 Decode.decode cn=Decode.BR rn -> (toN rn<32)%N.
Proof.
 intros cn rn DEC.
 unfold Decode.decode, Decode.dc_b, Decode.dc_dpi, Decode.dc_pcr,
 Decode.dc_b_cond, Decode.dc_b_reg, Decode.dc_b_imm, Decode.dc_cb, Decode.dc_tb in DEC.
 repeat match type of DEC with (if ?b then _ else _) = _ => destruct b eqn:?; try discriminate DEC end.
 all: inversion DEC; subst rn.
 all: rewrite I2N.inj_xb; apply xbits_bound.
Qed.
Lemma decoded_RET_register : forall cn rn,
 Decode.decode cn=Decode.RET rn -> (toN rn<32)%N.
Proof.
 intros cn rn DEC.
 unfold Decode.decode, Decode.dc_b, Decode.dc_dpi, Decode.dc_pcr,
 Decode.dc_b_cond, Decode.dc_b_reg, Decode.dc_b_imm, Decode.dc_cb, Decode.dc_tb in DEC.
 repeat match type of DEC with (if ?b then _ else _) = _ => destruct b eqn:?; try discriminate DEC end.
 all: inversion DEC; subst rn.
 all: rewrite I2N.inj_xb; apply xbits_bound.
Qed.
Lemma decoded_BLR_register : forall cn rn,
 Decode.decode cn=Decode.BLR rn -> (toN rn<32)%N.
Proof.
 intros cn rn DEC.
 unfold Decode.decode, Decode.dc_b, Decode.dc_dpi, Decode.dc_pcr,
 Decode.dc_b_cond, Decode.dc_b_reg, Decode.dc_b_imm, Decode.dc_cb, Decode.dc_tb in DEC.
 repeat match type of DEC with (if ?b then _ else _) = _ => destruct b eqn:?; try discriminate DEC end.
 all: inversion DEC; subst rn.
 all: rewrite I2N.inj_xb; apply xbits_bound.
Qed.
Lemma orelse_cons : forall (o: option (list int)) dd,
 (o orelse []) = [dd] -> o = Some [dd].
Proof. intros o dd. destruct o; simpl; intro H; [by f_equal | discriminate]. Qed.
Lemma bounded_small : forall v w imm,
 Asm.bounded v w=Some imm -> (toN w<63)%N -> (toN imm<2^(toN w))%N.
Proof.
 intros v w imm B W. unfold Asm.bounded in B.
 destruct (_ && _) eqn:E; [|discriminate]. inversion B; subst imm.
 rewrite I2N.inj_land,I2N.inj_ones.
 rewrite N.mod_small; [|eapply N.lt_trans;[apply ones_bound|apply N.pow_lt_mono_r;lia]].
 rewrite N.land_ones. apply N.mod_lt. lia.
Qed.
Lemma isel_Iimm_straightline : forall d ip relax k rd imm,
 (toN rd<32)%N -> straightline (l3l (isel d ip (Iimm relax k rd imm))).
Proof.
 intros d ip relax k rd imm RD.
 unfold straightline,isel. destruct k.
 - destruct (_ =? _)%uint63 eqn:HIT; cbn -[xb Asm.Encode.ADRP Asm.Encode.ADR Asm.Encode.MOVZ Asm.Encode.MOVK resolve].
   + unfold Asm.ADRP. destruct Asm.bounded eqn:B; cbn -[xb Asm.Encode.ADRP Asm.Encode.ADR Asm.Encode.MOVZ Asm.Encode.MOVK resolve]; [|constructor].
     repeat match goal with |- Forall _ (_::_) => constructor | |- Forall _ [] => constructor end.
     rewrite decode_ADRP; try (rewrite I2N.inj_xb;apply xbits_bound); try exact RD.
     exact I.
   + unfold Asm.ADR. destruct Asm.bounded eqn:B; cbn -[xb Asm.Encode.ADRP Asm.Encode.ADR Asm.Encode.MOVZ Asm.Encode.MOVK resolve]; [|constructor].
     repeat match goal with |- Forall _ (_::_) => constructor | |- Forall _ [] => constructor end.
     rewrite decode_ADR; [exact I| | |exact RD].
     * exact (bounded_small _ 19 _ B ltac:(lia)).
     * rewrite I2N.inj_land. change (N.land (toN (resolve d imm)) (N.ones 2)<2^2)%N. rewrite N.land_ones. apply N.mod_lt. lia.
 - destruct (fits _ _); cbn -[xb Asm.Encode.ADRP Asm.Encode.ADR Asm.Encode.MOVZ Asm.Encode.MOVK resolve].
   + unfold Asm.ADRP. destruct Asm.bounded eqn:B; cbn -[xb Asm.Encode.ADRP Asm.Encode.ADR Asm.Encode.MOVZ Asm.Encode.MOVK resolve].
     * repeat match goal with |- Forall _ (_::_) => constructor | |- Forall _ [] => constructor end.
       -- rewrite decode_ADRP; try (rewrite I2N.inj_xb;apply xbits_bound); try exact RD. exact I.
       -- rewrite decode_MOVK; [exact I| |exact RD|lia|lia|lia].
          rewrite I2N.inj_land. change (N.land (toN (resolve d imm)) (N.ones 16)<2^16)%N. rewrite N.land_ones. apply N.mod_lt. lia.
     * repeat match goal with |- Forall _ (_::_) => constructor | |- Forall _ [] => constructor end.
       -- exact I.
       -- rewrite decode_MOVK; [exact I| |exact RD|lia|lia|lia].
          rewrite I2N.inj_land. change (N.land (toN (resolve d imm)) (N.ones 16)<2^16)%N. rewrite N.land_ones. apply N.mod_lt. lia.
   + destruct (_ =? _)%uint63 eqn:HIT; cbn -[xb Asm.Encode.ADRP Asm.Encode.ADR Asm.Encode.MOVZ Asm.Encode.MOVK resolve]; [|constructor].
     repeat match goal with |- Forall _ (_::_) => constructor | |- Forall _ [] => constructor end.
     * rewrite decode_MOVZ; [exact I| |exact RD|lia|lia|lia].
       apply Uint63.eqb_correct in HIT. pose proof (f_equal toN HIT) as HIGH.
       rewrite I2N.inj_lsr in HIGH |- *.
       change ((toN (resolve d imm)>>32)=0)%N in HIGH.
       rewrite N.shiftr_div_pow2 in HIGH |- *. lia.
     * rewrite decode_MOVK; [exact I| |exact RD|lia|lia|lia].
       rewrite I2N.inj_land. change (N.land (toN (resolve d imm)) (N.ones 16)<2^16)%N. rewrite N.land_ones. apply N.mod_lt. lia.
 - destruct (_ =? _)%uint63 eqn:HIT; cbn -[xb Asm.Encode.ADRP Asm.Encode.ADR Asm.Encode.MOVZ Asm.Encode.MOVK resolve]; [|constructor].
   repeat match goal with |- Forall _ (_::_) => constructor | |- Forall _ [] => constructor end.
   + rewrite decode_MOVZ; [exact I| |exact RD|lia|lia|lia].
     rewrite I2N.inj_land. change (N.land (toN (resolve d imm >> 32)) (N.ones 16)<2^16)%N. rewrite N.land_ones. apply N.mod_lt. lia.
   + rewrite decode_MOVK; [exact I| |exact RD|lia|lia|lia].
     rewrite I2N.inj_land. change (N.land (toN (resolve d imm >> 16)) (N.ones 16)<2^16)%N. rewrite N.land_ones. apply N.mod_lt. lia.
   + rewrite decode_MOVK; [exact I| |exact RD|lia|lia|lia].
     rewrite I2N.inj_land. change (N.land (toN (resolve d imm)) (N.ones 16)<2^16)%N. rewrite N.land_ones. apply N.mod_lt. lia.
Qed.

Section Soundness.
  (* rewriter input *)
  Variable a : args.
  (* intermediary data produced by the rewriter *)
  Variable d : data.
  (* rewriter output *)
  Variable cnks : chunklist (list int).

  (* d came from the rewriter with input a *)
  Variable D : rw_hook a id = Some d.
  (* cnks is the output of the rewriter *)
  Variable RW : rw2 d = Some cnks.

  Notation ai := ♮d.(ai).
  Notation tc := d.(tc).
  Notation rel := d.(rel).
  Notation bi := d.(arg).(bi).
  Notation bi' := ♮d.(arg).(bi').
  Notation bti := ♮d.(bti).
  Notation pol := d.(arg).(pol).
  Notation dsets := d.(arg).(dsets).
  Notation irel := (irel d cnks).

  (* Is address `a` an external address? (one that is not in the rewritten code segment) *)
  Definition is_ext_addr a := (a <? bi' * 4) || ((bi' + lensC cnks) * 4 <=? a).
  (* Does address `a` start a chunk? *)
  Definition is_chunk_start_addr a := startschunk cnks bi' a.
  (* Given policy pol, an edge from index i to j is permitted if: *)
  Variant PermittedEdge: N -> N -> Prop :=
    (* 1: pol says i is a fallthrough instruction
          and j is the next index *)
    | FallthroughEdge i
        (I: pol i = Pfallthru true):
        PermittedEdge ♮i (S ♮i)
    (* 2: pol says i is a direct branch instruction that allows fallthrough
          and j is the next index *)
    | FallthroughEdge2 i j
        (I: pol i = Pdirect true j):
        PermittedEdge ♮i (S ♮i)
    (* 3: pol says i is a direct branch instruction
          and j is the direct target index *)
    | DirectEdge i j b
        (I: pol i = Pdirect b j):
        PermittedEdge ♮i ♮j
    | IgnoreEdge i j
        (I: pol i = Pignore):
        PermittedEdge ♮i j
    (* or 4: pol says i is an indirect branch instruction labeled with the nth destination set
          and j is an index in the nth destination set *)
    | IndirectEdge i j d n
        (I: pol i = Pindirect n)
        (D: nth_error dsets ♮n = Some d)
        (J: In j d):
        PermittedEdge ♮i ♮j.
  (* We now reinterpret policy pol to account for address relocation.
     An edge from relocated index i' to j' in the rewritten program is permitted if: *)
  Variant PermittedEdge': N -> N -> Prop :=
    (* 1: j' is the abort index *)
    | AbortEdge i':
        PermittedEdge' i' ai
    (* 2: applying the inverse relocation function to i' and j' results in the same original index
          in other words, we are still in the same chunk *)
    | IntraChunkEdge i' j'
        (SC: irel i' = irel j'):
        PermittedEdge' i' j'
    (* or 3: applying the inverse relocation function to i' and j' results in a permitted edge in the original program *)
    | TranslatedEdge i' j'
        (PE: PermittedEdge (irel i') (irel j')):
        PermittedEdge' i' j'.
  (* A step between two exit-store pairs in the new program is permitted if: *)
  Definition PermittedStep '((x', _, (x, _)) : exit * store * (exit * store)) :=
    match x', x with
    (* 1: the step is between addresses with indices i and i' such that i to i' is a permitted edge *)
    | Addr a', Addr a =>
        exists i i' (I: a = i * 4) (I': a' = i' * 4),
        PermittedEdge' i i'
    (* or 2: a hardware exception is raised *)
    | _, _ => True
    end.
  Lemma PEirel:
    forall i i' j, irel i = irel i' -> PermittedEdge' i j -> PermittedEdge' i' j.
  Proof.
    intros. inversion H0. apply AbortEdge. apply IntraChunkEdge. lia. apply TranslatedEdge. by rewrite <-H.
  Qed.
  (* Memory in store s contains list l starting at index i (in little endian),
     where each element has a width of w bytes *)
  Definition MemHas s l i w :=
    forall j n, ith l j = Some n ->
    getmem 64 LittleE w (s V_MEM64) (i * 4 + j * w) = ♮n.
  Definition mem_invs s :=
    (* s is a valid armv8 store *)
    models arm8typctx s ∧
    (* memory contains the flattened list of chunk bytes starting at index bi' *)
    MemHas s (flat_map cd cnks) bi' 4 ∧
    (* memory contains the flattened list of table bytes starting at index bti *)
    MemHas s (flat_map tblcontent tc) bti 8 ∧
    (* chunk bytes are nonwritable *)
    xbits (s A_WRITE) (bi' * 4) (bi' * 4 + (lensC cnks) * 4) = 0 ∧
    (* table bytes are nonwritable *)
    xbits (s A_WRITE) (bti * 4) (bti * 4 + (lensT tc) * 8) = 0 ∧
    (* chunk bytes are executable *)
    xbits (s UXN) (bi' * 4) (bi' * 4 + (lensC cnks) * 4) = 0.
  Definition flag_invs (s:store) := True.
  Definition store_invs s := mem_invs s ∧ flag_invs s.
  Definition hdP P (t: trace) :=
    match t with
    | (_, s)::_ => P s
    | _ => False
    end.
  (* We place an invariant point at the start of each chunk,
     at any external address, and whenever an exception is raised *)
  Definition K_inv_point (t: trace) :=
    match t with
    | (Addr a, s)::_ => is_ext_addr a || is_chunk_start_addr a
    | (Raise i, s)::_ => true
    | _ => false
    end.
  (* At each invariant point, we assert that every step so far is a permitted step
     and the store at the head of the trace satisfys our store invariants *)
  Definition K_inv (t: trace) := Forall PermittedStep (stepsof t) /\ hdP store_invs t.
  Definition K_invs t := if K_inv_point t then Some (K_inv t) else None.
  (* Any external address is an exit point *)
  Definition K_exits (t: trace) :=
    match t with
    | (Addr a, _)::_ => is_ext_addr a
    | _ => false
    end.
  Definition K_nibt b t := nextinv arm8_prog K_invs K_exits b t.
  Definition K_nib b x s := K_nibt b ((x,s)::nil).
  Definition K_ni x s := K_nib true x s.
  (* We can clear a trace prefix from the invariant
     if all steps up to the start of the suffix are permitted *)
  Lemma clear_trace':
    forall p xs t t0 b
      (NI: nextinv' p K_invs K_exits b (xs::t))
      (PS: Forall PermittedStep (stepsof (startof t xs::t0))),
    nextinv' p K_invs K_exits b (xs::t++t0).
  Proof.
    cofix IH; intros.
    inversion NI.
    - apply NIHere'; subst.
      unfold K_invs in *; simpl in *.
      repeat case_match; repeat select (_ = Some _) subst''; try done;
      (split; [rewrite app_comm_cons, stepsof_app, Forall_app|]; by inversion TRU).
    - eapply NIStep'.
      + cbv [effinv effinv' K_invs K_exits] in NOI|-*. rewrite IL.
        by destruct K_inv_point, b, is_ext_addr.
      + exact IL.
      + intros. subst. apply STEP in XS. rewrite app_comm_cons.
        apply IH; by try rewrite startof_cons.
  Qed.
  Lemma clear_trace:
    forall xs t t0 b
      (NI: K_nibt b (xs::t))
      (PS: Forall PermittedStep (stepsof (startof t xs::t0))),
    K_nibt b (xs::t++t0).
  Proof.
    intros until 3. apply clear_trace'; auto. apply NI.
    rewrite app_comm_cons in XP. now apply exec_prog_split in XP.
  Qed.
  Lemma memhas_ith_w:
    forall {ll l b m s w}
      (J: ith ll m = Some l)
      (M: MemHas s (concat ll) b (4 * w)),
      MemHas s l (b + length (concat (take m ll)) * w) (4 * w).
  Proof.
    intros until 3.
    specialize (M (j + length (concat (take m ll))) n)%nat.
    rewrite ith_concat2 with (n:=m), Nat.add_sub in M by lia.
    rewrite ith_skipn_hd in J. destruct drop.
    - easy.
    - inversion J; subst.
      rewrite ith_concat1 in M by (apply ith_Some; now rewrite H).
      apply M in H. rewrite <-H. f_equal. lia.
  Qed.
  Lemma memhas_ith:
    forall {ll l b m s}
      (J: ith ll m = Some l)
      (M: MemHas s (concat ll) b 4),
    MemHas s l (b + length (concat (take m ll))) 4.
  Proof.
    intros. eqapply (memhas_ith_w J M (w:=1)). lia.
  Qed.
  Lemma memhas_ith':
    forall {ll l b m s}
      (J: ith ll m = Some l)
      (M: MemHas s (concat ll) b 8),
    MemHas s l (b + length (concat (take m ll)) * 2) 8.
  Proof.
    intros. apply (memhas_ith_w J M (w:=2)).
  Qed.
  Lemma nlen_flat:
    forall A B (f: A -> list B) l, nlen (flat_map f l) = nsum (map nlen (map f l)).
  Proof.
    induction l.
    - easy.
    - simpl. rewrite nsum_cons, <-IHl, !nlen_length, length_app. lia.
  Qed.
  Lemma nsum_take_Sn:
    forall n l, nsum (take (S n) l) = nsum (take n l) + (nth n l 0).
  Proof.
    induction n.
    - by destruct l.
    - intros. destruct l.
      + done.
      + simpl. rewrite !nsum_cons, IHn. lia.
  Qed.
  Lemma nsum_take_Sn':
    forall n l x, ith l n = Some x -> nsum (take (S n) l) = nsum (take n l) + x.
  Proof.
    intros. rewrite nsum_take_Sn. eapply ith_nth in H. by rewrite H.
  Qed.
  Lemma nsum_nat:
    forall l, nsum l = list_sum (map N.to_nat l).
  Proof.
    induction l. easy. rewrite nsum_cons. simpl. lia.
  Qed.
  Lemma list_sum_N:
    forall l, list_sum l = ♭(nsum (map N.of_nat l)).
  Proof.
    induction l. easy. simpl. rewrite nsum_cons. lia.
  Qed.
  Lemma nlen_flat':
    forall A B (f: A -> list B) l, nlen (flat_map f l) = length (concat (map f l)).
  Proof.
    intros. by rewrite nlen_length, flat_map_concat_map.
  Qed.
  Lemma sumltlt:
    forall l n, sumlt l n = true -> nsum (map toN l) < toN n.
  Proof.
    unfold nsum. induction l; cbn; intros. lia.
    case_match; try done.
    apply IHl in H. rewrite nfls. lia.
  Qed.
  Lemma rw_inst_length:
    forall c, (length (rw_inst a c) <= 9)%nat.
  Proof.
    intros. unfold rw_inst, rw_indirect, setlr.
    destruct c.(ct); repeat case_match; simpl; lia.
  Qed.
  Lemma chunks_length:
    Forall (λ c, (length c.(cd) <= 9)%nat) d.(chunks).
  Proof.
    repeat so D. rewrite <-D. simpl.
    unfold stage3, id. generalize a.(nrelax). intro n. induction n.
    - unfold stage2. apply Forall_map, Forall_forall.
      intros. simpl. apply rw_inst_length.
    - simpl. unfold relax. destruct makerel.
      apply Forall_map. eapply Forall_impl; [|exact IHn].
      intros c Hc. simpl. unfold instmapi. rewrite mapi_length. simpl. exact Hc.
  Qed.
  Lemma cnks_length:
    Forall (λ c, (length c.(cd) <= 27)%nat) cnks.
  Proof.
    assert (L3: forall l, (length (concat (map l3l l)) <= 3 * length l)%nat).
    { induction l; simpl; [lia|]. rewrite length_app. destruct a0; simpl; lia. }
    rewrite (chunk_equiv _ _ RW), Forall_map.
    eapply Forall_impl; [|exact chunks_length].
    intros c Hc. simpl in *. etransitivity; [apply L3|].
    unfold instmapi. rewrite mapi_length. simpl. lia.
  Qed.
  Lemma noovfl: NoOverflow bi' cnks.
  Proof.
    pose proof cnks_length as CL.
    repeat so RW. case_match; try done. apply sumltlt in Heqb0. subst' RW.
    rewrite map_map in *. simpl in Heqb0.
    remember (map _ _). replace (map _ _) with l. lia. subst.
    apply map_ext_in. intros c IN. rewrite len_nlen, to_of_N.
    rewrite N.mod_small; [reflexivity|].
    rewrite Forall_forall in CL. apply CL in IN.
    rewrite nlen_length. lia.
  Qed.
  Lemma table_fits_sound:
    forall b tables, table_fits b tables = true ->
    ♮b * 4 + lensT tables * 8 < 2^63.
  Proof.
    assert (COUNT: forall (l: list int) n,
      fold_left (λ n (_: int), (n + 2)%N) l n = n + nlen l * 2).
    { induction l; intros; simpl; [lia|]. rewrite IHl. lia. }
    assert (TABLES: forall tables n,
      fold_left (λ n t,
        fold_left (λ n (_: int), (n + 2)%N) t.(tblcontent) n)
        tables n = n + lensT tables * 2).
    { induction tables; intros; simpl; [lia|]. rewrite COUNT, IHtables.
      rewrite !nlen_length, length_app. lia. }
    intros b tables FIT. unfold table_fits in FIT.
    rewrite TABLES in FIT. apply N.ltb_lt in FIT. unfold toN. lia.
  Qed.
  Lemma tables_noovfl:
    bti * 4 + lensT tc * 8 < 2^63.
  Proof.
    repeat so D. rewrite <-D. simpl. apply table_fits_sound. assumption.
  Qed.
  Lemma tables_D:
    compute_tables rel d.(Rewrite.ai) d.(Rewrite.bti) dsets = Some tc.
  Proof.
    repeat so D. rewrite <-D. simpl. assumption.
  Qed.
  Lemma output_source_nth : forall n c,
   ith cnks n=Some c -> c.(ci)=(a.(Rewrite.bi)+ofNat n)%uint63.
  Proof.
   intros. rewrite <-(arg_same a d D). apply (nth_ci d cnks RW noovfl); [|by rewrite <-ith_nth_error].
   intros m c0 N. rewrite <-ith_nth_error in N.
   rewrite (arg_same a d D). exact (proj1 (source_nth a d D m c0 N)).
  Qed.
  Lemma following_irel : forall n c,
   ith cnks n=Some c -> (S n < length d.(chunks))%nat ->
   irel (bi'+nlen(flat_map cd (take (S n) cnks))) = (toN c.(ci)+1)%N.
  Proof.
   intros n c N LT.
   assert (LN : (S n < length cnks)%nat) by (rewrite (num_cnks d cnks RW);lia).
   assert (NEXT : exists c', ith cnks (S n)=Some c') by (destruct (ith cnks (S n)) eqn:E; [eauto|apply ith_None in E;lia]).
   destruct NEXT as [c' NEXT].
   unfold irel. rewrite !nlen_flat,<-!firstn_map,findchunk_in with (d:=C[nil]).
   - rewrite (ith_nth _ _ _ _ NEXT). simpl.
     rewrite (output_source_nth _ _ N),(output_source_nth _ _ NEXT).
     pose proof (source_bound a d D). rewrite (chunks_count a d D) in LT. nify. lia.
   - exact (nonempty_cnks d cnks RW).
   - exact LN.
  Qed.
  Lemma rel_start : forall n c,
   ith d.(chunks) n=Some c -> d.(Rewrite.rel) c.(ci) = ofN (bi'+nlen(flat_map cd (take n cnks))).
  Proof.
   intros n c N.
   pose proof (source_nth a d D n c N) as (CI&DEC&POL&LAST&LT).
   pose proof (source_bound a d D) as SB.
   pose proof (chunks_count a d D) as CC.
   assert (CL : Forall (fun c=> (length c.(cd)<100)%nat) cnks).
   { eapply Forall_impl; [|apply cnks_length]. intros c0 C0. cbn beta in C0 |- *. lia. }
   pose proof (correct_lengths d cnks RW CL) as LENS.
   assert (MR : (d.(Rewrite.rel),d.(Rewrite.ai))=makerel a d.(chunks)).
   { repeat so D. rewrite <-D. reflexivity. }
   pose proof (f_equal fst MR) as REL.
   unfold makerel in REL. cbn beta iota zeta delta [fst] in REL.
   rewrite REL, CI.
   assert (L : (a.(Rewrite.bi) <=? a.(Rewrite.bi)+ofNat n = true)%uint63) by lia.
   assert (U : (a.(Rewrite.bi)+ofNat n <? a.(Rewrite.bi)+len d.(chunks)=true)%uint63).
   { rewrite len_length,CC; lia. }
   rewrite L,U. cbn.
   replace (a.(Rewrite.bi)+ofNat n-a.(Rewrite.bi))%uint63 with (ofNat n) by lia.
   rewrite csum_def,isumn.
   replace (toNat (ofNat n)) with n by lia.
   rewrite <-firstn_map,<-LENS,nlen_flat,<-firstn_map.
   rewrite (arg_same a d D).
   nify. fold (toN a.(Rewrite.bi')). rewrite !to_of_N,<-firstn_map,N.Div0.add_mod_idemp_r. reflexivity.
  Qed.
  Lemma ai_layout : d.(Rewrite.ai)=pad_to (csum a.(Rewrite.bi') (map chunksize d.(chunks)) (len d.(chunks))) 10.
  Proof. repeat so D. rewrite <-D. reflexivity. Qed.
  Lemma abort_after_code : (toN d.(arg).(Rewrite.bi') + nlen(flat_map cd cnks) <= toN d.(Rewrite.ai))%N.
  Proof.
   pose proof noovfl as NO.
   assert (CL : Forall (fun c=> (length c.(cd)<100)%nat) cnks).
   { eapply Forall_impl; [|apply cnks_length]. intros c C. cbn beta in C |- *. lia. }
   pose proof (correct_lengths d cnks RW CL) as LENS.
   assert (LEN : (nlen d.(chunks)<2^62)%N) by (exact (maxchunks d cnks RW NO CL)).
   rewrite ai_layout, csum_def,firstn_all2.
   - rewrite isumn, (arg_same a d D), !nlen_flat in *.
     rewrite <-LENS.
     eapply N.le_trans; [|apply pad_to_ge10].
     + rewrite I2N.inj_add,to_of_N,N.Div0.add_mod_idemp_r,N.mod_small by lia. lia.
     + rewrite I2N.inj_add,to_of_N,N.Div0.add_mod_idemp_r,N.mod_small by lia. exact NO.
   - rewrite nlen_length in LEN. rewrite len_length,length_map; lia.
  Qed.

  Lemma chunk_point_bound : forall n,
    bi' + lensC[:n] cnks <= ai.
  Proof.
    intro n. pose proof abort_after_code as END.
    rewrite !nlen_flat, <-!firstn_map in *.
    pose proof (nsum_firstn_le (cmap nlen cnks) n). lia.
  Qed.
  Lemma irel_at_start : forall m c,
    ith d.(chunks) m = Some c ->
    irel (bi' + lensC[:m] cnks) = toN c.(ci).
  Proof.
    intros m c NTH.
    assert (OUT : ith cnks m = Some (setd c
      (concat (map l3l (instmapi (d.(Rewrite.rel) c.(ci)) (isel d) c.(cd)))))).
    { rewrite (chunk_equiv d cnks RW), ith_map, NTH. reflexivity. }
    unfold irel. rewrite nlen_flat, <-!firstn_map, findchunk_in with (d:=C[nil]).
    - rewrite (ith_nth _ _ _ _ OUT). reflexivity.
    - exact (nonempty_cnks d cnks RW).
    - apply ith_Some. rewrite OUT. discriminate.
  Qed.
  Lemma relocation_endpoint : forall j,
    toN (d.(Rewrite.rel) j) < 2^61 /\
    (d.(Rewrite.rel) j = d.(Rewrite.ai) \/
      irel (toN (d.(Rewrite.rel) j)) = toN j) /\
    (is_ext_addr (toN (d.(Rewrite.rel) j)*4) = true \/
      is_chunk_start_addr (toN (d.(Rewrite.rel) j)*4) = true).
  Proof.
    intro j.
    pose proof (ai_bound a d D) as AB.
    pose proof abort_after_code as END.
    assert (ABORT : d.(Rewrite.rel) j = d.(Rewrite.ai) ->
      toN (d.(Rewrite.rel) j) < 2^61 /\
      (d.(Rewrite.rel) j = d.(Rewrite.ai) \/
        irel (toN (d.(Rewrite.rel) j)) = toN j) /\
      (is_ext_addr (toN (d.(Rewrite.rel) j)*4) = true \/
        is_chunk_start_addr (toN (d.(Rewrite.rel) j)*4) = true)).
    { intro EQ. rewrite EQ. split; [exact AB|]. split; [by left|].
      left. unfold is_ext_addr. apply orb_true_iff. right. apply N.leb_le. lia. }
    destruct ((a.(Rewrite.bi) <=? j) && (j <? a.(Rewrite.bi)+len d.(chunks)))%uint63 eqn:IN.
    - pose proof (source_bound a d D) as SB.
      rewrite <-(chunks_count a d D) in SB.
      rewrite len_length in IN by lia.
      set (m:=toNat (j-a.(Rewrite.bi))) in *.
      assert (MLT : (m < length d.(chunks))%nat) by (unfold m; lia).
      destruct (ith d.(chunks) m) as [c|] eqn:NTH; [|apply ith_None in NTH;lia].
      pose proof (source_nth a d D m c NTH) as (CI&_).
      assert (CIJ : c.(ci) = j) by (rewrite CI; unfold m; lia).
      rewrite <-CIJ, (rel_start m c NTH).
      pose proof (chunk_point_bound m) as PB.
      rewrite to_of_N, N.mod_small by lia.
      split; [lia|]. split; [right; exact (irel_at_start m c NTH)|].
      right. unfold is_chunk_start_addr. apply startschunk_at.
      rewrite (num_cnks d cnks RW). exact MLT.
    - assert (MR : (d.(Rewrite.rel), d.(Rewrite.ai)) = makerel a d.(chunks)).
      { repeat so D. rewrite <-D. reflexivity. }
      pose proof (f_equal fst MR) as REL.
      pose proof (f_equal snd MR) as AI.
      change (d.(Rewrite.ai) = pad_to (csum a.(Rewrite.bi') (map chunksize d.(chunks)) (len d.(chunks))) 10) in AI.
      unfold makerel in REL. cbn beta iota zeta delta [fst] in REL.
      rewrite <-AI in REL.
      assert (RJ : d.(Rewrite.rel) j =
        if ((a.(Rewrite.bi') <=? j) && (j <? d.(Rewrite.ai)))%uint63 then d.(Rewrite.ai)
        else if (j <? 1<<61)%uint63 then j else d.(Rewrite.ai)).
      { rewrite REL, IN. reflexivity. }
      destruct ((a.(Rewrite.bi') <=? j) && (j <? d.(Rewrite.ai)))%uint63 eqn:POOL.
      + apply ABORT. exact RJ.
      + destruct (j <? 1<<61)%uint63 eqn:FIT; [|apply ABORT; exact RJ].
        rewrite RJ.
        assert (OUT : toN j < bi' \/ bi' + lensC cnks <= toN j).
        { rewrite (arg_same a d D). rewrite (arg_same a d D) in END. lia. }
        split; [lia|]. split.
        * right. unfold irel. rewrite findchunk_out; [reflexivity|exact noovfl|].
          rewrite <-nlen_flat. exact OUT.
        * left. unfold is_ext_addr. apply orb_true_iff. destruct OUT as [OUT|OUT].
          -- left. apply N.ltb_lt. lia.
          -- right. apply N.leb_le. lia.
  Qed.

  Lemma resolve_raddr_val : forall j,
    toN (resolve d (Raddr j)) = toN (d.(Rewrite.rel) j) * 4.
  Proof.
    intro j. pose proof (relocation_endpoint j) as (TB&_&_).
    unfold resolve. nify. rewrite N.shiftl_mul_pow2. lia.
  Qed.

  Section ChunkCases.
    Variable n : nat.
    Variable c0 : chunk ().
    Variable c1 sz : chunk (list cinst).
    Variable c2 : chunk (list list3).
    Variable c3 : chunk (list int).

    Definition i := c0.(ci).
    Definition i' := bi' + lensC[:n] cnks.
    Definition ni' := bi' + lensT[:S n] tc.

    Notation c := c3.(cd).

    Variable NTH : ith d.(chunks) n = Some c1.
    Variable R1: c1 = change_szs (setd c0 (rw_inst a c0)) sz.
    Variable R2: c2 = setd c1 (instmapi (rel c1.(ci)) (isel d) c1.(cd)).
    Variable R3: c3 = setd c2 (concat (map l3l c2.(cd))).
    Lemma NTH2: ith cnks n = Some c3.
    Proof.
      by rewrite (chunk_equiv _ _ RW), ith_map, NTH, R3, R2.
    Qed.
    Lemma no_lst0:
      Forall (.≠ Lst0) c2.(cd).
    Proof.
      rewrite R2. simpl. eapply no_lst0.
      - apply RW.
      - eapply ith_In, NTH.
    Qed.

    Lemma irel_in:
      forall n (N: n <ₒ length c), irel (i' + n) = ♮i.
    Proof.
      intros. unfold i, i', irel.
      rewrite nlen_flat, <-!firstn_map, findchunk_in' with (d:=C[nil]).
      - by rewrite (ith_nth _ _ _ _ NTH2), R3, R2, R1.
      - eapply nonempty_cnks, RW.
      - apply ith_Some. by rewrite NTH2.
      - rewrite (ith_nth _ _ _ _ NTH2), nlen_length. lia.
    Qed.
    Lemma irel_i:
      irel i' = ♮i.
    Proof.
      replace i' with (i' + O) by lia. rewrite irel_in. lia.
      destruct c eqn:e. pose proof (nonempty_cnks _ _ RW).
      eapply Forall_forall in H. unfold Nonempty in H. by rewrite e in H.
      eapply ith_In, NTH2.
      simpl. lia.
    Qed.
    Lemma not_ext:
      forall n (N: n <ₒ length c), is_ext_addr 4(i' + n) = false.
    Proof.
      intros. unfold is_ext_addr, i'. rewrite !nlen_flat, <-!firstn_map.
      lia with (nsum_firstn_le (cmap nlen cnks) (S n)) by
        erewrite nsum_take_Sn', nlen_length by by rewrite !ith_map, NTH2.
    Qed.
    Notation favs P := (forall (s:store) (VS: store_invs s), P s) (only parsing).
    Notation Goal := (favs (K_nib false (Addr 4(i'+0)))) (only parsing).
    Lemma code: forall s (VS: mem_invs s), MemHas s c i' 4.
    Proof.
      intros. destruct_and! VS. unfold i'.
      rewrite nlen_flat', <-firstn_map.
      apply memhas_ith.
      - by rewrite ith_map, NTH2.
      - by rewrite flat_map_concat_map in H1.
    Qed.
    Lemma code_exec:
      forall s (VS: mem_invs s) j (J: j <ₒ length c),
      xbits (s UXN) (4(i' + j) mod 2^64) (N.succ (4(i' + j) mod 2^64)) = 0.
    Proof.
      intros. destruct VS as (MDL&CODE&DATA&NWC&NWD&EXC).
      pose proof (not_ext j J) as BOUNDS. unfold is_ext_addr in BOUNDS.
      pose proof noovfl as NO. rewrite <-nlen_flat in NO.
      rewrite N.mod_small by lia.
      erewrite xbits_inner, EXC, xbits_0_l; [reflexivity|lia|lia].
    Qed.
    Lemma KHere:
      forall x s
        (I: match x with
            | Addr a => is_ext_addr a ∨ is_chunk_start_addr a
            | _ => True
            end)
        (VS: store_invs s),
      K_ni x s.
    Proof.
      intros until 3. apply NIHere'.
      cbv[true_inv effinv K_invs K_inv_point].
      destruct x; try done.
      apply orb_prop_intro, Is_true_true in I. by rewrite I.
    Qed.
    Lemma ith_Some':
      forall A l i (a:A), ith l i = Some a -> i <ₒ length l.
    Proof.
      intros. apply ith_Some. by rewrite H.
    Qed.
    Definition cons2{A} (a:A) b t : a::b::t = [a;b]++t := eq_refl.
    Lemma mem_invs_step:
      forall t0 x s
        (XP: exec_prog a64prog ((x,s)::t0))
        (VS: hdP mem_invs t0),
      hdP mem_invs ((x,s)::t0).
    Proof.
      intros. destruct t0; try done. destruct p as [x0 s0].
      rewrite cons2 in XP. apply exec_prog_split in XP as (_&_&XP).
      destruct VS as (MDL&CODE&DATA&NWC&NWD&EXC).
      inversion XP. inversion H1. subst. clear H1 H2.
      repeat so LU; subst. apply (noassign_stmt_same A_WRITE) in XS as AW; [|apply noassign_awrite_arm2il].
      apply (noassign_stmt_same UXN) in XS as UX; [|apply noassign_uxn_arm2il].
      repeat split.
      - eapply (preservation_exec_prog _ welltyped_arm8_prog); by try apply XP.
      - intros j m ITH. cbn. erewrite <-nonwritable_mem_arm2il. by apply CODE. apply XS. intros.
        rewrite testbit_xbits. destruct (N.lt_decidable k (2^64)).
        + pose proof (proj1 (ith_Some (flat_map cd cnks) j) ltac:(by rewrite ITH)).
          remember (bi' * _ + j * 4) as n0.
          destruct (N.lt_decidable k n0).
          * assert (bi' * 4 + lensC cnks * 4 < 2 ^ 64) by
              (rewrite nlen_flat; lia with noovfl). rewrite nlen_length in H3.
            lia with (msub_wrap 64 k n0).
          * rewrite msub_sub, N.mod_small in H by lia. erewrite xbits_inner, NWC, xbits_0_l. easy. lia. rewrite nlen_length. lia.
        + rewrite xbits_above; auto. specialize (MDL A_WRITE _ ltac:(done)).
          eapply (N.lt_le_trans _ _ _ MDL), N.pow_le_mono_r; clear -H0; lia.
      - intros j m ITH. cbn. erewrite <-nonwritable_mem_arm2il. by apply DATA. apply XS. intros.
        rewrite testbit_xbits. destruct (N.lt_decidable k (2^64)).
        + pose proof (proj1 (ith_Some (flat_map tblcontent tc) j) ltac:(by rewrite ITH)).
          remember (bti * _ + j * 8) as n0.
          destruct (N.lt_decidable k n0).
          * assert (bti * 4 + lensT tc * 8 < 2 ^ 64) by (pose proof tables_noovfl; lia). rewrite nlen_length in H3.
            lia with (msub_wrap 64 k n0).
          * rewrite msub_sub, N.mod_small in H by lia. erewrite xbits_inner, NWD, xbits_0_l. easy. lia. rewrite nlen_length. lia.
        + rewrite xbits_above; auto. specialize (MDL A_WRITE _ ltac:(done)).
          eapply (N.lt_le_trans _ _ _ MDL), N.pow_le_mono_r; clear -H0; lia.
      - inversion AW. cbn; by rewrite <-H0.
      - inversion AW. cbn; by rewrite <-H0.
      - inversion UX. cbn; by rewrite <-H0.
    Qed.
    Lemma KStep:
      forall b j s q
        (VS: store_invs s)
        (Q: ith (map (arm_decode ∘ toN) c) j = Some q)
        (STEP: forall c1 s1 x1
        (XS: exec_stmt arm8typctx s (a64lift 4(i'+j) q) c1 s1 x1)
          (VS: mem_invs (reset_temps s s1)),
          PermittedStep (
            exitof 4(i'+S j) x1, reset_temps s s1,
           (Addr 4(i'+j), s)
          ) ∧ K_ni (exitof 4(i'+S j) x1) (reset_temps s s1)),
      K_nib b (Addr 4(i'+j)) s.
    Proof.
      intros.
      rewrite ith_map in Q. repeat so Q.
      assert (a64prog s ((i'+j)*4) = Some (4, a64lift 4(i'+j) q)) as P.
      { unfold a64prog. rewrite (mp2_mod_mul _ 2).
        rewrite code_exec by (apply (proj1 VS) || by eapply ith_Some').
        by rewrite N.mul_add_distr_r, (code s (proj1 VS) j _ oe), Q. }
      destruct (is_chunk_start_addr 4(i' + j) && b) eqn:S.
      { fwd. apply KHere; auto. }
      intro. eapply NIStep'.
      - cbv [effinv K_invs effinv' K_exits K_inv_point].
        rewrite not_ext by by eapply ith_Some'.
        destruct b; fwd; by case_match.
      - apply P.
      - intros. rewrite cons1.
        rewrite Nat2N.inj_succ, N.add_succ_r, N.mul_succ_l in STEP.
        specialize (STEP _ _ _ XS). hintro STEP.
        + fwd. apply clear_trace'.
          * by apply STEPp1.
          * by apply Forall_singleton.
        + eapply mem_invs_step.
          * apply exec_prog_step; [apply exec_prog_none|econstructor; apply P || apply XS].
          * by destruct VS.
    Qed.
    Definition cidx' x n := list_sum (take n (map (toNat ∘ instsize) x)).
    Lemma cidx_Sn:
      forall x n, cidx' x (S n) = (cidx' x n + nth n (map (toNat ∘ instsize) x) O)%nat.
    Proof.
      unfold cidx'. intros. rewrite !list_sum_N, <-!firstn_map, nsum_take_Sn, map_map.
      rewrite N2Nat.inj_add, <-map_map. change 0 with (N.of_nat O). rewrite map_nth. lia.
    Qed.
    Lemma cidx_Sn':
      forall n x y, ith y n = Some x -> cidx' y (S n) = (cidx' y n + ♮(instsize x))%nat.
    Proof.
      intros. rewrite cidx_Sn. f_equal. eapply ith_nth. by rewrite ith_map, H.
    Qed.
    Definition cidx_cons a t n: cidx' (a::t) (S n) = (♮(instsize a) + cidx' t n)%nat := eq_refl.
    Notation cidx := (cidx' c1.(cd)).
    (* Slicing the concatenated output of a mapped instruction list: the part
       starting at the j-th instruction's offset is its expansion followed by
       the rest. *)
    Lemma instmapi_drop:
      forall (f: int -> cinst -> list3)
        (SZ: forall ip x, f ip x <> Lst0 -> length (l3l (f ip x)) = toNat (instsize x)),
      forall L ip,
        Forall (.≠ Lst0) (instmapi ip f L) ->
        forall j x, ith L j = Some x ->
          @eq (list int) (drop (cidx' L j) (concat (map l3l (instmapi ip f L))))
            (List.app (l3l (f (ip + ofNat (cidx' L j))%uint63 x))
              (drop (cidx' L (S j)) (concat (map l3l (instmapi ip f L))))) /\
          f (ip + ofNat (cidx' L j))%uint63 x <> Lst0.
    Proof.
      intros f SZ. induction L as [|y L IH]; intros ip NL j x A; [discriminate|].
      unfold instmapi in NL |- *. rewrite mapi_cons in NL |- *. cbn [rev app map concat] in NL |- *.
      inversion NL as [|? ? NL0 NL1]; subst.
      change (_mapi instsize [] (ip + instsize y)%uint63 f L)
        with (instmapi (ip + instsize y)%uint63 f L) in *.
      pose proof (SZ ip y NL0) as LEN.
      destruct j as [|j].
      - cbn in A. injection A as <-.
        replace (ip + ofNat (cidx' (y::_) 0))%uint63 with ip by (unfold cidx'; simpl; lia).
        rewrite cidx_cons. replace (♮(instsize y) + cidx' L 0)%nat with (length (l3l (f ip y)))
          by (unfold cidx'; simpl; lia).
        split; [|exact NL0].
        unfold cidx'. simpl take. rewrite drop_app_length. reflexivity.
      - cbn in A.
        destruct (IH (ip + instsize y)%uint63 NL1 j x A) as [E NE].
        rewrite !cidx_cons.
        replace (♮(instsize y) + cidx' L (S j))%nat with (length (l3l (f ip y)) + cidx' L (S j))%nat by lia.
        replace (♮(instsize y) + cidx' L j)%nat with (length (l3l (f ip y)) + cidx' L j)%nat by lia.
        rewrite !drop_app_add, E.
        replace (ip + ofNat (length (l3l (f ip y)) + cidx' L j))%uint63
          with ((ip + instsize y) + ofNat (cidx' L j))%uint63 by (rewrite LEN; lia).
        split; [reflexivity|exact NE].
    Qed.
    Lemma cidxn:
      forall {j x}
        (A: ith c1.(cd) j = Some x),
      drop (cidx j) c3.(cd) =
      (l3l (isel d ♯(i' + cidx j) x)) ++ drop (cidx (S j)) c3.(cd) /\
      isel d ♯(i' + cidx j) x <> Lst0.
    Proof.
      intros j x A.
      pose proof (rel_start n c1 NTH) as REL.
      pose proof no_lst0 as NL. rewrite R2 in NL. cbn in NL. rewrite REL in NL.
      destruct (instmapi_drop (isel d) (instsize_correct' d) c1.(cd) (ofN i') NL j x A) as [E NE].
      replace (♯(i' + cidx j)) with (ofN i' + ofNat (cidx j))%uint63 by lia.
      rewrite R3, R2. cbn. rewrite REL.
      split; [exact E|exact NE].
    Qed.
    Lemma cidx_bound':
      forall j, cidx j + nth j (map (toNat ∘ instsize) c1.(cd)) O <= nlen c.
    Proof.
      intro. specialize no_lst0. rewrite R3, R2, <-flat_map_concat_map. simpl. rewrite nlen_flat, map_map.
      unfold cidx. rewrite list_sum_N. clear. generalize (rel c1.(ci)), j. unfold instmapi.
      induction c1.(cd); simpl; intros.
      - rewrite take_nil. by case_match.
      - rewrite mapi_acc in *. simpl. inversion H.
        erewrite <-instsize_correct, len_nlen in * by apply H2.
        destruct j0; simpl; rewrite !nsum_cons. destruct isel; cbn; lia.
        specialize (IHl _ j0 H3). lia.
    Qed.
    Lemma cidx_bound:
      forall j, cidx j <= nlen c.
    Proof.
      intro. lia with (cidx_bound' j).
    Qed.
    Lemma i'cidx_bound:
      forall j, i' + cidx j < 2 ^ 62.
    Proof.
      intro. unfold i'. apply N.le_lt_trans with (bi' + lensC[:S n] cnks).
      - rewrite <-N.add_assoc. apply N.add_le_mono_l.
        erewrite !nlen_flat, <-!firstn_map, nsum_take_Sn' by by rewrite !ith_map, NTH2.
        apply N.add_le_mono_l. apply cidx_bound.
      - eapply N.le_lt_trans, noovfl. rewrite nlen_flat, <-!firstn_map.
        lia with (nsum_firstn_le (cmap nlen cnks) (S n)).
    Qed.
    Lemma instmapi_len:
      forall L ip,
        Forall (.≠ Lst0) (instmapi ip (isel d) L) ->
        list_sum (map (toNat ∘ instsize) L) =
        length (concat (map l3l (instmapi ip (isel d) L))).
    Proof.
      induction L as [|y L IH]; intros ip NL; [done|].
      unfold instmapi in NL |- *. rewrite mapi_cons in NL |- *.
      cbn [rev app map concat list_sum] in NL |- *.
      inversion NL as [|? ? NL0 NL1]; subst.
      change (_mapi instsize [] (ip + instsize y)%uint63 (isel d) L)
        with (instmapi (ip + instsize y)%uint63 (isel d) L) in *.
      rewrite length_app, (instsize_correct' d ip y NL0), <-(IH _ NL1). reflexivity.
    Qed.
    Lemma cidx_all:
      forall j, (length c1.(cd) <= j)%nat -> cidx j = length c.
    Proof.
      intros j J.
      pose proof (rel_start n c1 NTH) as REL.
      pose proof no_lst0 as NL. rewrite R2 in NL. cbn in NL. rewrite REL in NL.
      rewrite R3, R2. cbn. rewrite REL.
      unfold cidx'. rewrite take_ge by (rewrite length_map; lia).
      exact (instmapi_len c1.(cd) (ofN i') NL).
    Qed.
    Lemma irel_next:
      forall j, (S n < length d.(chunks) ->
        length c1.(cd) <= j -> irel (i' + cidx j) = S ♮i)%nat.
    Proof.
      intros j NEXT J. rewrite (cidx_all j J).
      pose proof (source_nth a d D n c1 NTH) as (CI&DEC&POL&LAST&LT).
      assert (POS : i' + nlen c = toN d.(arg).(Rewrite.bi') + nlen (flat_map cd (take (S n) cnks))).
      { unfold i'. rewrite !nlen_flat, <-!firstn_map.
        erewrite nsum_take_Sn' by (rewrite !ith_map, NTH2; reflexivity).
        lia. }
      rewrite nlen_length in POS.
      rewrite POS, (following_irel n c3 NTH2 NEXT). rewrite R3, R2, R1. cbn.
      unfold i. lia.
    Qed.
    Lemma ExecInum:
      forall b j s n
        (VS: store_invs s)
        (Q: ith c1.(cd) j = Some (Inum n))
        (STEP: forall c1 s1 x1
          (XS: exec_stmt arm8typctx s (a64lift 4(i'+cidx j) (arm_decode ♮n)) c1 s1 x1)
          (VS: mem_invs (reset_temps s s1)),
          PermittedStep (
            exitof 4(i'+cidx (S j)) x1, reset_temps s s1,
           (Addr 4(i'+cidx j), s)
          ) ∧ K_ni (exitof 4(i'+cidx (S j)) x1) (reset_temps s s1)),
        K_nib b (Addr 4(i'+cidx j)) s.
    Proof.
      intros. eapply KStep; auto.
      - by rewrite ith_skipn_hd, skipn_map, (proj1 (cidxn Q)).
      - intros. eqapply (STEP c4 s1 x1 XS VS0).
        all: rewrite (cidx_Sn' _ _ _ Q); simpl; lia.
    Qed.
    Lemma ExecIimm:
      forall b relax j s sz r imm
        (VS: store_invs s)
        (R: (r <? 32 = true)%uint63)
        (Q: ith c1.(cd) j = Some (Iimm relax sz r imm))
        (EDGE: PermittedEdge' i' (i'+cidx (S j)))
        (STEP: K_ni (Addr 4(i'+cidx (S j))) (s.[arm_varid ♮r := ♮(resolve d imm)])),
        K_nib b (Addr 4(i'+cidx j)) s.
    Proof.
      intros. destruct (cidxn Q) as [C NL0]. simpl in C, NL0.
      pose proof (cidx_Sn' _ _ _ Q) as CSJ.
      pose proof (cidx_bound (S j)) as CLL; rewrite CSJ, nlen_length in CLL.
      pose proof (i'cidx_bound j) as ICB.
      pose proof (irel_i) as IRI.
      pose proof (irel_in (cidx j)) as IRCJ.
      repeat case_match; try done; simpl in CLL, CSJ.
      Ltac blia := rewrite ?N.shiftr_div_pow2, ?N.shiftl_mul_pow2, ?land16, ?land3 in *; lia.
      Ltac step C := eapply KStep; [try done | by rewrite ith_skipn_hd, skipn_map, <-?List.tl_skipn, C | intros ?c?s?x?XS?MI].
      Ltac inchunk := repeat eexists; [eapply IntraChunkEdge; rewrite !irel_in; blia|].
      Ltac outchunk := match goal with EDGE: PermittedEdge' _ _ |- _ => repeat eexists; [eapply PEirel; [|eqapply EDGE]; rewrite ?irel_in; blia|] end.
      - destruct Asm.ADRP eqn:ADRP; try done.
        step C. repeat so ADRP. subst i0. simpl in XS.
        apply (ExecADRP19 H1) in XS as [S' X']; [|lia].
        replace (lsr _ 10) with ♯((i' + cidx j) >> 10) in S' by blia.
        rewrite plusminus52 in S' by blia. subst x. simpl exitof.
        outchunk. eqapply STEP. lia. eqapply S'. unfold clearlow12 in H0. blia.
      - destruct Asm.ADR eqn:ADR; try done.
        step C. repeat so ADR. subst i0. simpl in XS.
        apply (ExecADR19 H1) in XS as [S' X']; [|blia..].
        subst x. simpl exitof.
        outchunk.
        rewrite S', plusminus62 by lia.
        eqapply STEP; try lia. nify. by rewrite <-(N.shiftl_mul_pow2 _ 2), recompose_bytes'.
      - destruct Asm.ADRP eqn:ADRP.
        + step C. repeat so ADRP. subst i0. simpl in XS.
          apply (ExecADRP19 H1) in XS as [S' X']; [| lia].
          subst x. simpl exitof.
          inchunk.
          replace (lsr _ 10) with ♯((i' + cidx j) >> 10) in S' by blia.
          rewrite plusminus52 in S' by blia. subst' S'. clear c s0.
          step C.
          apply ExecMovk in XS as [S' X']; [|blia..].
          rewrite update_updated, update_cancel in S'.
          subst x. simpl exitof.
          outchunk. eqapply STEP. lia. rewrite S'. f_equal.
          apply movk_adrp.
        + step C; apply ExecUDF in XS as [S' X']; subst; repeat eexists; by apply KHere.
      - step C.
        apply ExecMovz in XS as [S' X']; [|lia..].
        subst x. simpl exitof.
        inchunk. simp (_<<4). subst' S'. clear c s0.
        step C. apply ExecMovk in XS as [S' X']; [|blia..].
        rewrite update_updated, update_cancel in S'.
        subst x. simpl exitof.
        outchunk. eqapply STEP. lia. rewrite S'. f_equal.
        apply movk_z1.
      - step C.
        apply ExecMovz in XS as [S' X']; [|blia..].
        subst x. simpl exitof.
        inchunk. simp (_<<4). subst' S'. clear c s0.
        step C. apply ExecMovk in XS as [S' X']; [|blia..].
        rewrite update_updated, update_cancel in S'.
        subst x. simpl exitof.
        inchunk. simp (_<<4). subst' S'. clear c s0.
        step C. apply ExecMovk in XS as [S' X']; [|blia..].
        rewrite update_updated, update_cancel in S'.
        subst x. simpl exitof.
        outchunk. eqapply STEP. lia. rewrite S'. f_equal.
        apply movk_z2. blia.
      Qed.
    Ltac cones :=
      let rec loop n :=
                match n with
                | 0%nat => idtac
                | S ?n' =>
                    let z := eval vm_compute in (ofNat n) in
                    let i := eval vm_compute in (ones z) in
                    change i with (ones z); loop n'
                end
        in loop 63%nat.
    (* discharge the register/field range side conditions of the Exec lemmas *)
    Ltac sidecond :=
      match goal with
      | |- (_ <? _ = true)%uint63 =>
          cones; first [rewrite landones; lia | (destruct is_zero; simpl; lia)]
      end.
    Lemma ExecIb:
      forall b j s sz r t
        (VS: store_invs s)
        (Q: ith c1.(cd) j = Some (Ib sz t r))
        (EDGE: PermittedEdge' (i'+cidx j) ♮(resolve d r >> 2))
        (STEP: favs (K_ni (Addr (♮(resolve d r >> 2) * 4))))
        (EDGE': match t with
                | Decode.BL _
                | Decode.B _ => True
                | _ => PermittedEdge' (i'+cidx j) (i'+cidx (S j))
                end)
        (STEP': match t with
                | Decode.BL _
                | Decode.B _ => True
                | _ => K_ni (Addr 4(i'+cidx (S j))) s
                end),
        K_nib b (Addr 4(i'+cidx j)) s.
    Proof.
      intros. destruct (cidxn Q) as [C NL0]. simpl in C, NL0.
      pose proof (cidx_Sn' _ _ _ Q) as CSJ.
      pose proof (cidx_bound (S j)) as CLL; rewrite CSJ, nlen_length in CLL.
      pose proof (i'cidx_bound j) as ICB.
      pose proof (i'cidx_bound (S j)) as ICB'.
      pose proof (irel_i) as IRI.
      pose proof (irel_in (cidx j)) as IRCJ.
      repeat case_match; try done; simpl in CLL, CSJ.
      - destruct Asm.Bcond eqn:BCOND; try done.
        step C. simpl in XS. repeat so BCOND. subst i0.
        eapply (ExecBcond _ H1) in XS as [S' X'].
        Unshelve. all: try sidecond.
        destruct X'; subst x; simpl exitof.
        rewrite plusminus62 by lia.
        outchunk. by apply STEP.
        outchunk. eqapply STEP'; auto; lia.
      - destruct Asm.B eqn:B.
        step C. simpl in XS. repeat so B. subst i0.
        apply (ExecB H1) in XS as [S' X'].
        subst x. simpl exitof.
        rewrite plusminus62 by lia.
        outchunk. by apply STEP.
        step C. apply ExecUDF in XS as [S' X'].
        subst. repeat eexists. by apply KHere.
      - destruct Asm.BL eqn:BL.
        + step C. simpl in XS. repeat so BL. subst i0.
          apply (ExecBL H1) in XS as [S' X'].
          subst x. simpl exitof.
          rewrite plusminus62 by lia.
          outchunk. by apply STEP.
        + step C. apply ExecUDF in XS as [S' X'].
          subst. repeat eexists. by apply KHere.
      - destruct Asm.CBZ eqn:CBZ; try done.
        step C. simpl in XS. repeat so CBZ. subst i0.
        eapply (ExecCBZ _ _ _ H1) in XS as [S' X'].
        Unshelve. all: try sidecond.
        destruct X'; subst x; simpl exitof.
        rewrite plusminus62 by lia.
        outchunk. by apply STEP.
        outchunk. eqapply STEP'; auto; lia.
      - destruct Asm.TBZ eqn:TBZ; try done.
        step C. simpl in XS. repeat so TBZ. subst i0.
        eapply (ExecTBZ _ _ _ _ H1) in XS as [S' X'].
        Unshelve. all: try sidecond.
        destruct X'; subst x; simpl exitof.
        rewrite plusminus62 by lia.
        outchunk. by apply STEP.
        outchunk. eqapply STEP'; auto; lia.
      - destruct Asm.Bcond eqn:BCOND; destruct Asm.B eqn:B; try done.
        + step C. simpl in XS. repeat so BCOND. subst i0.
          eapply (ExecBcond _ H1) in XS as [S' X'].
        Unshelve. all: try sidecond.
          destruct X'; subst x; simpl exitof.
          rewrite plusminus62 by lia.
          outchunk. eqapply STEP'; auto; lia.
          inchunk. subst' S'. clear c s0.
          step C. simpl in XS. repeat so B. subst i1.
          apply (ExecB H2) in XS as [S' X'].
          subst x; simpl exitof.
          replace (add _ _) with ♯(i' + S(cidx j)) by lia.
          rewrite plusminus62 by lia.
          outchunk. by apply STEP.
        + step C. apply ExecUDF in XS as [S' X'].
          subst. repeat eexists. by apply KHere.
      - destruct Asm.CBZ eqn:CBZ; destruct Asm.B eqn:B; try done.
        + step C. simpl in XS. repeat so CBZ. subst i0.
          eapply (ExecCBZ _ _ _ H1) in XS as [S' X'].
        Unshelve. all: try sidecond.
          destruct X'; subst x; simpl exitof.
          rewrite plusminus62 by lia.
          outchunk. eqapply STEP'; auto; lia.
          inchunk. subst' S'. clear c s0.
          step C. simpl in XS. repeat so B. subst i1.
          eapply (ExecB H2) in XS as [S' X'].
          subst x; simpl exitof.
          replace (add _ _) with ♯(i' + S(cidx j)) by lia.
          rewrite plusminus62 by lia.
          outchunk. by apply STEP.
        + step C. apply ExecUDF in XS as [S' X'].
          subst. repeat eexists. by apply KHere.
      - destruct Asm.TBZ eqn:TBZ; destruct Asm.B eqn:B; try done.
        + step C. simpl in XS. repeat so TBZ. subst i0.
          eapply (ExecTBZ _ _ _ _ H1) in XS as [S' X'].
        Unshelve. all: try sidecond.
          destruct X'; subst x; simpl exitof.
          rewrite plusminus62 by lia.
          outchunk. eqapply STEP'; auto; lia.
          inchunk. subst' S'. clear c s0.
          step C. simpl in XS. repeat so B. subst i1.
          eapply (ExecB H2) in XS as [S' X'].
          subst x; simpl exitof.
          replace (add _ _) with ♯(i' + S(cidx j)) by lia.
          rewrite plusminus62 by lia.
          outchunk. by apply STEP.
        + step C. apply ExecUDF in XS as [S' X'].
          subst. repeat eexists. by apply KHere.
    Qed.
    Lemma ExecIhsh:
      forall b j s r lbl h
        (VS: store_invs s)
        (Q: ith c1.(cd) j = Some (Ihsh r lbl))
        (R: (r <? 31 = true)%uint63)
        (H: (nth ♮lbl tc (Build_table h nil 0)).(tblhash) = h)
        (H': match h with
             | Hash.H_UBFX lsb width => ((lsb <? 64) && (width-1 <? 62) && (lsb+width-1 <? 64) = true)%uint63
             | Hash.H_EOR_UBFX shift lsb width => ((shift <? 32) && (lsb <? 64) && (width-1 <? 62) && (lsb+width-1 <? 64) = true)%uint63
             end)
        (EDGE: PermittedEdge' i' (i'+cidx (S j)))
        (STEP: forall x (X: x < ♮(Hash.hash_size h)),
          K_ni (Addr 4(i'+cidx (S j))) (s.[arm_varid ♮r := x])
        ),
        K_nib b (Addr 4(i'+cidx j)) s.
    Proof.
      intros. destruct (cidxn Q) as [C NL0]. simpl in C, NL0.
      pose proof (cidx_Sn' _ _ _ Q) as CSJ; simpl in CSJ.
      pose proof (cidx_bound (S j)) as CLL; rewrite CSJ, nlen_length in CLL.
      pose proof (i'cidx_bound j) as ICB.
      pose proof (i'cidx_bound (S j)) as ICB'.
      pose proof (irel_i) as IRI.
      pose proof (irel_in (cidx j)) as IRCJ.
      case_match; try done.
      so H0. rewrite Util.ith_nth_error in H1.
      erewrite (nth_error_nth _ _ _ H1) in H. subst'' H0. subst h.
      destruct h0.
      - step C. simpl in XS.
        apply ExecNOP in XS as [S' X'].
        subst x0. simpl exitof.
        inchunk. subst' S'. clear c s0.
        step C. simpl in XS.
        apply ExecUBFX6 in XS as [m [S' [X' M]]]; try lia.
        subst x0. simpl exitof.
        outchunk. subst' S'. specialize (STEP m). hintro STEP.
        eqapply STEP. lia. eqapply M. simpl. nify.
        rewrite N.mod_small. blia. rewrite N.shiftl_mul_pow2, N.mul_1_l. apply N.pow_lt_mono_r; lia.
      - step C. simpl in XS.
        apply ExecEOR in XS as [m0 [S' X']]; try lia.
        subst x0. simpl exitof.
        inchunk. subst' S'. clear c s0.
        step C. simpl in XS.
        apply ExecUBFX6 in XS as [m [S' [X' M]]]; try lia.
        subst x0. simpl exitof.
        outchunk. subst' S'. rewrite update_cancel. specialize (STEP m). hintro STEP.
        eqapply STEP. lia. eqapply M. simpl. nify.
        rewrite N.mod_small. blia. rewrite N.shiftl_mul_pow2, N.mul_1_l. apply N.pow_lt_mono_r; lia.
    Qed.


    (* Any chunk consisting of an abort branch reaches the abort target or
       raises an exception if the branch cannot be encoded. *)
    Lemma chunk_abort:
      (exists k, c1.(cd) = [Ib k (Decode.BL 0) (Rrt 0)]) -> Goal.
    Proof.
      intros ABORT s VS.
      destruct ABORT as [k CD1].
      pose proof no_lst0 as NL.
      rewrite R2 in NL. cbn in NL. rewrite CD1 in NL.
      destruct k; try (cbn in NL; inversion NL; contradiction).
      assert (REL : d.(Rewrite.rel) c1.(ci)=ofN i') by exact (rel_start n c1 NTH).
      assert (CODE : c3.(cd)=[Asm.BL (ofN i') (resolve d (Rrt 0)>>2) orelse Asm.UDF]).
      { rewrite R3,R2. cbn. rewrite CD1,REL. unfold instmapi. rewrite mapi_cons. cbn.
        change (l3l ((option_map Lst1 (Asm.BL (ofN i') (resolve d (Rrt 0)>>2))) orelse (Lst1 Asm.UDF)) ++ [] = [Asm.BL (ofN i') (resolve d (Rrt 0)>>2) orelse Asm.UDF]).
        destruct (Asm.BL (ofN i') (resolve d (Rrt 0)>>2)); reflexivity. }
      assert (TARGET : toN (resolve d (Rrt 0)>>2)=toN d.(Rewrite.ai)).
      { pose proof (ai_bound a d D) as AI. unfold resolve. nify.
        rewrite N.shiftl_mul_pow2,N.shiftr_div_pow2. lia. }
      assert (IPB : (i'<2^62)%N).
      { pose proof noovfl as NO.
        pose proof (nsum_firstn_le (cmap nlen cnks) n).
        unfold i'. rewrite nlen_flat,<-!firstn_map. lia. }
      assert (TARGETB : (resolve d (Rrt 0)>>2 <? 1<<62=true)%uint63) by (pose proof (ai_bound a d D);lia).
      unfold Asm.BL in CODE.
      destruct (Asm.bounded ((resolve d (Rrt 0)>>2)-ofN i') 26) as [imm|] eqn:IMM; cbn in CODE.
      + eapply KStep with (j:=0%nat) (q:=arm_decode (toN (Asm.Encode.BL imm))); [exact VS|rewrite CODE;reflexivity|].
        intros ctx s1 x XS MI.
        apply (ExecBL IMM) in XS as [ST EXIT].
        rewrite N.add_0_r in EXIT. fold i' in EXIT.
        rewrite plusminus62 in EXIT by assumption.
        rewrite TARGET in EXIT. subst x. split.
        * cbn [exitof PermittedStep]. repeat eexists. apply AbortEdge.
        * apply KHere; [|split;[exact MI|exact I]].
          left. unfold is_ext_addr.
          assert (EXT : ((toN d.(arg).(Rewrite.bi')+nlen(flat_map cd cnks))*4 <=? toN d.(Rewrite.ai)*4)%N =true) by (apply N.leb_le;pose proof abort_after_code;lia).
          rewrite EXT,orb_true_r. exact I.
      + eapply KStep with (j:=0%nat) (q:=arm_decode (toN Asm.UDF)); [exact VS|rewrite CODE;reflexivity|].
        intros ctx s1 x XS MI. apply ExecUDF in XS as [ST EXIT]. subst x.
        split; [exact I|apply KHere; [exact I|split;[exact MI|exact I]]].
    Qed.

    Lemma chunk_ignore : c0.(ct)=Decode.ignore ->
     forall s, store_invs s -> K_nib false (Addr ((i'+0)*4)) s.
    Proof.
     intros CT s VS.
     pose proof (source_nth a d D n c1 NTH) as (CI&DEC&POL&LAST&BOUND).
     assert (META : metadata c1=c0).
     { rewrite R1. unfold change_szs,metadata,setd. destruct c0 as [cn ci ct cp cl []]. reflexivity. }
     assert (DEC0 : Decode.decode c0.(cn)=Decode.ignore).
     { rewrite <-META in CT |- *. cbn in CT |- *. exact (eq_trans DEC CT). }
     assert (POL0 : c0.(cp)=d.(arg).(Rewrite.pol) c0.(ci)).
     { rewrite <-META. cbn. rewrite (arg_same a d D). exact POL. }
     (* A permitted fallthrough reaches the following chunk. *)
     destruct (isfallthrough c0) eqn:FT.
     - assert (CD1 : c1.(cd)=[Inum c0.(cn)]).
       { rewrite R1. cbn. unfold rw_inst. rewrite CT,FT. destruct sz.(cd); reflexivity. }
       assert (CODE : c3.(cd)=[c0.(cn)]).
       { rewrite R3,R2. cbn. rewrite CD1. reflexivity. }
       assert (NL : c1.(cl)=false).
       { change ((metadata c1).(cl)=false). rewrite META. exact (fallthrough_not_last c0 FT). }
       pose proof (not_last_has_next a d D n c1 NTH NL) as NEXT.
       assert (POS : i'+1 = toN d.(arg).(Rewrite.bi')+nlen(flat_map cd(take (S n) cnks))).
       { unfold i'. rewrite !nlen_flat,<-!firstn_map.
         erewrite nsum_take_Sn' by (rewrite !ith_map,NTH2;reflexivity).
         rewrite CODE. cbn. lia. }
       assert (IREL : irel (i'+1)=(toN c0.(ci)+1)%N).
       { rewrite POS,(following_irel n c3 NTH2 NEXT).
         rewrite R3,R2,R1. reflexivity. }
       assert (PE : PermittedEdge (toN c0.(ci)) (toN c0.(ci)+1)).
       { unfold isfallthrough in FT. destruct c0.(cp) as [b|b target| |lbl] eqn:CP; try destruct b; simpl in FT; try discriminate.
         - eqapply (FallthroughEdge c0.(ci) (eq_sym POL0)); lia.
         - eqapply (FallthroughEdge2 c0.(ci) target (eq_sym POL0)); lia.
         - apply IgnoreEdge. symmetry. exact POL0. }
       eapply KStep with (j:=0%nat) (q:=arm_decode (toN c0.(cn))); [exact VS|rewrite CODE;reflexivity|].
       intros ctx s1 x XS MI.
       pose proof (nojumps_exec _ _ _ _ _ _ XS (nonbranch_arm2il _ _ (nonbranch_decode_ignore _ DEC0))) as NJ.
       destruct x as [[addr|exc]|]; [contradiction| |].
       + split; [exact I|]. apply KHere; [exact I|split;[exact MI|exact I]].
       + split.
         * cbn [exitof PermittedStep]. repeat eexists.
           apply TranslatedEdge.
           rewrite N.add_0_r. change (PermittedEdge (irel i') (irel (i'+1))).
           assert (START : irel i'=toN c0.(ci)) by exact irel_i.
           rewrite START,IREL.
           exact PE.
         * apply KHere; [|split;[exact MI|exact I]].
           right. unfold is_chunk_start_addr.
           change (Is_true (startschunk cnks (toN d.(arg).(Rewrite.bi')) ((i'+1)*4))).
           rewrite POS,startschunk_at; [exact I|rewrite (num_cnks d cnks RW);exact NEXT].
     (* The final chunk and restrictive policies use the abort path. *)
     - apply chunk_abort; [|exact VS].
       rewrite R1. cbn. unfold rw_inst. rewrite CT,FT.
       destruct sz.(cd) as [|x xs]; [exists Sz1|exists (instsz x)]; reflexivity.
    Qed.

    Lemma chunk_straightline : isfallthrough c0=true -> straightline c ->
     forall s, store_invs s -> K_nib false (Addr ((i'+0)*4)) s.
    Proof.
     intros FT SL.
     assert (META : metadata c1=c0).
     { rewrite R1. unfold change_szs,metadata,setd. destruct c0 as [cn ci ct cp cl []]. reflexivity. }
     pose proof (source_nth a d D n c1 NTH) as (_&_&POL&_&_).
     assert (POL0 : c0.(cp)=d.(arg).(Rewrite.pol) c0.(ci)).
     { rewrite <-META. cbn. rewrite (arg_same a d D). exact POL. }
     assert (NL : c1.(cl)=false).
     { change ((metadata c1).(cl)=false). rewrite META. exact (fallthrough_not_last c0 FT). }
     pose proof (not_last_has_next a d D n c1 NTH NL) as NEXT.
     assert (POS : i'+nlen c=toN d.(arg).(Rewrite.bi')+nlen(flat_map cd(take(S n)cnks))).
     { unfold i'. rewrite !nlen_flat,<-!firstn_map.
       erewrite nsum_take_Sn' by (rewrite !ith_map,NTH2;reflexivity). lia. }
     assert (IREL : irel (i'+nlen c)=toN c0.(ci)+1).
     { rewrite POS,(following_irel n c3 NTH2 NEXT). rewrite R3,R2,R1. reflexivity. }
     assert (PE : PermittedEdge (toN c0.(ci)) (toN c0.(ci)+1)).
     { unfold isfallthrough in FT. destruct c0.(cp) as [b|b target| |lbl] eqn:CP; try destruct b; simpl in FT; try discriminate.
       - eqapply (FallthroughEdge c0.(ci) (eq_sym POL0));lia.
       - eqapply (FallthroughEdge2 c0.(ci) target (eq_sym POL0));lia.
       - apply IgnoreEdge. symmetry. exact POL0. }
     assert (ENDPOINT : forall s, store_invs s -> K_ni (Addr ((i'+nlen c)*4)) s).
     { intros s VS. apply KHere; [|exact VS]. right.
       unfold is_chunk_start_addr. rewrite POS,startschunk_at; [exact I|rewrite(num_cnks d cnks RW);exact NEXT]. }
     assert (STEPS : forall m j b s, (m+j=length c)%nat -> (0<m)%nat ->
       store_invs s -> K_nib b (Addr((i'+j)*4)) s).
     { induction m as [|m IH]; intros j b s LEN NZ VS; [lia|].
       assert (J : (j<length c)%nat) by lia.
       destruct (ith c j) as [v|] eqn:V; [|apply ith_None in V;lia].
       eapply KStep with (j:=j) (q:=arm_decode (toN v)); [exact VS|change (ith (map (arm_decode ∘ toN) c) j=Some(arm_decode(toN v)));rewrite ith_map,V;reflexivity|].
       intros ctx s1 x XS MI.
       assert (NB : nonbranch(arm_decode(toN v))).
       { unfold straightline in SL. apply Forall_forall with(x:=v) in SL; [exact SL|eapply ith_In,V]. }
       pose proof (nojumps_exec _ _ _ _ _ _ XS (nonbranch_arm2il _ _ NB)) as NJ.
       destruct x as [[addr|exc]|]; [contradiction| |].
       - split; [exact I|apply KHere;[exact I|split;[exact MI|exact I]]].
       - split.
         + cbn [exitof PermittedStep]. repeat eexists.
           destruct (Nat.lt_dec (S j) (length c)) as [MORE|DONE].
           * apply IntraChunkEdge. rewrite !irel_in by assumption. reflexivity.
           * apply TranslatedEdge.
             rewrite (irel_in j J).
             replace (N.of_nat(S j)) with (nlen c) by (rewrite nlen_length;lia).
             rewrite IREL. exact PE.
         + destruct m as [|m].
           * change (K_ni (Addr ((i'+N.of_nat(S j))*4)) (reset_temps s s1)).
             replace (N.of_nat(S j)) with (nlen c) by (rewrite nlen_length;lia).
             apply ENDPOINT. split;[exact MI|exact I].
           * apply (IH (S j) true); [lia|lia|split;[exact MI|exact I]]. }
     intros s VS. apply (STEPS (length c) 0%nat false s); [lia| |exact VS].
     pose proof (nonempty_cnks d cnks RW) as NE.
     apply Forall_forall with(x:=c3) in NE; [|eapply ith_In,NTH2].
     unfold Nonempty in NE. clear -NE. destruct c3.(cd); [contradiction|simpl;lia].
    Qed.
    Lemma chunk_ADR : forall imm rd, c0.(ct)=Decode.ADR imm rd ->
     forall s, store_invs s -> K_nib false (Addr((i'+0)*4)) s.
    Proof.
     intros imm rd CT.
     destruct (isfallthrough c0) eqn:FT.
     - apply chunk_straightline; [exact FT|].
       assert (RD : (toN rd<32)%N).
       { pose proof (source_nth a d D n c1 NTH) as (_&DEC&_&_&_).
         rewrite R1 in DEC. cbn in DEC. rewrite CT in DEC.
         exact (decoded_ADR_register _ imm rd DEC). }
       assert (CD1 : exists k, c1.(cd)=[Iimm true k rd (Rimm ((c0.(ci)<<2)+sext imm 21))]).
       { rewrite R1. cbn. unfold rw_inst. rewrite CT,FT.
         destruct sz.(cd) as [|x xs]; [exists Sz2|exists(instsz x)];reflexivity. }
       destruct CD1 as [k CD1].
       rewrite R3,R2. cbn. rewrite CD1.
       unfold instmapi. rewrite mapi_cons. cbn -[isel].
       rewrite app_nil_r. apply isel_Iimm_straightline. exact RD.
     - apply chunk_abort.
       rewrite R1. cbn. unfold rw_inst. rewrite CT,FT.
       destruct sz.(cd) as [|x xs];[exists Sz1|exists(instsz x)];reflexivity.
    Qed.

    Lemma chunk_ADRP : forall imm rd, c0.(ct)=Decode.ADRP imm rd ->
     forall s, store_invs s -> K_nib false (Addr((i'+0)*4)) s.
    Proof.
     intros imm rd CT.
     destruct (isfallthrough c0) eqn:FT.
     - apply chunk_straightline; [exact FT|].
       assert (RD : (toN rd<32)%N).
       { pose proof (source_nth a d D n c1 NTH) as (_&DEC&_&_&_).
         rewrite R1 in DEC. cbn in DEC. rewrite CT in DEC.
         exact (decoded_ADRP_register _ imm rd DEC). }
       assert (CD1 : exists k, c1.(cd)=[Iimm true k rd
         (Rimm (clearlow12 (c0.(ci)<<2)+sext (imm<<12) 33))]).
       { rewrite R1. cbn. unfold rw_inst. rewrite CT,FT.
         destruct sz.(cd) as [|x xs]; [exists Sz3|exists(instsz x)];reflexivity. }
       destruct CD1 as [k CD1].
       rewrite R3,R2. cbn. rewrite CD1.
       unfold instmapi. rewrite mapi_cons. cbn -[isel].
       rewrite app_nil_r. apply isel_Iimm_straightline. exact RD.
     - apply chunk_abort.
       rewrite R1. cbn. unfold rw_inst. rewrite CT,FT.
       destruct sz.(cd) as [|x xs];[exists Sz1|exists(instsz x)];reflexivity.
    Qed.

    Lemma chunk_Bcond : forall imm cond,
      c0.(ct) = Decode.Bcond imm cond ->
      forall s, store_invs s -> K_nib false (Addr ((i'+0)*4)) s.
    Proof.
      intros imm cond CT.
      set (target := (c0.(ci)+sext imm 19)%uint63).
      destruct (isdirect c0 false target) eqn:DIR.
      - assert (FT : isfallthrough c0 = true) by exact (isdirect_false_fallthrough c0 target DIR).
        assert (META : metadata c1 = c0).
        { rewrite R1. unfold change_szs, metadata, setd. destruct c0 as [cn ci ct cp cl []]. reflexivity. }
        pose proof (source_nth a d D n c1 NTH) as (_&_&POL&_&_).
        assert (POL0 : c0.(cp) = d.(arg).(Rewrite.pol) c0.(ci)).
        { rewrite <-META. cbn. rewrite (arg_same a d D). exact POL. }
        assert (PE : PermittedEdge (toN c0.(ci)) (toN target)).
        { unfold isdirect in DIR.
          destruct c0.(cp) as [b|b dest| |lbl] eqn:CP; try destruct b; cbn in DIR; rewrite ?andb_false_r in DIR; try discriminate.
          - apply andb_true_iff in DIR as [_ EQ]. apply Uint63.eqb_correct in EQ. subst dest.
            apply (DirectEdge c0.(ci) target true). rewrite <-POL0. reflexivity.
          - apply IgnoreEdge. rewrite <-POL0. reflexivity. }
        assert (NLAST : c1.(cl) = false).
        { change ((metadata c1).(cl)=false). rewrite META. exact (fallthrough_not_last c0 FT). }
        pose proof (not_last_has_next a d D n c1 NTH NLAST) as NEXT.
        assert (POS : i'+nlen c = bi'+lensC[:S n] cnks).
        { unfold i'. rewrite !nlen_flat, <-!firstn_map.
          erewrite nsum_take_Sn' by (rewrite !ith_map, NTH2; reflexivity). lia. }
        assert (ENDREL : irel (i'+nlen c) = toN c0.(ci)+1).
        { rewrite POS, (following_irel n c3 NTH2 NEXT).
          rewrite R3,R2,R1. reflexivity. }
        assert (FPE : PermittedEdge (toN c0.(ci)) (toN c0.(ci)+1)).
        { unfold isfallthrough in FT. destruct c0.(cp) as [b|b dest| |lbl] eqn:CP;
            try destruct b; cbn in FT; try discriminate.
          - eqapply (FallthroughEdge c0.(ci) (eq_sym POL0)); lia.
          - eqapply (FallthroughEdge2 c0.(ci) dest (eq_sym POL0)); lia.
          - apply IgnoreEdge. rewrite <-POL0. reflexivity. }
        assert (FALL_EDGE : PermittedEdge' i' (i'+nlen c)).
        { apply TranslatedEdge. rewrite irel_i, ENDREL. exact FPE. }
        assert (FALL_END : forall s, store_invs s ->
          K_ni (Addr ((i'+nlen c)*4)) s).
        { intros s VS. apply KHere; [|exact VS]. right. unfold is_chunk_start_addr.
          rewrite POS, startschunk_at; [exact I|rewrite (num_cnks d cnks RW); exact NEXT]. }
        pose proof (relocation_endpoint target) as (TB & RT & POINT).
        assert (RESOLVE : (resolve d (Raddr target)>>2)%uint63 = d.(Rewrite.rel) target).
        { unfold resolve. nify. rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. lia. }
        assert (TARGET_EDGE : PermittedEdge' i' (toN (d.(Rewrite.rel) target))).
        { destruct RT as [ABORT|RT].
          - rewrite ABORT. apply AbortEdge.
          - apply TranslatedEdge. rewrite irel_i, RT. exact PE. }
        assert (TARGET_END : forall s, store_invs s ->
          K_ni (Addr (toN (d.(Rewrite.rel) target)*4)) s).
        { intros s VS. apply KHere; [|exact VS].
          destruct POINT as [POINT|POINT]; [left|right]; rewrite POINT; exact I. }
        assert (IPB : i' < 2^61).
        { pose proof (chunk_point_bound n).
          pose proof (ai_bound a d D). exact (N.le_lt_trans _ _ _ H H0). }
        assert (CD1 : exists k, c1.(cd) = [Ib k (Decode.Bcond imm cond) (Raddr target)]).
        { rewrite R1. cbn. unfold rw_inst. rewrite CT. fold target. rewrite DIR.
          destruct sz.(cd) as [|x xs]; [exists Sz2|exists (instsz x)]; reflexivity. }
        destruct CD1 as [k CD1].
        assert (REL : d.(Rewrite.rel) c1.(ci) = ofN i') by exact (rel_start n c1 NTH).
        assert (CODE : c = l3l (isel d (ofN i') (Ib k (Decode.Bcond imm cond) (Raddr target)))).
        { rewrite R3,R2. cbn. rewrite CD1,REL. unfold instmapi. rewrite mapi_cons.
          cbn -[isel]. rewrite app_nil_r. reflexivity. }
        assert (NL : isel d (ofN i') (Ib k (Decode.Bcond imm cond) (Raddr target)) <> Lst0).
        { pose proof no_lst0 as NL.
          rewrite R2 in NL. cbn in NL. rewrite CD1,REL in NL.
          unfold instmapi in NL. rewrite mapi_cons in NL. cbn -[isel] in NL.
          exact (Forall_inv NL). }
        intros s VS. destruct k.
        + cbn [isel] in CODE,NL. rewrite RESOLVE in CODE,NL.
          unfold Asm.Bcond in CODE,NL.
          destruct (Asm.bounded (d.(Rewrite.rel) target - ofN i') 19)%uint63 as [m|] eqn:IMM;
            cbn in CODE,NL; [|contradiction].
          assert (LEN : nlen c = 1) by (rewrite CODE; reflexivity).
          rewrite LEN in FALL_END, FALL_EDGE.
          eapply KStep with (j:=0%nat) (q:=arm_decode (toN (Asm.Encode.Bcond m (cond land 15))));
            [exact VS|rewrite CODE; reflexivity|].
          intros ctx s1 x XS MI. rewrite N.add_0_r in XS.
          apply (ExecBcond' IMM) in XS as [ST EXIT].
          2: { change ((cond land ones 4 <? 1<<4)%uint63 = true). apply landones. lia. }
          destruct EXIT as [EXIT|EXIT].
          * rewrite plusminus62 in EXIT by lia. subst x. cbn [exitof N.of_nat]. split.
            -- cbn [PermittedStep]. exists i', (toN (d.(Rewrite.rel) target)). repeat split; try lia. exact TARGET_EDGE.
            -- apply TARGET_END. split; [exact MI|exact I].
          * subst x. cbn [exitof N.of_nat]. split.
            -- cbn [PermittedStep]. exists i', (i'+1). repeat split; try lia. exact FALL_EDGE.
            -- apply FALL_END. split; [exact MI|exact I].
        + cbn [isel] in CODE,NL. rewrite RESOLVE in CODE,NL.
          assert (INV : Asm.Bcond (ofN i') (ofN i'+2) (cond lxor 1 land 15) =
            Some (Asm.Encode.Bcond 2 (cond lxor 1 land 15))).
          { unfold Asm.Bcond. replace ((ofN i'+2)-ofN i')%uint63 with 2%uint63 by lia. reflexivity. }
          rewrite INV in CODE,NL.
          unfold Asm.B in CODE,NL.
          destruct (Asm.bounded (d.(Rewrite.rel) target - (ofN i'+1)) 26)%uint63 as [m|] eqn:IMM;
            cbn in CODE,NL; [|contradiction].
          assert (LEN : nlen c = 2) by (rewrite CODE; reflexivity).
          rewrite LEN in FALL_END, FALL_EDGE.
          assert (IREL1 : irel (i'+1) = toN c0.(ci)).
          { apply (irel_in 1%nat).
            rewrite nlen_length in LEN. lia. }
          eapply KStep with (j:=0%nat) (q:=arm_decode (toN (Asm.Encode.Bcond 2 (cond lxor 1 land 15))));
            [exact VS|rewrite CODE; reflexivity|].
          intros ctx s1 x XS MI. rewrite N.add_0_r in XS.
          apply (ExecBcond' (m:=2%uint63) eq_refl) in XS as [ST EXIT].
          2: { change (((cond lxor 1) land ones 4 <? 1<<4)%uint63 = true). apply landones. lia. }
          replace (ofZ 62 (Z.of_N i' + Sint63.to_Z 2)) with (i'+2) in EXIT by (unfold ofZ; lia).
          destruct EXIT as [EXIT|EXIT].
          * subst x. cbn [exitof N.of_nat]. split.
            -- cbn [PermittedStep]. exists i', (i'+2). repeat split; try lia. exact FALL_EDGE.
            -- apply FALL_END. split; [exact MI|exact I].
          * subst x. cbn [exitof N.of_nat]. split.
            -- cbn [PermittedStep]. exists i', (i'+1). repeat split; try lia.
               apply IntraChunkEdge. rewrite irel_i, IREL1. reflexivity.
            -- eapply KStep with (j:=1%nat) (q:=arm_decode (toN (Asm.Encode.B m)));
                 [split; [exact MI|exact I]|rewrite CODE; reflexivity|].
               intros ctx2 s2 x2 XS2 MI2.
               replace (ofN i'+1)%uint63 with (ofN (i'+1)) in IMM by lia.
               apply (ExecB IMM) in XS2 as [ST2 EXIT2].
               rewrite plusminus62 in EXIT2 by lia. subst x2. cbn [exitof N.of_nat]. split.
               ++ cbn [PermittedStep]. exists (i'+1), (toN (d.(Rewrite.rel) target)). repeat split; try lia.
                  eapply PEirel; [|exact TARGET_EDGE]. rewrite irel_i, IREL1. reflexivity.
               ++ apply TARGET_END. split; [exact MI2|exact I].
        + cbn [isel] in NL. contradiction.
      - apply chunk_abort.
        rewrite R1. cbn. unfold rw_inst. rewrite CT. fold target. rewrite DIR.
        destruct sz.(cd) as [|x xs]; [exists Sz1|exists (instsz x)]; reflexivity.
    Qed.

    Lemma chunk_CBZ : forall sf op imm rt,
      c0.(ct) = Decode.CBZ sf op imm rt ->
      forall s, store_invs s -> K_nib false (Addr ((i'+0)*4)) s.
    Proof.
      intros sf op imm rt CT.
      set (target := (c0.(ci)+sext imm 19)%uint63).
      destruct (isdirect c0 false target) eqn:DIR.
      - assert (FT : isfallthrough c0 = true) by exact (isdirect_false_fallthrough c0 target DIR).
        assert (META : metadata c1 = c0).
        { rewrite R1. unfold change_szs, metadata, setd. destruct c0 as [cn ci ct cp cl []]. reflexivity. }
        pose proof (source_nth a d D n c1 NTH) as (_&_&POL&_&_).
        assert (POL0 : c0.(cp) = d.(arg).(Rewrite.pol) c0.(ci)).
        { rewrite <-META. cbn. rewrite (arg_same a d D). exact POL. }
        assert (PE : PermittedEdge (toN c0.(ci)) (toN target)).
        { unfold isdirect in DIR.
          destruct c0.(cp) as [b|b dest| |lbl] eqn:CP; try destruct b; cbn in DIR; rewrite ?andb_false_r in DIR; try discriminate.
          - apply andb_true_iff in DIR as [_ EQ]. apply Uint63.eqb_correct in EQ. subst dest.
            apply (DirectEdge c0.(ci) target true). rewrite <-POL0. reflexivity.
          - apply IgnoreEdge. rewrite <-POL0. reflexivity. }
        assert (NLAST : c1.(cl) = false).
        { change ((metadata c1).(cl)=false). rewrite META. exact (fallthrough_not_last c0 FT). }
        pose proof (not_last_has_next a d D n c1 NTH NLAST) as NEXT.
        assert (POS : i'+nlen c = bi'+lensC[:S n] cnks).
        { unfold i'. rewrite !nlen_flat, <-!firstn_map.
          erewrite nsum_take_Sn' by (rewrite !ith_map, NTH2; reflexivity). lia. }
        assert (ENDREL : irel (i'+nlen c) = toN c0.(ci)+1).
        { rewrite POS, (following_irel n c3 NTH2 NEXT).
          rewrite R3,R2,R1. reflexivity. }
        assert (FPE : PermittedEdge (toN c0.(ci)) (toN c0.(ci)+1)).
        { unfold isfallthrough in FT. destruct c0.(cp) as [b|b dest| |lbl] eqn:CP;
            try destruct b; cbn in FT; try discriminate.
          - eqapply (FallthroughEdge c0.(ci) (eq_sym POL0)); lia.
          - eqapply (FallthroughEdge2 c0.(ci) dest (eq_sym POL0)); lia.
          - apply IgnoreEdge. rewrite <-POL0. reflexivity. }
        assert (FALL_EDGE : PermittedEdge' i' (i'+nlen c)).
        { apply TranslatedEdge. rewrite irel_i, ENDREL. exact FPE. }
        assert (FALL_END : forall s, store_invs s ->
          K_ni (Addr ((i'+nlen c)*4)) s).
        { intros s VS. apply KHere; [|exact VS]. right. unfold is_chunk_start_addr.
          rewrite POS, startschunk_at; [exact I|rewrite (num_cnks d cnks RW); exact NEXT]. }
        pose proof (relocation_endpoint target) as (TB & RT & POINT).
        assert (RESOLVE : (resolve d (Raddr target)>>2)%uint63 = d.(Rewrite.rel) target).
        { unfold resolve. nify. rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. lia. }
        assert (TARGET_EDGE : PermittedEdge' i' (toN (d.(Rewrite.rel) target))).
        { destruct RT as [ABORT|RT].
          - rewrite ABORT. apply AbortEdge.
          - apply TranslatedEdge. rewrite irel_i, RT. exact PE. }
        assert (TARGET_END : forall s, store_invs s ->
          K_ni (Addr (toN (d.(Rewrite.rel) target)*4)) s).
        { intros s VS. apply KHere; [|exact VS].
          destruct POINT as [POINT|POINT]; [left|right]; rewrite POINT; exact I. }
        assert (IPB : i' < 2^61).
        { pose proof (chunk_point_bound n).
          pose proof (ai_bound a d D). exact (N.le_lt_trans _ _ _ H H0). }
        assert (CD1 : exists k, c1.(cd) = [Ib k (Decode.CBZ sf op imm rt) (Raddr target)]).
        { rewrite R1. cbn. unfold rw_inst. rewrite CT. fold target. rewrite DIR.
          destruct sz.(cd) as [|x xs]; [exists Sz2|exists (instsz x)]; reflexivity. }
        destruct CD1 as [k CD1].
        assert (REL : d.(Rewrite.rel) c1.(ci) = ofN i') by exact (rel_start n c1 NTH).
        assert (CODE : c = l3l (isel d (ofN i') (Ib k (Decode.CBZ sf op imm rt) (Raddr target)))).
        { rewrite R3,R2. cbn. rewrite CD1,REL. unfold instmapi. rewrite mapi_cons.
          cbn -[isel]. rewrite app_nil_r. reflexivity. }
        assert (NL : isel d (ofN i') (Ib k (Decode.CBZ sf op imm rt) (Raddr target)) <> Lst0).
        { pose proof no_lst0 as NL.
          rewrite R2 in NL. cbn in NL. rewrite CD1,REL in NL.
          unfold instmapi in NL. rewrite mapi_cons in NL. cbn -[isel] in NL.
          exact (Forall_inv NL). }
        intros s VS. destruct k.
        + cbn [isel] in CODE,NL. rewrite RESOLVE in CODE,NL.
          unfold Asm.CBZ in CODE,NL.
          destruct (Asm.bounded (d.(Rewrite.rel) target - ofN i') 19)%uint63 as [m|] eqn:IMM;
            cbn in CODE,NL; [|contradiction].
          assert (LEN : nlen c = 1) by (rewrite CODE; reflexivity).
          rewrite LEN in FALL_END, FALL_EDGE.
          eapply KStep with (j:=0%nat) (q:=arm_decode (toN (Asm.Encode.CBZ (sf land 1) (op land 1) m (rt land 31))));
            [exact VS|rewrite CODE; reflexivity|].
          intros ctx s1 x XS MI. rewrite N.add_0_r in XS.
          apply (ExecCBZ' IMM) in XS as [ST EXIT].
          all: try (cones; apply landones; lia).
          destruct EXIT as [EXIT|EXIT].
          * rewrite plusminus62 in EXIT by lia. subst x. cbn [exitof N.of_nat]. split.
            -- cbn [PermittedStep]. exists i', (toN (d.(Rewrite.rel) target)). repeat split; try lia. exact TARGET_EDGE.
            -- apply TARGET_END. split; [exact MI|exact I].
          * subst x. cbn [exitof N.of_nat]. split.
            -- cbn [PermittedStep]. exists i', (i'+1). repeat split; try lia. exact FALL_EDGE.
            -- apply FALL_END. split; [exact MI|exact I].
        + cbn [isel] in CODE,NL. rewrite RESOLVE in CODE,NL.
          assert (INV : Asm.CBZ (sf land 1) (b2i (is_zero op)) (ofN i') (ofN i'+2) (rt land 31) =
            Some (Asm.Encode.CBZ (sf land 1) (b2i (is_zero op)) 2 (rt land 31))).
          { unfold Asm.CBZ. replace ((ofN i'+2)-ofN i')%uint63 with 2%uint63 by lia. reflexivity. }
          rewrite INV in CODE,NL.
          unfold Asm.B in CODE,NL.
          destruct (Asm.bounded (d.(Rewrite.rel) target - (ofN i'+1)) 26)%uint63 as [m|] eqn:IMM;
            cbn in CODE,NL; [|contradiction].
          assert (LEN : nlen c = 2) by (rewrite CODE; reflexivity).
          rewrite LEN in FALL_END, FALL_EDGE.
          assert (IREL1 : irel (i'+1) = toN c0.(ci)).
          { apply (irel_in 1%nat).
            rewrite nlen_length in LEN. lia. }
          eapply KStep with (j:=0%nat) (q:=arm_decode (toN (Asm.Encode.CBZ (sf land 1) (b2i (is_zero op)) 2 (rt land 31))));
            [exact VS|rewrite CODE; reflexivity|].
          intros ctx s1 x XS MI. rewrite N.add_0_r in XS.
          apply (ExecCBZ' (m:=2%uint63) eq_refl) in XS as [ST EXIT].
          all: try (cones; apply landones; lia).
          all: try (unfold b2i; destruct (is_zero op); reflexivity).
          replace (ofZ 62 (Z.of_N i' + Sint63.to_Z 2)) with (i'+2) in EXIT by (unfold ofZ; lia).
          destruct EXIT as [EXIT|EXIT].
          * subst x. cbn [exitof N.of_nat]. split.
            -- cbn [PermittedStep]. exists i', (i'+2). repeat split; try lia. exact FALL_EDGE.
            -- apply FALL_END. split; [exact MI|exact I].
          * subst x. cbn [exitof N.of_nat]. split.
            -- cbn [PermittedStep]. exists i', (i'+1). repeat split; try lia.
               apply IntraChunkEdge. rewrite irel_i, IREL1. reflexivity.
            -- eapply KStep with (j:=1%nat) (q:=arm_decode (toN (Asm.Encode.B m)));
                 [split; [exact MI|exact I]|rewrite CODE; reflexivity|].
               intros ctx2 s2 x2 XS2 MI2.
               replace (ofN i'+1)%uint63 with (ofN (i'+1)) in IMM by lia.
               apply (ExecB IMM) in XS2 as [ST2 EXIT2].
               rewrite plusminus62 in EXIT2 by lia. subst x2. cbn [exitof N.of_nat]. split.
               ++ cbn [PermittedStep]. exists (i'+1), (toN (d.(Rewrite.rel) target)). repeat split; try lia.
                  eapply PEirel; [|exact TARGET_EDGE]. rewrite irel_i, IREL1. reflexivity.
               ++ apply TARGET_END. split; [exact MI2|exact I].
        + cbn [isel] in NL. contradiction.
      - apply chunk_abort.
        rewrite R1. cbn. unfold rw_inst. rewrite CT. fold target. rewrite DIR.
        destruct sz.(cd) as [|x xs]; [exists Sz1|exists (instsz x)]; reflexivity.
    Qed.

    Lemma chunk_TBZ : forall b5 op b40 imm rt,
      c0.(ct) = Decode.TBZ b5 op b40 imm rt ->
      forall s, store_invs s -> K_nib false (Addr ((i'+0)*4)) s.
    Proof.
      intros b5 op b40 imm rt CT.
      set (target := (c0.(ci)+sext imm 14)%uint63).
      destruct (isdirect c0 false target) eqn:DIR.
      - assert (FT : isfallthrough c0 = true) by exact (isdirect_false_fallthrough c0 target DIR).
        assert (META : metadata c1 = c0).
        { rewrite R1. unfold change_szs, metadata, setd. destruct c0 as [cn ci ct cp cl []]. reflexivity. }
        pose proof (source_nth a d D n c1 NTH) as (_&_&POL&_&_).
        assert (POL0 : c0.(cp) = d.(arg).(Rewrite.pol) c0.(ci)).
        { rewrite <-META. cbn. rewrite (arg_same a d D). exact POL. }
        assert (PE : PermittedEdge (toN c0.(ci)) (toN target)).
        { unfold isdirect in DIR.
          destruct c0.(cp) as [b|b dest| |lbl] eqn:CP; try destruct b; cbn in DIR; rewrite ?andb_false_r in DIR; try discriminate.
          - apply andb_true_iff in DIR as [_ EQ]. apply Uint63.eqb_correct in EQ. subst dest.
            apply (DirectEdge c0.(ci) target true). rewrite <-POL0. reflexivity.
          - apply IgnoreEdge. rewrite <-POL0. reflexivity. }
        assert (NLAST : c1.(cl) = false).
        { change ((metadata c1).(cl)=false). rewrite META. exact (fallthrough_not_last c0 FT). }
        pose proof (not_last_has_next a d D n c1 NTH NLAST) as NEXT.
        assert (POS : i'+nlen c = bi'+lensC[:S n] cnks).
        { unfold i'. rewrite !nlen_flat, <-!firstn_map.
          erewrite nsum_take_Sn' by (rewrite !ith_map, NTH2; reflexivity). lia. }
        assert (ENDREL : irel (i'+nlen c) = toN c0.(ci)+1).
        { rewrite POS, (following_irel n c3 NTH2 NEXT).
          rewrite R3,R2,R1. reflexivity. }
        assert (FPE : PermittedEdge (toN c0.(ci)) (toN c0.(ci)+1)).
        { unfold isfallthrough in FT. destruct c0.(cp) as [b|b dest| |lbl] eqn:CP;
            try destruct b; cbn in FT; try discriminate.
          - eqapply (FallthroughEdge c0.(ci) (eq_sym POL0)); lia.
          - eqapply (FallthroughEdge2 c0.(ci) dest (eq_sym POL0)); lia.
          - apply IgnoreEdge. rewrite <-POL0. reflexivity. }
        assert (FALL_EDGE : PermittedEdge' i' (i'+nlen c)).
        { apply TranslatedEdge. rewrite irel_i, ENDREL. exact FPE. }
        assert (FALL_END : forall s, store_invs s ->
          K_ni (Addr ((i'+nlen c)*4)) s).
        { intros s VS. apply KHere; [|exact VS]. right. unfold is_chunk_start_addr.
          rewrite POS, startschunk_at; [exact I|rewrite (num_cnks d cnks RW); exact NEXT]. }
        pose proof (relocation_endpoint target) as (TB & RT & POINT).
        assert (RESOLVE : (resolve d (Raddr target)>>2)%uint63 = d.(Rewrite.rel) target).
        { unfold resolve. nify. rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. lia. }
        assert (TARGET_EDGE : PermittedEdge' i' (toN (d.(Rewrite.rel) target))).
        { destruct RT as [ABORT|RT].
          - rewrite ABORT. apply AbortEdge.
          - apply TranslatedEdge. rewrite irel_i, RT. exact PE. }
        assert (TARGET_END : forall s, store_invs s ->
          K_ni (Addr (toN (d.(Rewrite.rel) target)*4)) s).
        { intros s VS. apply KHere; [|exact VS].
          destruct POINT as [POINT|POINT]; [left|right]; rewrite POINT; exact I. }
        assert (IPB : i' < 2^61).
        { pose proof (chunk_point_bound n).
          pose proof (ai_bound a d D). exact (N.le_lt_trans _ _ _ H H0). }
        assert (CD1 : exists k, c1.(cd) = [Ib k (Decode.TBZ b5 op b40 imm rt) (Raddr target)]).
        { rewrite R1. cbn. unfold rw_inst. rewrite CT. fold target. rewrite DIR.
          destruct sz.(cd) as [|x xs]; [exists Sz2|exists (instsz x)]; reflexivity. }
        destruct CD1 as [k CD1].
        assert (REL : d.(Rewrite.rel) c1.(ci) = ofN i') by exact (rel_start n c1 NTH).
        assert (CODE : c = l3l (isel d (ofN i') (Ib k (Decode.TBZ b5 op b40 imm rt) (Raddr target)))).
        { rewrite R3,R2. cbn. rewrite CD1,REL. unfold instmapi. rewrite mapi_cons.
          cbn -[isel]. rewrite app_nil_r. reflexivity. }
        assert (NL : isel d (ofN i') (Ib k (Decode.TBZ b5 op b40 imm rt) (Raddr target)) <> Lst0).
        { pose proof no_lst0 as NL.
          rewrite R2 in NL. cbn in NL. rewrite CD1,REL in NL.
          unfold instmapi in NL. rewrite mapi_cons in NL. cbn -[isel] in NL.
          exact (Forall_inv NL). }
        intros s VS. destruct k.
        + cbn [isel] in CODE,NL. rewrite RESOLVE in CODE,NL.
          unfold Asm.TBZ in CODE,NL.
          destruct (Asm.bounded (d.(Rewrite.rel) target - ofN i') 14)%uint63 as [m|] eqn:IMM;
            cbn in CODE,NL; [|contradiction].
          assert (LEN : nlen c = 1) by (rewrite CODE; reflexivity).
          rewrite LEN in FALL_END, FALL_EDGE.
          eapply KStep with (j:=0%nat) (q:=arm_decode (toN (Asm.Encode.TBZ (b5 land 1) (op land 1) (b40 land 15) m (rt land 31))));
            [exact VS|rewrite CODE; reflexivity|].
          intros ctx s1 x XS MI. rewrite N.add_0_r in XS.
          apply (ExecTBZ' IMM) in XS as [ST EXIT].
          all: try (cones; apply landones; lia).
          destruct EXIT as [EXIT|EXIT].
          * rewrite plusminus62 in EXIT by lia. subst x. cbn [exitof N.of_nat]. split.
            -- cbn [PermittedStep]. exists i', (toN (d.(Rewrite.rel) target)). repeat split; try lia. exact TARGET_EDGE.
            -- apply TARGET_END. split; [exact MI|exact I].
          * subst x. cbn [exitof N.of_nat]. split.
            -- cbn [PermittedStep]. exists i', (i'+1). repeat split; try lia. exact FALL_EDGE.
            -- apply FALL_END. split; [exact MI|exact I].
        + cbn [isel] in CODE,NL. rewrite RESOLVE in CODE,NL.
          assert (INV : Asm.TBZ (b5 land 1) (b2i (is_zero op)) (b40 land 15) (ofN i') (ofN i'+2) (rt land 31) =
            Some (Asm.Encode.TBZ (b5 land 1) (b2i (is_zero op)) (b40 land 15) 2 (rt land 31))).
          { unfold Asm.TBZ. replace ((ofN i'+2)-ofN i')%uint63 with 2%uint63 by lia. reflexivity. }
          rewrite INV in CODE,NL.
          unfold Asm.B in CODE,NL.
          destruct (Asm.bounded (d.(Rewrite.rel) target - (ofN i'+1)) 26)%uint63 as [m|] eqn:IMM;
            cbn in CODE,NL; [|contradiction].
          assert (LEN : nlen c = 2) by (rewrite CODE; reflexivity).
          rewrite LEN in FALL_END, FALL_EDGE.
          assert (IREL1 : irel (i'+1) = toN c0.(ci)).
          { apply (irel_in 1%nat).
            rewrite nlen_length in LEN. lia. }
          eapply KStep with (j:=0%nat) (q:=arm_decode (toN (Asm.Encode.TBZ (b5 land 1) (b2i (is_zero op)) (b40 land 15) 2 (rt land 31))));
            [exact VS|rewrite CODE; reflexivity|].
          intros ctx s1 x XS MI. rewrite N.add_0_r in XS.
          apply (ExecTBZ' (m:=2%uint63) eq_refl) in XS as [ST EXIT].
          all: try (cones; apply landones; lia).
          all: try (unfold b2i; destruct (is_zero op); reflexivity).
          replace (ofZ 62 (Z.of_N i' + Sint63.to_Z 2)) with (i'+2) in EXIT by (unfold ofZ; lia).
          destruct EXIT as [EXIT|EXIT].
          * subst x. cbn [exitof N.of_nat]. split.
            -- cbn [PermittedStep]. exists i', (i'+2). repeat split; try lia. exact FALL_EDGE.
            -- apply FALL_END. split; [exact MI|exact I].
          * subst x. cbn [exitof N.of_nat]. split.
            -- cbn [PermittedStep]. exists i', (i'+1). repeat split; try lia.
               apply IntraChunkEdge. rewrite irel_i, IREL1. reflexivity.
            -- eapply KStep with (j:=1%nat) (q:=arm_decode (toN (Asm.Encode.B m)));
                 [split; [exact MI|exact I]|rewrite CODE; reflexivity|].
               intros ctx2 s2 x2 XS2 MI2.
               replace (ofN i'+1)%uint63 with (ofN (i'+1)) in IMM by lia.
               apply (ExecB IMM) in XS2 as [ST2 EXIT2].
               rewrite plusminus62 in EXIT2 by lia. subst x2. cbn [exitof N.of_nat]. split.
               ++ cbn [PermittedStep]. exists (i'+1), (toN (d.(Rewrite.rel) target)). repeat split; try lia.
                  eapply PEirel; [|exact TARGET_EDGE]. rewrite irel_i, IREL1. reflexivity.
               ++ apply TARGET_END. split; [exact MI2|exact I].
        + cbn [isel] in NL. contradiction.
      - apply chunk_abort.
        rewrite R1. cbn. unfold rw_inst. rewrite CT. fold target. rewrite DIR.
        destruct sz.(cd) as [|x xs]; [exists Sz1|exists (instsz x)]; reflexivity.
    Qed.

    Lemma chunk_unrelaxed :
      (forall rel ip inst, In inst (rw_inst a c0) -> relaxi rel ip inst = inst) ->
      c1.(cd) = rw_inst a c0.
    Proof.
      intro STABLE.
      assert (META : metadata c1 = c0).
      { rewrite R1. unfold change_szs, metadata, setd. destruct c0 as [cn ci ct cp cl []]. reflexivity. }
      assert (SOURCE : ith (stage2 a (stage1 a)) n = Some (setd c0 (rw_inst a c0))).
      { unfold stage2. rewrite ith_map, <-(chunks_metadata a d D), ith_map, NTH.
        cbn [option_map]. rewrite META. reflexivity. }
      pose proof (stage3_stable_chunk a _ _ _ SOURCE STABLE) as OUT.
      assert (CHUNKS : d.(chunks) = stage3 a (stage2 a (stage1 a))).
      { repeat so D. rewrite <-D. reflexivity. }
      rewrite <-CHUNKS, NTH in OUT. inversion OUT. reflexivity.
    Qed.

    Lemma chunk_direct_target : forall target,
      isdirect c0 true target = true ->
      PermittedEdge' i' (toN (resolve d (Raddr target)>>2)) /\
      (forall s, store_invs s -> K_ni (Addr (toN (resolve d (Raddr target)>>2)*4)) s).
    Proof.
      intros target DIR.
      assert (META : metadata c1 = c0).
      { rewrite R1. unfold change_szs, metadata, setd. destruct c0 as [cn ci ct cp cl []]. reflexivity. }
      pose proof (source_nth a d D n c1 NTH) as (_&_&POL&_&_).
      assert (POL0 : c0.(cp) = d.(arg).(Rewrite.pol) c0.(ci)).
      { rewrite <-META. cbn. rewrite (arg_same a d D). exact POL. }
      assert (PE : PermittedEdge (toN c0.(ci)) (toN target)).
      { unfold isdirect in DIR. cbn in DIR.
        destruct c0.(cp) as [b|b dest| |lbl] eqn:CP; cbn in DIR; try discriminate.
        - apply Uint63.eqb_correct in DIR. subst dest.
          apply (DirectEdge c0.(ci) target b). rewrite <-POL0. reflexivity.
        - apply IgnoreEdge. rewrite <-POL0. reflexivity. }
      pose proof (relocation_endpoint target) as (TB & RT & POINT).
      assert (RESOLVE : (resolve d (Raddr target)>>2)%uint63 = d.(Rewrite.rel) target).
      { unfold resolve. nify. rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. lia. }
      rewrite RESOLVE. split.
      - destruct RT as [ABORT|RT].
        + rewrite ABORT. apply AbortEdge.
        + apply TranslatedEdge. rewrite irel_i, RT. exact PE.
      - intros s VS. apply KHere; [|exact VS].
        destruct POINT as [POINT|POINT]; [left|right]; rewrite POINT; exact I.
    Qed.

    Lemma chunk_B : forall imm, c0.(ct) = Decode.B imm -> Goal.
    Proof.
      intros imm CT. set (target := (c0.(ci)+sext imm 26)%uint63).
      destruct (isdirect c0 true target) eqn:DIR.
      - destruct (chunk_direct_target target DIR) as [EDGE ENDPOINT].
        assert (CD1 : exists k, c1.(cd) = [Ib k (Decode.B imm) (Raddr target)]).
        { rewrite R1. cbn. unfold rw_inst. rewrite CT. fold target. rewrite DIR.
          destruct sz.(cd) as [|x xs]; [exists Sz1|exists (instsz x)]; reflexivity. }
        destruct CD1 as [k CD1]. intros s VS.
        eapply (ExecIb false 0 s k (Raddr target) (Decode.B imm));
          [exact VS|rewrite CD1;reflexivity|rewrite N.add_0_r;exact EDGE|exact ENDPOINT|exact I|exact I].
      - apply chunk_abort. rewrite R1. cbn. unfold rw_inst. rewrite CT. fold target. rewrite DIR.
        destruct sz.(cd) as [|x xs]; [exists Sz1|exists (instsz x)]; reflexivity.
    Qed.

    Lemma store_invs_x30 : forall s v,
      store_invs s -> v < 2^64 -> store_invs (s.[R_X30 := v]).
    Proof.
      intros s v [(MDL&CODE&DATA&NWC&NWD&EXC) FLAGS] V.
      split; [|exact I]. split.
      - apply models_update; [exact V|exact MDL].
      - cbn [update]. repeat split; assumption.
    Qed.

    Lemma chunk_BL : forall imm, c0.(ct) = Decode.BL imm -> Goal.
    Proof.
      intros imm CT. set (target := (c0.(ci)+sext imm 26)%uint63).
      destruct (isdirect c0 true target) eqn:DIR.
      - destruct (chunk_direct_target target DIR) as [EDGE ENDPOINT].
        destruct a.(orig_lr) eqn:ORIG.
        + assert (CD1 : c1.(cd) = setlr ((c0.(ci)+1)<<2)
            (Ib Sz1 (Decode.B imm) (Raddr target))).
          { rewrite chunk_unrelaxed.
            - unfold rw_inst. rewrite CT. fold target. rewrite DIR, ORIG. reflexivity.
            - unfold rw_inst. rewrite CT. fold target. rewrite DIR, ORIG.
              unfold setlr. destruct (_ <? _)%uint63; intros rel ip inst INST;
                cbn in INST; repeat destruct INST as [<-|INST]; try contradiction; reflexivity. }
          unfold setlr in CD1.
          destruct (((c0.(ci)+1)<<2) <? 1<<32)%uint63 eqn:FIT.
          all: intros s VS.
          all: assert (BOUNDS : forall j, (j < 4)%nat -> i'+cidx j < i'+nlen c) by
            (intros j J; pose proof (cidx_bound' j) as B;
            rewrite CD1 in B |- *; destruct j as [|[|[|[|j]]]]; cbn in B |- *; lia).
          all: assert (INTRA : forall j k, (j<4)%nat -> (k<4)%nat ->
            PermittedEdge' (i'+cidx j) (i'+cidx k)) by
            (intros j k J K; apply IntraChunkEdge;
            rewrite !irel_in; try reflexivity; pose proof (BOUNDS _ J); pose proof (BOUNDS _ K); rewrite nlen_length in *; lia).
          all: assert (BRANCH : forall s, store_invs s ->
            K_ni (Addr ((i'+cidx 2)*4)) s) by
            (intros s0 VS0; eapply (ExecIb true 2 s0 Sz1 (Raddr target) (Decode.B imm));
            [exact VS0|rewrite CD1;reflexivity| |exact ENDPOINT|exact I|exact I];
            eapply PEirel; [|exact EDGE]; rewrite irel_i, irel_in; [reflexivity|];
            pose proof (BOUNDS 2%nat ltac:(lia)); rewrite nlen_length in *; lia).
          all: assert (MATERIALIZE : forall s, store_invs s ->
            K_ni (Addr ((i'+cidx 1)*4)) s) by
            (intros s0 VS0; eapply ExecIimm with (j:=1%nat) (r:=30%uint63);
            [exact VS0|reflexivity|rewrite CD1;reflexivity|rewrite <-(N.add_0_r i') at 1;apply (INTRA 0%nat 2%nat);lia|];
            apply BRANCH; apply store_invs_x30; [exact VS0|]; unfold resolve; lia).
          all: eapply ExecInum with (j:=0%nat);
            [exact VS|rewrite CD1;reflexivity|].
          all: intros ctx s1 x XS MI; rewrite N.add_0_r in XS.
          all: apply (ExecB (m:=4%uint63) eq_refl) in XS as [ST EXIT]
            || apply (ExecB (m:=5%uint63) eq_refl) in XS as [ST EXIT].
          all: pose proof (i'cidx_bound 3%nat) as IPB; rewrite CD1 in IPB; cbn in IPB.
          all: match type of EXIT with
          | _ = Some (Addr (?dst * 4)) =>
              replace dst with (i'+cidx 3) in EXIT by
                (rewrite CD1; unfold cidx'; cbn; unfold ofZ; lia)
          end.
          all: subst x; cbn [exitof]; split.
          all: try (cbn [PermittedStep]; repeat eexists; apply (INTRA 0%nat 3%nat); lia).
          all: eapply ExecInum with (j:=3%nat);
            [split;[exact MI|exact I]|rewrite CD1;reflexivity|].
          all: intros ctx2 s2 x2 XS2 MI2; rewrite CD1 in XS2; cbn in XS2.
          all: apply (ExecBL (m:=(0-3)%uint63) eq_refl) in XS2 as [ST2 EXIT2]
            || apply (ExecBL (m:=(0-4)%uint63) eq_refl) in XS2 as [ST2 EXIT2].
          all: match type of EXIT2 with
          | _ = Some (Addr (?dst * 4)) =>
              replace dst with (i'+cidx 1) in EXIT2 by
                (rewrite CD1; unfold cidx'; cbn; unfold ofZ; lia)
          end.
          all: subst x2; cbn [exitof]; split.
          all: try (cbn [PermittedStep]; repeat eexists; apply (INTRA 3%nat 1%nat); lia).
          all: apply MATERIALIZE; split; [exact MI2|exact I].
        + assert (CD1 : exists k, c1.(cd) = [Ib k (Decode.BL imm) (Raddr target)]).
          { rewrite R1. cbn. unfold rw_inst. rewrite CT. fold target. rewrite DIR, ORIG.
            destruct sz.(cd) as [|x xs]; [exists Sz1|exists (instsz x)]; reflexivity. }
          destruct CD1 as [k CD1]. intros s VS.
          eapply (ExecIb false 0 s k (Raddr target) (Decode.BL imm));
            [exact VS|rewrite CD1;reflexivity|rewrite N.add_0_r;exact EDGE|exact ENDPOINT|exact I|exact I].
      - apply chunk_abort. rewrite R1. cbn. unfold rw_inst. rewrite CT. fold target. rewrite DIR.
        destruct sz.(cd) as [|x xs]; [exists Sz1|exists (instsz x)]; reflexivity.
    Qed.

    Lemma chunk_invalid: c0.(ct) = Decode.invalid -> Goal.
    Proof.
      intro CT. apply chunk_abort.
      rewrite R1. cbn. unfold rw_inst. rewrite CT.
      destruct sz.(cd) as [|x xs]; [exists Sz1|exists (instsz x)]; reflexivity.
    Qed.

    (* A register write preserves the store invariants. *)
    Lemma store_invs_upd : forall s r v,
      store_invs s -> v < 2^64 -> store_invs (s.[arm_varid r := v]).
    Proof.
      intros s r v [(MDL&CODE&DATA&NWC&NWD&EXC) FLAGS] V.
      assert (FM: forall x, (x = V_MEM64 \/ x = A_WRITE \/ x = UXN) ->
        (s.[arm_varid r := v]) x = s x).
      { intros x X. unfold arm_varid.
        destruct X as [X|[X|X]]; subst; repeat case_match; by rewrite update_frame. }
      assert (T: arm8typctx (arm_varid r) = Some 64)
        by (unfold arm_varid; repeat case_match; reflexivity).
      split; [|exact I]. unfold mem_invs, MemHas in *.
      rewrite !(FM V_MEM64 (or_introl eq_refl)),
        !(FM A_WRITE (or_intror (or_introl eq_refl))),
        !(FM UXN (or_intror (or_intror eq_refl))).
      repeat split; try assumption.
      apply models_update; [|exact MDL]. by rewrite T.
    Qed.
    (* A raw instruction word that the chunk emits is a 4-byte memory read,
       hence below 2^32. *)
    Lemma inum_bound : forall j n0 s,
      mem_invs s -> ith c1.(cd) j = Some (Inum n0) -> ♮n0 < 2^32.
    Proof.
      intros j n0 s MI Q.
      destruct (cidxn Q) as [C NL0]. simpl in C.
      assert (IT : ith c (cidx j) = Some n0).
      { rewrite ith_skipn_hd, C. reflexivity. }
      pose proof (code s MI (cidx j) n0 IT) as CODE.
      pose proof (getmem_bound 64 LittleE 4 (s V_MEM64) (i' * 4 + (cidx j) * 4)) as B.
      rewrite CODE in B. change (2 ^ (4 * 8)) with (2 ^ 32) in B. exact B.
    Qed.
    (* Any destination of this chunk's indirect branch is a permitted,
       observable target. *)
    Lemma chunk_indirect_target : forall lbl D0 dd,
      c0.(cp) = Pindirect lbl ->
      nth_error d.(arg).(Rewrite.dsets) ♮lbl = Some D0 -> In dd D0 ->
      PermittedEdge' i' (toN (d.(Rewrite.rel) dd)) /\
      (forall s, store_invs s -> K_ni (Addr (toN (d.(Rewrite.rel) dd)*4)) s).
    Proof.
      intros lbl D0 dd CP DSN IN.
      assert (META : metadata c1 = c0).
      { rewrite R1. unfold change_szs, metadata, setd. destruct c0 as [cn ci ct cp cl []]. reflexivity. }
      pose proof (source_nth a d D n c1 NTH) as (_&_&POL&_&_).
      assert (POL0 : c0.(cp) = d.(arg).(Rewrite.pol) c0.(ci)).
      { rewrite <-META. cbn. rewrite (arg_same a d D). exact POL. }
      assert (PE : PermittedEdge (toN c0.(ci)) (toN dd)).
      { apply (IndirectEdge c0.(ci) dd D0 lbl); [|exact DSN|exact IN].
        rewrite <-POL0. exact CP. }
      pose proof (relocation_endpoint dd) as (TB & RT & POINT).
      split.
      - destruct RT as [ABORT|RT].
        + rewrite ABORT. apply AbortEdge.
        + apply TranslatedEdge. rewrite irel_i, RT. exact PE.
      - intros s VS. apply KHere; [|exact VS].
        destruct POINT as [POINT|POINT]; [left|right]; rewrite POINT; exact I.
    Qed.
    (* Single-target indirect branch: an Iimm loads the relocated target into
       the branch register, then the original branch word runs and jumps to it. *)
    Lemma ind1_case : forall Rn dd lbl,
      (exists z, c1.(cd) = [Iimm true z Rn (Raddr dd); Inum c0.(cn)]) ->
      (Rn <? 32 = true)%uint63 ->
      c0.(cp) = Pindirect lbl ->
      Util.ith d.(arg).(Rewrite.dsets) lbl = Some [dd] ->
      (♮c0.(cn) < 2^32 -> forall s s1 c x a,
         exec_stmt arm8typctx s (a64lift a (arm_decode ♮c0.(cn))) c s1 x ->
         reset_temps s s1 = s /\ x = Some (Addr (s (arm_varid ♮Rn)))) ->
      Goal.
    Proof.
      intros Rn dd lbl [z CD] R CP DS BRX s VS.
      assert (DSN : nth_error d.(arg).(Rewrite.dsets) ♮lbl = Some [dd])
        by (rewrite <-Util.ith_nth_error; exact DS).
      destruct (chunk_indirect_target lbl [dd] dd CP DSN (or_introl eq_refl)) as [TEDGE TEND].
      assert (Q0 : ith c1.(cd) O = Some (Iimm true z Rn (Raddr dd))) by (rewrite CD; reflexivity).
      assert (Q1 : ith c1.(cd) (S O) = Some (Inum c0.(cn))) by (rewrite CD; reflexivity).
      pose proof (cidx_Sn' _ _ _ Q1) as CS1.
      pose proof (cidx_bound (S (S O))) as CLL. rewrite CS1, nlen_length in CLL.
      simpl in CS1, CLL.
      assert (LT : (cidx (S O) < length c)%nat) by lia.
      assert (IC : irel (i' + cidx (S O)) = ♮i) by (apply irel_in, LT).
      change (i' + 0) with (i' + cidx O).
      eapply ExecIimm with (j := O) (sz := z) (r := Rn) (imm := Raddr dd) (relax := true).
      - exact VS.
      - exact R.
      - exact Q0.
      - apply IntraChunkEdge. by rewrite irel_i, IC.
      - assert (VS' : store_invs (s.[arm_varid ♮Rn := ♮(resolve d (Raddr dd))]))
          by (apply store_invs_upd; [exact VS | lia]).
        pose proof (inum_bound (S O) _ s (proj1 VS) Q1) as WB.
        eapply ExecInum with (j := S O) (n := c0.(cn)); [exact VS' | exact Q1 |].
        intros c' s1 x1 XS MI.
        apply (BRX WB) in XS as [S' X'].
        rewrite update_updated in X'. subst x1. cbn [exitof]. rewrite S'.
        split.
        + exists (i' + cidx (S O)), (toN (d.(Rewrite.rel) dd)), eq_refl, (resolve_raddr_val dd).
          eapply PEirel; [|exact TEDGE]. rewrite irel_i, IC. reflexivity.
        + pose proof (TEND _ VS') as KEND. rewrite <-(resolve_raddr_val dd) in KEND. exact KEND.
    Qed.

    (* Values an indirect branch register may hold when the branch runs: the
       abort address or the relocated address of a destination in the set. *)
    Definition IndTgt lbl v := exists D0,
      nth_error dsets ♮lbl = Some D0 /\
      (v = ai * 4 \/ exists dd, In dd D0 /\ v = toN (rel dd) * 4).
    Lemma cidx_lt : forall j x, ith c1.(cd) j = Some x -> cidx j <ₒ length c.
    Proof.
      intros j x Q. pose proof (cidx_Sn' _ _ _ Q) as CS.
      pose proof (cidx_bound (S j)) as CLL. rewrite CS, nlen_length in CLL.
      assert (SZ : (1 <= ♮(instsize x))%nat)
        by (destruct x as [?|? [] ? ?|? ?|[] ? ?]; vm_compute; lia).
      lia.
    Qed.
    (* A jump from inside this chunk to an IndTgt value is permitted and lands
       on an invariant point. *)
    Lemma ind_target : forall lbl v j s s1,
      c0.(cp) = Pindirect lbl -> IndTgt lbl v -> j <ₒ length c ->
      PermittedStep (Addr v, s1, (Addr 4(i'+j), s)) /\
      (store_invs s1 -> K_ni (Addr v) s1).
    Proof.
      intros lbl v j s s1 CP [D0 [DSN [->|[dd [IN ->]]]]] J.
      - split.
        + exists (i'+j), ai, eq_refl, eq_refl. apply AbortEdge.
        + intro VS. apply KHere; [|exact VS]. left. unfold is_ext_addr.
          assert (EXT : ((bi'+nlen(flat_map cd cnks))*4 <=? ai*4)%N = true)
            by (apply N.leb_le; pose proof abort_after_code; lia).
          rewrite EXT, orb_true_r. exact I.
      - destruct (chunk_indirect_target lbl D0 dd CP DSN IN) as [TEDGE TEND]. split.
        + exists (i'+j), (toN (rel dd)), eq_refl, eq_refl.
          eapply PEirel; [|exact TEDGE]. rewrite irel_i, irel_in by exact J. reflexivity.
        + exact (TEND s1).
    Qed.
    (* The indirect jump word at position j: it reaches a permitted target
       whenever the branch register holds an IndTgt value. *)
    Lemma ind_jump : forall b lbl rn j w s,
      c0.(cp) = Pindirect lbl ->
      ith c1.(cd) j = Some (Inum w) ->
      (♮w < 2^32 -> forall s s1 c x a,
        exec_stmt arm8typctx s (a64lift a (arm_decode ♮w)) c s1 x ->
        x = Some (Addr (s (arm_varid ♮rn)))) ->
      store_invs s -> IndTgt lbl (s (arm_varid ♮rn)) ->
      K_nib b (Addr 4(i'+cidx j)) s.
    Proof.
      intros b lbl rn j w s CP Q BRX VS TGT.
      pose proof (inum_bound j w s (proj1 VS) Q) as WB.
      eapply ExecInum; [exact VS|exact Q|].
      intros ctx s1 x XS MI. apply (BRX WB) in XS. subst x. cbn [exitof].
      destruct (ind_target lbl _ (cidx j) s (reset_temps s s1) CP TGT (cidx_lt _ _ Q)) as [PS K].
      split; [exact PS|apply K; split; [exact MI|exact I]].
    Qed.
    (* Single destination: an Iimm loads the relocated target into rn. *)
    Lemma ind1_prefix : forall b lbl rn dd D0 z j y s,
      c0.(cp) = Pindirect lbl -> nth_error dsets ♮lbl = Some D0 -> In dd D0 ->
      (rn <? 32 = true)%uint63 ->
      ith c1.(cd) j = Some (Iimm true z rn (Raddr dd)) ->
      ith c1.(cd) (S j) = Some y ->
      (forall s, store_invs s -> IndTgt lbl (s (arm_varid ♮rn)) ->
        K_ni (Addr 4(i'+cidx (S j))) s) ->
      store_invs s -> K_nib b (Addr 4(i'+cidx j)) s.
    Proof.
      intros b lbl rn dd D0 z j y s CP DSN IN R Q Q' EPI VS.
      pose proof (cidx_lt _ _ Q') as LT.
      eapply ExecIimm; [exact VS|exact R|exact Q| |].
      - apply IntraChunkEdge. rewrite irel_i, irel_in by exact LT. reflexivity.
      - apply EPI.
        + apply store_invs_upd; [exact VS|lia].
        + rewrite update_updated. exists D0. split; [exact DSN|].
          right. exists dd. split; [exact IN|]. apply resolve_raddr_val.
    Qed.
    (* The setlr block at j: B over the block, BL back to materialize the
       return address in X30, then the inner instruction at j+2 runs.
       P is any store property that survives writes to X30. *)
    Lemma ExecSetlr : forall b j isz bw lw imm inst (P: store -> Prop) s,
      ith c1.(cd) j = Some (Inum bw) ->
      ith c1.(cd) (S j) = Some (Iimm false isz 30 (Rimm imm)) ->
      ith c1.(cd) (S (S j)) = Some inst ->
      ith c1.(cd) (S (S (S j))) = Some (Inum lw) ->
      (isz = Sz2 /\ bw = 0x14000004 /\ lw = 0x97fffffd \/
       isz = Sz3 /\ bw = 0x14000005 /\ lw = 0x97fffffc)%uint63 ->
      (♮(instsize inst) = 1)%nat ->
      (forall s v, P s -> P (s.[R_X30 := v])) ->
      (forall s, store_invs s -> P s -> K_ni (Addr 4(i'+cidx (S (S j)))) s) ->
      store_invs s -> P s -> K_nib b (Addr 4(i'+cidx j)) s.
    Proof.
      intros b j isz bw lw imm inst P s Q0 Q1 Q2 Q3 SZS SZ PX INNER VS PS.
      pose proof (cidx_Sn' _ _ _ Q0) as C0. pose proof (cidx_Sn' _ _ _ Q1) as C1.
      pose proof (cidx_Sn' _ _ _ Q2) as C2. rewrite SZ in C2.
      pose proof (cidx_lt _ _ Q3) as LT3.
      pose proof (i'cidx_bound (S (S (S j)))) as IPB.
      assert (INTRA : forall k l, (k <= cidx (S (S (S j))))%nat -> (l <= cidx (S (S (S j))))%nat ->
        PermittedEdge' (i'+k) (i'+l))
        by (intros k l K L; apply IntraChunkEdge; rewrite !irel_in by lia; reflexivity).
      destruct SZS as [(->&->&->)|(->&->&->)]; simpl in C0, C1.
      all: eapply ExecInum; [exact VS|exact Q0|].
      all: intros ctx s1 x XS MI.
      all: apply (ExecB (m:=4%uint63) eq_refl) in XS as [ST EXIT]
        || apply (ExecB (m:=5%uint63) eq_refl) in XS as [ST EXIT].
      all: try change (Sint63Axioms.to_Z 4%uint63) with 4%Z in EXIT.
      all: try change (Sint63Axioms.to_Z 5%uint63) with 5%Z in EXIT.
      all: match type of EXIT with
        | _ = Some (Addr (?dst * 4)) =>
            replace dst with (i'+cidx (S (S (S j)))) in EXIT by (unfold ofZ; lia)
        end.
      all: subst x; cbn [exitof]; split.
      all: try (repeat eexists; apply INTRA; lia).
      all: assert (VS1 : store_invs (reset_temps s s1)) by (split; [exact MI|exact I]).
      all: assert (PS1 : P (reset_temps s s1)) by (rewrite ST; exact PS).
      all: eapply ExecInum; [exact VS1|exact Q3|].
      all: intros ctx2 s2 x2 XS2 MI2.
      all: apply (ExecBL (m:=(0-3)%uint63) eq_refl) in XS2 as [ST2 EXIT2]
        || apply (ExecBL (m:=(0-4)%uint63) eq_refl) in XS2 as [ST2 EXIT2].
      all: try change (Sint63Axioms.to_Z (0-3)%uint63) with (-3)%Z in EXIT2.
      all: try change (Sint63Axioms.to_Z (0-4)%uint63) with (-4)%Z in EXIT2.
      all: match type of EXIT2 with
        | _ = Some (Addr (?dst * 4)) =>
            replace dst with (i'+cidx (S j)) in EXIT2 by (unfold ofZ; lia)
        end.
      all: subst x2; cbn [exitof]; split.
      all: try (repeat eexists; apply INTRA; lia).
      all: assert (VS2 : store_invs (reset_temps (reset_temps s s1) s2))
        by (split; [exact MI2|exact I]).
      all: assert (PS2 : P (reset_temps (reset_temps s s1) s2)) by (rewrite ST2; apply PX, PS1).
      all: eapply ExecIimm with (r := 30%uint63); [exact VS2|reflexivity|exact Q1| |].
      all: try (rewrite <-(N.add_0_r i') at 1; apply (INTRA 0%nat); lia).
      all: apply INNER; [apply store_invs_upd; [exact VS2|unfold resolve; lia]|apply PX, PS2].
    Qed.
    (* The hash-table lookup at j: PUSH2 a scratch register, hash rn, load the
       table address into the scratch register, load the table entry into rn,
       POP2 the scratch register.  Afterwards rn holds an IndTgt value. *)
    Lemma hash_prefix : forall b lbl rn D0 j y s,
      c0.(cp) = Pindirect lbl -> nth_error dsets ♮lbl = Some D0 ->
      (rn <? 31 = true)%uint63 ->
      ith c1.(cd) j = Some (Inum (Asm.PUSH2 (b2i (is_zero rn)) 31)) ->
      ith c1.(cd) (S j) = Some (Ihsh rn lbl) ->
      ith c1.(cd) (S (S j)) = Some (Iimm true Sz2 (b2i (is_zero rn)) (Rtbl lbl)) ->
      ith c1.(cd) (S (S (S j))) = Some (Inum (Asm.LDR_r64 rn (b2i (is_zero rn)) rn)) ->
      ith c1.(cd) (S (S (S (S j)))) = Some (Inum (Asm.POP2 (b2i (is_zero rn)) 31)) ->
      ith c1.(cd) (S (S (S (S (S j))))) = Some y ->
      (forall s, store_invs s -> IndTgt lbl (s (arm_varid ♮rn)) ->
        K_ni (Addr 4(i'+cidx (S (S (S (S (S j))))))) s) ->
      store_invs s -> K_nib b (Addr 4(i'+cidx j)) s.
    Proof.
      intros b lbl rn D0 j y s CP DSN R Q0 Q1 Q2 Q3 Q4 Q5 EPI VS.
      set (rt := b2i (is_zero rn)) in *.
      assert (RT : (rt <? 2 = true)%uint63) by (unfold rt; destruct is_zero; reflexivity).
      assert (RTN : rt <> rn).
      { unfold rt. destruct (is_zero rn) eqn:Z; simpl; intro E; rewrite <-E in Z;
          vm_compute in Z; discriminate Z. }
      assert (NRT : arm_varid ♮rn <> arm_varid ♮rt)
        by (apply varid_neq; [lia|lia|intro E; apply RTN; symmetry; exact E]).
      (* the table for lbl *)
      destruct (compute_tables_nth _ _ _ _ _ _ _ tables_D DSN) as (tbl&TN&FH&TCONT&TIDX).
      destruct (nth_error_split _ _ TN) as (l1&l2&TCS&L1).
      assert (PRE : firstn ♮lbl tc = l1)
        by (rewrite TCS, <-L1, firstn_app, Nat.sub_diag, firstn_all; simpl; apply app_nil_r).
      rewrite PRE in TIDX.
      assert (TOT : flat_map tblcontent tc =
        flat_map tblcontent l1 ++ tbl.(tblcontent) ++ flat_map tblcontent l2)
        by (rewrite TCS, flat_map_app; reflexivity).
      pose proof tables_noovfl as TB. rewrite TOT, !nlen_length, !length_app in TB.
      assert (HLEN : (length tbl.(tblcontent) = ♮(Hash.hash_size tbl.(tblhash)))%nat)
        by (rewrite TCONT; apply table_length).
      assert (IDX : ♮tbl.(tblidx) = bti + 2 * length (flat_map tblcontent l1)).
      { rewrite TIDX, len_length. I2N.nify. lia. }
      assert (RES : ♮(resolve d (Rtbl lbl)) = ♮tbl.(tblidx) * 4).
      { unfold resolve. rewrite Util.ith_nth_error, TN. cbn. I2N.nify.
        rewrite N.shiftl_mul_pow2. lia. }
      (* positions *)
      pose proof (cidx_Sn' _ _ _ Q0) as C0. pose proof (cidx_Sn' _ _ _ Q1) as C1.
      pose proof (cidx_Sn' _ _ _ Q2) as C2. pose proof (cidx_Sn' _ _ _ Q3) as C3.
      pose proof (cidx_Sn' _ _ _ Q4) as C4. simpl in C0, C1, C2, C3, C4.
      pose proof (cidx_lt _ _ Q5) as LT5.
      assert (INTRA : forall k l,
        (k <= cidx (S (S (S (S (S j))))))%nat -> (l <= cidx (S (S (S (S (S j))))))%nat ->
        PermittedEdge' (i'+k) (i'+l))
        by (intros k l K L; apply IntraChunkEdge; rewrite !irel_in by lia; reflexivity).
      (* PUSH2 *)
      eapply ExecInum; [exact VS|exact Q0|].
      intros ctx1 s1 x XS MI. clear Q0.
      destruct (ExecPUSH2g RT XS) as [->| ->]; cbn [exitof].
      { split; [exact I|apply KHere; [exact I|split; [exact MI|exact I]]]. }
      split; [repeat eexists; apply INTRA; lia|].
      assert (VS1 : store_invs (reset_temps s s1)) by (split; [exact MI|exact I]).
      clear XS MI. revert VS1. generalize (reset_temps s s1). clear s VS s1. intros s VS.
      (* hash rn *)
      eapply ExecIhsh with (h := tbl.(tblhash)); [exact VS|exact Q1|exact R| | |
        rewrite <-(N.add_0_r i') at 1; apply (INTRA 0%nat); lia|].
      { erewrite nth_error_nth by exact TN. reflexivity. }
      { exact (find_hash_ok _ _ _ FH). }
      intros xh XH.
      assert (VS2 : store_invs (s.[arm_varid ♮rn := xh])) by (apply store_invs_upd; [exact VS|lia]).
      (* table address into rt *)
      eapply ExecIimm with (r := rt); [exact VS2|lia|exact Q2|rewrite <-(N.add_0_r i') at 1; apply (INTRA 0%nat); lia|].
      set (s3 := s.[arm_varid ♮rn := xh].[arm_varid ♮rt := ♮(resolve d (Rtbl lbl))]).
      assert (VS3 : store_invs s3) by (apply store_invs_upd; [exact VS2|lia]).
      (* load the entry *)
      eapply ExecInum; [exact VS3|exact Q3|].
      intros ctx3 s4 x XS MI.
      assert (AL : forall st, ♮rt = 31 -> st R_SP mod 16 = 0) by (intros st E; exfalso; lia).
      apply (ExecLDR64 (ltac:(lia) : (rn <? 32 = true)%uint63) (ltac:(lia) : (rt <? 32 = true)%uint63)
        (AL _)) in XS as [ST ->].
      cbn [exitof]. split; [repeat eexists; apply INTRA; lia|].
      set (xn := N.to_nat xh).
      assert (XN : (xn < length tbl.(tblcontent))%nat) by (rewrite HLEN; unfold xn; lia).
      destruct (nth_error tbl.(tblcontent) xn) as [e|] eqn:E; [|apply nth_error_None in E; lia].
      assert (MEM : getmem 64 LittleE 8 (s3 V_MEM64)
          (s3 (arm_varid ♮rt) ⊕ s3 (arm_varid ♮rn) * 8) = ♮e).
      { destruct VS3 as ((MDL&CODE&DATA&_)&_).
        assert (A : s3 (arm_varid ♮rt) ⊕ s3 (arm_varid ♮rn) * 8 =
          bti * 4 + (length (flat_map tblcontent l1) + xn)%nat * 8).
        { unfold s3. rewrite update_updated, update_frame, update_updated by exact NRT.
          rewrite RES, IDX. unfold xn. rewrite N.mod_small; lia. }
        rewrite A. apply DATA. rewrite ith_nth_error, TOT, nth_error_app2, Nat.add_sub' by lia.
        rewrite nth_error_app1 by exact XN. exact E. }
      rewrite MEM in ST.
      assert (TGT : IndTgt lbl ♮e).
      { exists D0. split; [exact DSN|]. rewrite TCONT in E.
        destruct (table_entry _ _ _ _ _ _ E) as [->|(dd&IN&->)].
        - left. pose proof (ai_bound a d D). I2N.nify. rewrite N.shiftl_mul_pow2. lia.
        - right. exists dd. split; [exact IN|].
          pose proof (relocation_endpoint dd) as (TBD&_). I2N.nify. rewrite N.shiftl_mul_pow2. lia. }
      assert (VS4 : store_invs (reset_temps s3 s4)) by (split; [exact MI|exact I]).
      rewrite ST in VS4 |- *. clear MI ST.
      (* POP2 *)
      eapply ExecInum; [exact VS4|exact Q4|].
      intros ctx6 s6 x XS MI.
      destruct (ExecPOP2g RT XS) as [->|(A&B&C&ST6&->)]; cbn [exitof].
      { split; [exact I|apply KHere; [exact I|split; [exact MI|exact I]]]. }
      split; [repeat eexists; apply INTRA; lia|].
      apply EPI; [split; [exact MI|exact I]|].
      rewrite ST6.
      rewrite (update_frame _ _ _ _ (varid_neq_v rn R_SP R eq_refl)).
      rewrite (update_frame _ _ _ _ (varid_neq_v rn (arm_varid 31) R eq_refl)).
      rewrite (update_frame _ _ _ _ NRT), update_updated. exact TGT.
    Qed.

    (* BR and RET: abort unless the policy is indirect with a destination set. *)
    Lemma chunk_indirect_jump : forall rn,
      (c0.(ct) = Decode.BR rn \/ c0.(ct) = Decode.RET rn) -> Goal.
    Proof.
      intros rn CT'.
      assert (META : metadata c1 = c0).
      { rewrite R1. unfold change_szs, metadata, setd. destruct c0 as [cn ci ct cp cl []]. reflexivity. }
      pose proof (source_nth a d D n c1 NTH) as (_&DEC&_&_&_).
      assert (DEC0 : Decode.decode c0.(cn) = c0.(ct)) by (rewrite <-META; cbn; exact DEC).
      assert (RN : (rn <? 32 = true)%uint63).
      { destruct CT' as [CT|CT]; rewrite CT in DEC0.
        - pose proof (decoded_BR_register _ _ DEC0). I2N.nify. lia.
        - pose proof (decoded_RET_register _ _ DEC0). I2N.nify. lia. }
      assert (RI : rw_inst a c0 = match c0.(cp) with
        | Pindirect lbl => rw_indirect a rn [Inum c0.(cn)] lbl
        | _ => [Ib Sz1 (Decode.BL 0) (Rrt 0)] end).
      { unfold rw_inst. destruct CT' as [CT|CT]; rewrite CT; reflexivity. }
      destruct c0.(cp) as [b|b t| |lbl] eqn:CP; cbv iota in RI.
      1,2,3: apply chunk_abort; rewrite R1; cbn; rewrite RI;
        destruct sz.(cd) as [|x xs]; [exists Sz1|exists (instsz x)]; reflexivity.
      unfold rw_indirect in RI. cbv zeta in RI.
      destruct (Util.ith a.(Rewrite.dsets) lbl orelse []) as [|dd [|d2 rest]] eqn:DSE.
      - cbv iota in RI. apply chunk_abort; rewrite R1; cbn; rewrite RI;
          destruct sz.(cd) as [|x xs]; [exists Sz1|exists (instsz x)]; reflexivity.
      - cbv iota in RI.
        apply orelse_cons in DSE.
        assert (CD : c1.(cd) = [Iimm true Sz3 rn (Raddr dd); Inum c0.(cn)]).
        { rewrite chunk_unrelaxed.
          - exact RI.
          - rewrite RI. intros rel ip inst INST. cbn in INST.
            repeat destruct INST as [<-|INST]; try contradiction; reflexivity. }
        apply (ind1_case rn dd lbl (ex_intro _ Sz3 CD) RN CP).
        + rewrite (arg_same a d D). exact DSE.
        + intros WB s0 s1 ctx x aa XS.
          destruct CT' as [CT|CT]; rewrite CT in DEC0.
          * destruct (word_of_decode_BR _ _ DEC0 WB) as [W _]. rewrite W in XS. exact (ExecBR RN XS).
          * destruct (word_of_decode_RET _ _ DEC0 WB) as [W _]. rewrite W in XS. exact (ExecRET RN XS).
      - (* several destinations: look up a hash table *)
        cbv iota in RI. destruct (rn =? 31)%uint63 eqn:R31; rewrite ?R31 in RI; cbv iota zeta in RI.
        { apply chunk_abort; rewrite R1; cbn; rewrite RI;
            destruct sz.(cd) as [|x xs]; [exists Sz1|exists (instsz x)]; reflexivity. }
        assert (R31' : (rn <? 31 = true)%uint63) by (apply eqb_false_spec in R31; lia).
        assert (DSN : nth_error dsets ♮lbl = Some (dd::d2::rest)).
        { rewrite <-Util.ith_nth_error, (arg_same a d D).
          destruct (Util.ith a.(Rewrite.dsets) lbl); [cbn in DSE; by subst|discriminate]. }
        assert (CD : c1.(cd) = [Inum (Asm.PUSH2 (b2i (is_zero rn)) 31); Ihsh rn lbl;
          Iimm true Sz2 (b2i (is_zero rn)) (Rtbl lbl); Inum (Asm.LDR_r64 rn (b2i (is_zero rn)) rn);
          Inum (Asm.POP2 (b2i (is_zero rn)) 31); Inum c0.(cn)]).
        { rewrite chunk_unrelaxed.
          - exact RI.
          - rewrite RI. intros rel ip inst INST. cbn in INST.
            repeat destruct INST as [<-|INST]; try contradiction; reflexivity. }
        intros s VS. change (i'+0) with (i'+cidx O).
        eapply (hash_prefix false lbl rn _ O); [exact CP|exact DSN|exact R31'|
          rewrite CD; reflexivity..| |exact VS].
        intros s0 VS0 TGT.
        apply (ind_jump true lbl rn 5 c0.(cn) s0 CP); [rewrite CD; reflexivity| |exact VS0|exact TGT].
        intros WB s' s1 ctx x aa XS.
        destruct CT' as [CT|CT]; rewrite CT in DEC0.
        + destruct (word_of_decode_BR _ _ DEC0 WB) as [W _]. rewrite W in XS. exact (proj2 (ExecBR RN XS)).
        + destruct (word_of_decode_RET _ _ DEC0 WB) as [W _]. rewrite W in XS. exact (proj2 (ExecRET RN XS)).
    Qed.

    (* BLR: like BR, but the return address must reach X30.  Under orig_lr the
       original return address is materialized by a setlr block and the BLR
       word is turned into BR. *)
    Lemma chunk_BLR : forall rn, c0.(ct) = Decode.BLR rn -> Goal.
    Proof.
      intros rn CT.
      assert (META : metadata c1 = c0).
      { rewrite R1. unfold change_szs, metadata, setd. destruct c0 as [cn ci ct cp cl []]. reflexivity. }
      pose proof (source_nth a d D n c1 NTH) as (_&DEC&_&_&_).
      assert (DEC0 : Decode.decode c0.(cn) = Decode.BLR rn) by (rewrite <-CT, <-META; cbn; exact DEC).
      assert (RN : (rn <? 32 = true)%uint63)
        by (pose proof (decoded_BLR_register _ _ DEC0); I2N.nify; lia).
      (* the original BLR word jumps to rn *)
      assert (BLRX : ♮c0.(cn) < 2^32 -> forall s s1 c x a,
        exec_stmt arm8typctx s (a64lift a (arm_decode ♮c0.(cn))) c s1 x ->
        x = Some (Addr (s (arm_varid ♮rn)))).
      { intros WB s s1 ctx x aa XS.
        destruct (word_of_decode_BLR _ _ DEC0 WB) as [W _]. rewrite W in XS.
        destruct (ExecBLR RN XS) as (v&_&_&X). exact X. }
      (* the BLR word with bit 21 cleared is BR rn *)
      assert (BRX : ♮(c0.(cn) lxor (1<<21)) < 2^32 -> forall s s1 c x a,
        exec_stmt arm8typctx s (a64lift a (arm_decode ♮(c0.(cn) lxor (1<<21)))) c s1 x ->
        x = Some (Addr (s (arm_varid ♮rn)))).
      { intros WB s s1 ctx x aa XS.
        assert (WB0 : ♮c0.(cn) < 2^32).
        { rewrite I2N.inj_lxor in WB.
          replace ♮c0.(cn) with (N.lxor (N.lxor ♮c0.(cn) ♮(1<<21)%uint63) ♮(1<<21)%uint63)
            by (rewrite N.lxor_assoc, N.lxor_nilpotent, N.lxor_0_r; reflexivity).
          apply (lxor_bound 32); [exact WB|vm_compute; reflexivity]. }
        destruct (word_of_decode_BLR _ _ DEC0 WB0) as [W _].
        rewrite (i2ninj _ _ W), BLR_lxor_BR in XS by exact RN.
        exact (proj2 (ExecBR RN XS)). }
      assert (RI : rw_inst a c0 =
        if a.(orig_lr) && (rn =? 30)%uint63 then
          match c0.(cp) with
          | Pindirect lbl =>
              match Util.ith a.(Rewrite.dsets) lbl orelse [] with
              | [dd] => setlr ((c0.(ci)+1)<<2) (Ib Sz1 (Decode.B 0) (Raddr dd))
              | _ => [Ib Sz1 (Decode.BL 0) (Rrt 0)]
              end
          | _ => [Ib Sz1 (Decode.BL 0) (Rrt 0)]
          end
        else
          match c0.(cp) with
          | Pindirect lbl => rw_indirect a rn
              (if a.(orig_lr) then setlr ((c0.(ci)+1)<<2) (Inum (c0.(cn) lxor (1<<21)))
               else [Inum c0.(cn)]) lbl
          | _ => [Ib Sz1 (Decode.BL 0) (Rrt 0)]
          end).
      { unfold rw_inst. rewrite CT. reflexivity. }
      assert (ABORT : rw_inst a c0 = [Ib Sz1 (Decode.BL 0) (Rrt 0)] -> Goal).
      { intro AB. apply chunk_abort. rewrite R1. cbn. rewrite AB.
        destruct sz.(cd) as [|x xs]; [exists Sz1|exists (instsz x)]; reflexivity. }
      assert (STABLE : forall l, rw_inst a c0 = l ->
        (forall rel ip inst, In inst l -> relaxi rel ip inst = inst) -> c1.(cd) = l).
      { intros l RL ST. rewrite chunk_unrelaxed; [exact RL|]. rewrite RL. exact ST. }
      destruct c0.(cp) as [b|b t| |lbl] eqn:CP.
      1,2,3: apply ABORT; rewrite RI; destruct (_ && _); reflexivity.
      assert (ORS : forall (o: option (list int)) l, o orelse [] = l -> l <> [] -> o = Some l).
      { intros [o|] l E NE; cbn in E; [by subst|]. exfalso. apply NE. symmetry. exact E. }
      assert (DSN : forall D0, Util.ith a.(Rewrite.dsets) lbl = Some D0 ->
        nth_error dsets ♮lbl = Some D0).
      { intros D0 E. rewrite <-Util.ith_nth_error, (arg_same a d D). exact E. }
      intros s VS.
      destruct (a.(orig_lr) && (rn =? 30))%uint63 eqn:LR30; cbv iota in RI.
      - (* BLR X30 under orig_lr: only a single destination is kept *)
        destruct (Util.ith a.(Rewrite.dsets) lbl orelse []) as [|dd [|d2 rest]] eqn:DSE; cbv iota in RI.
        1,3: revert s VS; apply ABORT; exact RI.
        pose proof (DSN _ (ORS _ _ DSE ltac:(discriminate))) as DS.
        destruct (chunk_indirect_target lbl [dd] dd CP DS (or_introl eq_refl)) as [TEDGE TEND].
        assert (RESOLVE : ♮(resolve d (Raddr dd) >> 2) = ♮(rel dd))
          by (pose proof (relocation_endpoint dd) as (TB&_); unfold resolve; I2N.nify;
              rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2; lia).
        unfold setlr in RI. destruct (((c0.(ci)+1)<<2) <? 1<<32)%uint63 eqn:FIT.
        all: assert (CD := STABLE _ RI ltac:(intros rel ip inst INST; cbn in INST;
          repeat destruct INST as [<-|INST]; try contradiction; reflexivity)).
        all: change (i'+0) with (i'+cidx O).
        all: eapply (ExecSetlr false O) with (P := fun _ => True);
          [rewrite CD; reflexivity..
          |first [ (left; split; [reflexivity|split; reflexivity])
                 | (right; split; [reflexivity|split; reflexivity]) ]
          |reflexivity|intros; exact I| |exact VS|exact I].
        all: intros s0 VS0 _.
        all: eapply (ExecIb true 2 s0 Sz1 (Raddr dd) (Decode.B 0));
          [exact VS0|rewrite CD; reflexivity| |intros s1 VS1; rewrite RESOLVE; exact (TEND s1 VS1)
          |exact I|exact I].
        all: rewrite RESOLVE; eapply PEirel; [|exact TEDGE].
        all: rewrite irel_i, irel_in; [reflexivity|eapply cidx_lt; rewrite CD; reflexivity].
      - (* BLR rn keeps rn intact across the X30 writes of setlr *)
        assert (NE30 : orig_lr a = true -> arm_varid ♮rn <> R_X30).
        { intro ORIG. rewrite ORIG in LR30. cbn in LR30.
          apply (varid_neq rn 30 RN eq_refl). intro E. subst rn. vm_compute in LR30. discriminate LR30. }
        assert (PX : orig_lr a = true -> forall lbl s v,
          IndTgt lbl (s (arm_varid ♮rn)) -> IndTgt lbl ((s.[R_X30 := v]) (arm_varid ♮rn))).
        { intros ORIG lbl' s0 v TG. rewrite update_frame by exact (NE30 ORIG). exact TG. }
        (* the epilogue after rn holds an IndTgt value at position j *)
        assert (EPI : forall j, c1.(cd) = take j c1.(cd) ++
            (if a.(orig_lr) then setlr ((c0.(ci)+1)<<2) (Inum (c0.(cn) lxor (1<<21)))
             else [Inum c0.(cn)]) ->
          forall s, store_invs s -> IndTgt lbl (s (arm_varid ♮rn)) ->
          K_ni (Addr 4(i'+cidx j)) s).
        { intros j CDJ s0 VS0 TG.
          assert (Q : forall k x, ith (if a.(orig_lr) then setlr ((c0.(ci)+1)<<2) (Inum (c0.(cn) lxor (1<<21)))
              else [Inum c0.(cn)]) k = Some x -> ith c1.(cd) (k+j) = Some x).
          { intros k x QK. pose proof (ith_Some' _ _ _ _ QK) as QKL.
            pose proof (f_equal (@length _) CDJ) as LEN. rewrite length_app, length_take in LEN.
            assert (J : (j <= length c1.(cd))%nat) by lia.
            rewrite CDJ, ith_nth_error, nth_error_app2; rewrite length_take, Nat.min_l by exact J.
            - rewrite Nat.add_sub, <-ith_nth_error. exact QK.
            - lia. }
          destruct (a.(orig_lr)) eqn:ORIG.
          - unfold setlr in Q. destruct (((c0.(ci)+1)<<2) <? 1<<32)%uint63 eqn:FIT.
            all: eapply (ExecSetlr true j) with (P := fun s => IndTgt lbl (s (arm_varid ♮rn)));
              [apply (Q 0%nat); reflexivity
              |apply (Q 1%nat); reflexivity
              |apply (Q 2%nat); reflexivity
              |apply (Q 3%nat); reflexivity
              |first [ (left; split; [reflexivity|split; reflexivity])
                     | (right; split; [reflexivity|split; reflexivity]) ]
              |reflexivity|exact (PX ltac:(first [exact eq_refl|exact ORIG]) lbl)| |exact VS0|exact TG].
            all: intros s1 VS1 TG1.
            all: eapply (ind_jump true lbl rn (S (S j)) _ s1 CP); [|exact BRX|exact VS1|exact TG1].
            all: apply (Q 2%nat); reflexivity.
          - apply (ind_jump true lbl rn j c0.(cn) s0 CP); [|exact BLRX|exact VS0|exact TG].
            apply (Q 0%nat). reflexivity. }
        unfold rw_indirect in RI. cbv zeta in RI.
        destruct (Util.ith a.(Rewrite.dsets) lbl orelse []) as [|dd [|d2 rest]] eqn:DSE; cbv iota in RI.
        + revert s VS. apply ABORT. exact RI.
        + (* one destination *)
          pose proof (DSN _ (ORS _ _ DSE ltac:(discriminate))) as DS.
          assert (CD : c1.(cd) = Iimm true Sz3 rn (Raddr dd) ::
            (if a.(orig_lr) then setlr ((c0.(ci)+1)<<2) (Inum (c0.(cn) lxor (1<<21)))
             else [Inum c0.(cn)])).
          { apply STABLE; [exact RI|]. intros rel ip inst INST.
            destruct (a.(orig_lr));
              [unfold setlr in INST; destruct (((c0.(ci)+1)<<2) <? 1<<32)%uint63|];
              cbn in INST; repeat destruct INST as [<-|INST]; try contradiction; reflexivity. }
          assert (Q1 : exists y, ith c1.(cd) 1 = Some y)
            by (rewrite CD; destruct (a.(orig_lr));
                [unfold setlr; destruct (((c0.(ci)+1)<<2) <? 1<<32)%uint63|]; eexists; reflexivity).
          destruct Q1 as [y Q1]. change (i'+0) with (i'+cidx O).
          eapply (ind1_prefix false lbl rn dd _ Sz3 O y s CP DS (or_introl eq_refl) RN);
            [rewrite CD; reflexivity|exact Q1| |exact VS].
          apply EPI. rewrite CD. reflexivity.
        + (* several destinations: look up a hash table *)
          destruct (rn =? 31)%uint63 eqn:R31; rewrite ?R31 in RI; cbv iota zeta in RI.
          { revert s VS. apply ABORT. exact RI. }
          assert (R31' : (rn <? 31 = true)%uint63) by (apply eqb_false_spec in R31; lia).
          pose proof (DSN _ (ORS _ _ DSE ltac:(discriminate))) as DS.
          assert (CD : c1.(cd) = [Inum (Asm.PUSH2 (b2i (is_zero rn)) 31); Ihsh rn lbl;
            Iimm true Sz2 (b2i (is_zero rn)) (Rtbl lbl); Inum (Asm.LDR_r64 rn (b2i (is_zero rn)) rn);
            Inum (Asm.POP2 (b2i (is_zero rn)) 31)] ++
            (if a.(orig_lr) then setlr ((c0.(ci)+1)<<2) (Inum (c0.(cn) lxor (1<<21)))
             else [Inum c0.(cn)])).
          { apply STABLE; [exact RI|]. intros rel ip inst INST.
            destruct (a.(orig_lr));
              [unfold setlr in INST; destruct (((c0.(ci)+1)<<2) <? 1<<32)%uint63|];
              cbn in INST; repeat destruct INST as [<-|INST]; try contradiction; reflexivity. }
          assert (Q5 : exists y, ith c1.(cd) 5 = Some y)
            by (rewrite CD; destruct (a.(orig_lr));
                [unfold setlr; destruct (((c0.(ci)+1)<<2) <? 1<<32)%uint63|]; eexists; reflexivity).
          destruct Q5 as [y Q5]. change (i'+0) with (i'+cidx O).
          eapply (hash_prefix false lbl rn _ O y s CP DS R31');
            [rewrite CD; reflexivity..|exact Q5| |exact VS].
          apply EPI. rewrite CD. reflexivity.
    Qed.

    Lemma chunk_cases: Goal.
    Proof.
      intros.
      assert (IGNORE: c0.(ct) = Decode.ignore -> K_nib false (Addr 4(i'+0)) s).
      { intro IGN. by apply chunk_ignore. }
      assert (INVALID: c0.(ct) = Decode.invalid -> K_nib false (Addr 4(i'+0)) s).
      { intro INV. by apply chunk_invalid. }
      assert (ADR: forall imm rd, c0.(ct) = Decode.ADR imm rd -> K_nib false (Addr 4(i'+0)) s).
      { intros imm rd CT. by apply (chunk_ADR imm rd). }
      assert (ADRP: forall imm rd, c0.(ct) = Decode.ADRP imm rd -> K_nib false (Addr 4(i'+0)) s).
      { intros imm rd CT. by apply (chunk_ADRP imm rd). }
      assert (BCOND: forall imm cond, c0.(ct) = Decode.Bcond imm cond -> K_nib false (Addr 4(i'+0)) s).
      { intros imm cond CT. by apply (chunk_Bcond imm cond). }
      assert (B: forall imm, c0.(ct) = Decode.B imm -> K_nib false (Addr 4(i'+0)) s).
      { intros imm CT. by apply (chunk_B imm). }
      assert (BL: forall imm, c0.(ct) = Decode.BL imm -> K_nib false (Addr 4(i'+0)) s).
      { intros imm CT. by apply (chunk_BL imm). }
      assert (CBZ: forall sf op imm rt, c0.(ct) = Decode.CBZ sf op imm rt -> K_nib false (Addr 4(i'+0)) s).
      { intros sf op imm rt CT. by apply (chunk_CBZ sf op imm rt). }
      assert (TBZ: forall b5 op b40 imm rt, c0.(ct) = Decode.TBZ b5 op b40 imm rt -> K_nib false (Addr 4(i'+0)) s).
      { intros b5 op b40 imm rt CT. by apply (chunk_TBZ b5 op b40 imm rt). }
      assert (BRC: forall rn, c0.(ct) = Decode.BR rn -> K_nib false (Addr 4(i'+0)) s).
      { intros rn CT. by apply (chunk_indirect_jump rn (or_introl CT)). }
      assert (RETC: forall rn, c0.(ct) = Decode.RET rn -> K_nib false (Addr 4(i'+0)) s).
      { intros rn CT. by apply (chunk_indirect_jump rn (or_intror CT)). }
      assert (BLRC: forall rn, c0.(ct) = Decode.BLR rn -> K_nib false (Addr 4(i'+0)) s).
      { intros rn CT. by apply (chunk_BLR rn). }
      unfold change_szs, setd in R1, R2; cbn in R1, R2.
      remember (zip_withl _ _ _) eqn:C. remember zip_withl. forget (map _ _).
      destruct c0, cd, ct; cbn in C, R2; subst l. simpl in R1.
      { by apply IGNORE. }
      { by eapply INVALID. }
      { by eapply ADR. }
      { by eapply ADRP. }
      { by eapply BCOND. }
      { by eapply BRC. }
      { by eapply BLRC. }
      { by eapply RETC. }
      { by eapply B. }
      { by eapply BL. }
      { by eapply CBZ. }
      { by eapply TBZ. }
    Qed.
  End ChunkCases.
  Theorem kotori_soundness:
    forall a0 s0 t x s
      (VS: store_invs s0)
      (SC: is_chunk_start_addr a0 = true)
      (ENTRY: startof t (x, s) = (Addr a0, s0)),
    satisfies_all a64prog K_invs K_exits ((x,s)::t).
  Proof.
    intros. apply prove_invs.
    - cbn. rewrite ENTRY. apply NIHere. cbv [effinv K_invs K_inv_point]. by rewrite SC, orb_true_r.
    - intros. cbv[get_precondition true_inv K_invs K_inv_point] in PRE.
      repeat case_match; try done. inversion H; subst.
      cbn in H0. rewrite H0, orb_false_l in H2. destruct PRE as [PS VT].

      rewrite cons1. apply clear_trace; auto. simpl in VT.
      apply startschunk_idx in H2 as [n [LEN N]]. subst.
      rewrite <-(N.add_0_r (_+_)). eapply (chunk_cases n).
      + apply ith_nth'. rewrite (num_cnks d) in LEN; lia || auto.
      + repeat so D. remember (change_szs _ _). remember d.(chunks).
        rewrite <-D in Heql. simpl in Heql. subst l c.
        unfold stage3, stage2. by rewrite relaxn_same, nth_zip, map_nth.
      + reflexivity.
      + reflexivity.
      + auto.
        Unshelve. all: apply (C[nil]) || apply (C[()]).
  Qed.
End Soundness.
