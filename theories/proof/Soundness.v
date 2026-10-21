From coqutil Require Import Tactics.fwd autoforward.
From Stdlib Require Import ZArith ZifySint63.
From stdpp Require Import list list_basics.
From Kotori Require Import Rewrite proof.Util proof.Rewrite proof.Decode proof.Exec proof.I2N.
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


Definition arm8_prog s a :=
  match a mod 4, xbits (s UXN) (a mod 2^64) (N.succ (a mod 2^64)) with
  | 0, 0 => Some (4, arm2il a (arm_decode (getmem 64 LittleE 4 (s V_MEM64) a)))
  | _, _ => None end.

Theorem welltyped_arm8_prog: welltyped_prog arm8typctx arm8_prog.
Proof.
  intros s a. unfold arm8_prog.
  destruct (a mod 4); try done. destruct (xbits (s UXN) _ _); try done.
  exists arm8typctx. admit.
Admitted.
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
    xbits (s A_WRITE) (bti * 4) (bti * 4 + (lensT tc) * 8) = 0.
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
  Lemma noovfl: NoOverflow bi' cnks.
  Proof.
    repeat so RW. case_match; try done. apply sumltlt in Heqb0. subst' RW.
    rewrite map_map in *. simpl in Heqb0.
    remember (map _ _). replace (map _ _) with l. lia. subst.
    apply map_ext_in. intros. rewrite len_nlen. admit.
  Admitted.
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
      destruct VS as (MDL&CODE&DATA&NWC&NWD).
      inversion XP. inversion H1. subst. clear H1 H2.
      repeat so LU; subst. apply (noassign_stmt_same A_WRITE) in XS as AW; [|apply noassign_awrite_arm2il].
      repeat split.
      - eapply (preservation_exec_prog _ welltyped_arm8_prog); by try apply XP.
      - intros j m ITH. cbn. erewrite <-nonwritable_mem_arm2il. by apply CODE. apply XS. intros.
        rewrite testbit_xbits. destruct (N.lt_decidable k (2^64)).
        + pose proof (proj1 (ith_Some (flat_map cd cnks) j) ltac:(by rewrite ITH)).
          remember (bi' * _ + j * 4) as n0.
          destruct (N.lt_decidable k n0).
          * assert (bi' * 4 + lensC cnks * 4 < 2 ^ 64) by admit. rewrite nlen_length in H3.
            lia with (msub_wrap 64 k n0).
          * rewrite msub_sub, N.mod_small in H by lia. erewrite xbits_inner, NWC, xbits_0_l. easy. lia. rewrite nlen_length. lia.
        + rewrite xbits_above; auto. specialize (MDL A_WRITE _ ltac:(done)).
          eapply (N.lt_le_trans _ _ _ MDL), N.pow_le_mono_r; clear -H0; lia.
      - intros j m ITH. cbn. erewrite <-nonwritable_mem_arm2il. by apply DATA. apply XS. intros.
        rewrite testbit_xbits. destruct (N.lt_decidable k (2^64)).
        + pose proof (proj1 (ith_Some (flat_map tblcontent tc) j) ltac:(by rewrite ITH)).
          remember (bti * _ + j * 8) as n0.
          destruct (N.lt_decidable k n0).
          * assert (bti * 4 + lensT tc * 8 < 2 ^ 64) by admit. rewrite nlen_length in H3.
            lia with (msub_wrap 64 k n0).
          * rewrite msub_sub, N.mod_small in H by lia. erewrite xbits_inner, NWD, xbits_0_l. easy. lia. rewrite nlen_length. lia.
        + rewrite xbits_above; auto. specialize (MDL A_WRITE _ ltac:(done)).
          eapply (N.lt_le_trans _ _ _ MDL), N.pow_le_mono_r; clear -H0; lia.
      - inversion AW. cbn; by rewrite <-H0.
      - inversion AW. cbn; by rewrite <-H0.
    Admitted.
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
      { unfold a64prog. rewrite (mp2_mod_mul _ 2). case_match.
        - by rewrite N.mul_add_distr_r, (code s (proj1 VS) j _ oe), Q.
        - admit. }
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
    Admitted.
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
    Lemma cidxn:
      forall {j x}
        (A: ith c1.(cd) j = Some x),
      drop (cidx j) c3.(cd) =
      (l3l (isel d ♯(i' + cidx j) x)) ++ drop (cidx (S j)) c3.(cd) /\
      isel d ♯(i' + cidx j) x <> Lst0.
    Proof.
      intros. erewrite <-(firstn_skipn ♮(instsize x) (drop _ _)), skipn_skipn.
      rewrite (cidx_Sn' _ _ _ A), Nat.add_comm.
      rewrite (and_iff_compat_r); [|split; try apply app_inv_tail; intro; by rewrite H].
      specialize no_lst0.
      rewrite R3, R2, <-(add_0_r (rel c1.(ci))), <-(add_0_r (ofN _)), Forall_forall.
      simpl. revert x j A. unfold instmapi.
      generalize 0%uint63. clear. induction c1.(cd); [done|]; intros.
      setoid_rewrite mapi_cons. simpl. destruct j.
      - unfold cidx'. inversion A; subst.
        rewrite firstn_O, skipn_O, firstn_app, firstn_all2, List.firstn_eq_O, app_nil_r.
        + repeat f_equal. simpl. rewrite N.add_0_r. split. admit.
           apply H. rewrite mapi_cons. left. admit.
        + rewrite instsize_correct'; lia || apply H. rewrite mapi_cons. by left.
        + rewrite instsize_correct'; lia || apply H. rewrite mapi_cons. by left.
      - rewrite skipn_app, skipn_all2, app_nil_l.
        + specialize (IHl (add i0 (instsize a)) _ _ A).
          rewrite instsize_correct', <-add_assoc, cidx_cons, Nat.add_sub'.
          hintro IHl. destruct IHl. setoid_rewrite H0. split.
          * do 2 f_equal. lia.
          * eapply ZifyClasses.eq_iff; [  | exact H1 ]. do 3 f_equal. lia.
          * intros. apply H. unfold instmapi in *.
            rewrite mapi_cons, <-add_assoc. simpl. by right.
          * apply H. setoid_rewrite mapi_cons. by left.
        + rewrite cidx_cons, instsize_correct'. lia.
          apply H. setoid_rewrite mapi_cons. by left.
    Admitted.
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
        (R: (r <? 31 = true)%uint63)
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
        apply (ExecADRP H1) in XS as [S' X']; [|lia].
        replace (lsr _ 10) with ♯((i' + cidx j) >> 10) in S' by blia.
        rewrite plusminus52 in S' by blia. subst x. simpl exitof.
        outchunk. eqapply STEP. lia. eqapply S'. unfold clearlow12 in H0. blia.
      - destruct Asm.ADR eqn:ADR; try done.
        step C. repeat so ADR. subst i0. simpl in XS.
        apply (ExecADR H1) in XS as [S' X']; [|blia..].
        subst x. simpl exitof.
        outchunk.
        rewrite S', plusminus62 by lia.
        eqapply STEP; try lia. nify. by rewrite <-(N.shiftl_mul_pow2 _ 2), recompose_bytes'.
      - destruct Asm.ADRP eqn:ADRP.
        + step C. repeat so ADRP. subst i0. simpl in XS.
          apply (ExecADRP H1) in XS as [S' X']; [| lia].
          subst x. simpl exitof.
          inchunk.
          replace (lsr _ 10) with ♯((i' + cidx j) >> 10) in S' by blia.
          rewrite plusminus52 in S' by blia. subst' S'. clear c s0.
          step C.
          apply ExecMovk in XS as [S' X']; [|blia..].
          rewrite update_updated, update_cancel in S'.
          subst x. simpl exitof.
          outchunk. eqapply STEP. lia. rewrite S'. f_equal.
          rewrite rbits_0_i, land16, cbits_add by lia. nify. blia.
        + step C; apply ExecUDF in XS as [S' X']; subst; repeat eexists; by apply KHere.
      - step C.
        apply ExecMovz in XS as [S' X']; [|lia..].
        subst x. simpl exitof.
        inchunk. simp (_<<4). subst' S'. clear c s0.
        step C. apply ExecMovk in XS as [S' X']; [|blia..].
        rewrite update_updated, update_cancel in S'.
        subst x. simpl exitof.
        outchunk. eqapply STEP. lia. rewrite S'. f_equal.
        rewrite rbits_0_i, cbits_add; blia.
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
        rewrite rbits_0_i, cbits_add, !land16.
        nify. rewrite (rbits_mod_r _ _ _ 16).
        rewrite rbits_0'. clear -H0. blia.
        rewrite <-shiftr_mod_xbits. blia.
        lia.
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
        apply (ExecBcond H1) in XS as [S' X']; [|cones; rewrite landones; lia].
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
        apply (ExecCBZ H1) in XS as [S' X']; [|cones; rewrite landones; lia..].
        destruct X'; subst x; simpl exitof.
        rewrite plusminus62 by lia.
        outchunk. by apply STEP.
        outchunk. eqapply STEP'; auto; lia.
      - destruct Asm.TBZ eqn:TBZ; try done.
        step C. simpl in XS. repeat so TBZ. subst i0.
        apply (ExecTBZ H1) in XS as [S' X']; [|cones; rewrite landones; lia..].
        destruct X'; subst x; simpl exitof.
        rewrite plusminus62 by lia.
        outchunk. by apply STEP.
        outchunk. eqapply STEP'; auto; lia.
      - destruct Asm.Bcond eqn:BCOND; destruct Asm.B eqn:B; try done.
        + step C. simpl in XS. repeat so BCOND. subst i0.
          apply (ExecBcond H1) in XS as [S' X']; [|cones; rewrite landones; lia..].
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
          apply (ExecCBZ H1) in XS as [S' X']; [|cones; rewrite landones || destruct is_zero; simpl; try lia..].
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
          apply (ExecTBZ H1) in XS as [S' X']; [|cones; rewrite landones || destruct is_zero; simpl; try lia..].
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
        apply ExecUBFX in XS as [m [S' [X' M]]]; try lia.
        subst x0. simpl exitof.
        outchunk. subst' S'. specialize (STEP m). hintro STEP.
        eqapply STEP. lia. eqapply M. simpl. nify.
        rewrite N.mod_small. blia. rewrite N.shiftl_mul_pow2, N.mul_1_l. apply N.pow_lt_mono_r; lia.
      - step C. simpl in XS.
        apply ExecEOR in XS as [m0 [S' X']]; try lia.
        subst x0. simpl exitof.
        inchunk. subst' S'. clear c s0.
        step C. simpl in XS.
        apply ExecUBFX in XS as [m [S' [X' M]]]; try lia.
        subst x0. simpl exitof.
        outchunk. subst' S'. rewrite update_cancel. specialize (STEP m). hintro STEP.
        eqapply STEP. lia. eqapply M. simpl. nify.
        rewrite N.mod_small. blia. rewrite N.shiftl_mul_pow2, N.mul_1_l. apply N.pow_lt_mono_r; lia.
    Qed.

    Lemma chunk_cases: Goal.
    Proof.
      intros. unfold change_szs, setd in R1, R2; cbn in R1, R2.
      remember (zip_withl _ _ _) eqn:C. remember zip_withl. forget (map _ _).
      destruct c0, cd, ct; cbn in C, R2; subst l. simpl in R1.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      unfold rw_indirect in *.
      admit.
      admit.
      admit.
      admit.
      admit.
      (* apply zwcs in C as [? [? C]]; simpl in C. *)
      (* admit. admit. *)
      (* cbv in R2. *)
    Admitted.
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
