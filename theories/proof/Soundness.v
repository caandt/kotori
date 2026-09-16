From coqutil Require Import Tactics.fwd autoforward.
From Stdlib Require Import ZArith.
From stdpp Require Import list list_basics.
From Kotori Require Import Rewrite proof.Util proof.Rewrite.
From Picinae Require Import armv8 armv8_lifter_rework.
Import ARM8Arch.
Notation a64prog := arm8_prog.
Notation a64lift := arm2il.
Notation a64dec := arm_decode.

Ltac fwd_rewrites ::= fwd_rewrites_autorewrite.

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
  Notation bi := ♮d.(arg).(bi).
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
    xbits (s A_WRITE) (bi' * 4) (bi' * 4 + (lensT tc) * 8) = 0.
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
  Lemma nlen_flat':
    forall A B (f: A -> list B) l, nlen (flat_map f l) = length (concat (map f l)).
  Proof.
    intros. by rewrite nlen_length, flat_map_concat_map.
  Qed.
  Section ChunkCases.
    Variable n : nat.
    Variable cc : chunk (list cinst).
    Variable ic : chunk (list int).

    Definition i := ic.(ci).
    Definition i' := bi' + lensC[:n] cnks.
    Definition ni' := bi' + lensT[:S n] tc.

    Notation c := ic.(cd).

    Variable NTH : ith cnks n = Some ic.
    Variable R : ic = setd cc (nconcat (instmapi (rel cc.(ci)) (isel d) cc.(cd))).

    Lemma irel_in:
      forall n (N: n <ₒ length c), irel (i' + n) = ♮i.
    Proof.
      intros. unfold i, i', irel.
      rewrite nlen_flat, <-!firstn_map, findchunk_in' with (d:=C[nil]).
      - eapply ith_nth in NTH. by rewrite NTH.
      - eapply nonempty_cnks, RW.
      - apply ith_Some. by rewrite NTH.
      - eapply ith_nth in NTH. rewrite NTH, nlen_length. lia.
    Qed.
    Lemma not_ext:
      forall n (N: n <ₒ length c), is_ext_addr 4(i' + n) = false.
    Proof.
      intros. unfold is_ext_addr, i'. rewrite !nlen_flat, <-!firstn_map.
      lia with (nsum_firstn_le (cmap nlen cnks) (S n)) by
        erewrite nsum_take_Sn', nlen_length by by rewrite !ith_map, NTH.
    Qed.
    Notation favs P := (forall (s:store) (VS: store_invs s), P s) (only parsing).
    Notation Goal := (favs (K_nib false (Addr 4(i'+0)))) (only parsing).
    Lemma code: forall s (VS: mem_invs s), MemHas s c i' 4.
    Proof.
      intros. destruct_and! VS. unfold i'.
      rewrite nlen_flat', <-firstn_map.
      apply memhas_ith.
      - by rewrite ith_map, NTH.
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
      repeat so LU; subst.
      eapply noassign_stmt_same in XS.
    Admitted.
    Lemma KStep:
      forall b j s q
        (VS: store_invs s)
        (Q: ith (map (arm_decode ∘ toN) c) j = Some q)
        (STEP: forall c1 s1 x1
        (XS: exec_stmt arm8typctx s (a64lift 4(i'+j) q) c1 s1 x1)
          (VS: mem_invs (reset_temps s s1)),
          PermittedStep (
            exitof 4(i'+N.succ j) x1, reset_temps s s1,
           (Addr 4(i'+j), s)
          ) ∧ K_ni (exitof 4(i'+N.succ j) x1) (reset_temps s s1)),
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
        rewrite N.add_succ_r, N.mul_succ_l in STEP.
        specialize (STEP _ _ _ XS). hintro STEP.
        + fwd. apply clear_trace'.
          * by apply STEPp1.
          * by apply Forall_singleton.
        + eapply mem_invs_step.
          * apply exec_prog_step; [apply exec_prog_none|econstructor; apply P || apply XS].
          * by destruct VS.
    Admitted.
    Lemma chunk_cases: Goal.
    Proof.
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
      + apply ith_nth'. lia.
      + repeat so RW. rewrite <-RW, map_map. rewrite <-RW, !length_map in LEN.
        apply Some_inj. rewrite <-nth_error_nth' by (rewrite length_map; lia).
        now erewrite map_nth_error by (apply nth_error_nth';lia).
      + assumption.
        Unshelve. all: apply (C[nil]).
  Qed.
End Soundness.
