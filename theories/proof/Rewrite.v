From Stdlib Require Import ZArith.
From stdpp Require  Import list_tactics.
From Kotori Require Import proof.Util proof.I2N Rewrite.
From RecordUpdate Require Import RecordUpdate.

Definition cons1{A} (a:A) t : a::t=[a]++t := eq_refl.
Lemma mapi_acc{A B sz} {f: int -> A -> B}:
  forall l i acc, _mapi sz acc i f l = rev acc ++ _mapi sz [] i f l.
Proof.
  induction l; intros.
    by rewrite rev_alt, app_nil_r.
    simpl. by rewrite IHl, (IHl _ [_]), app_assoc.
Qed.
Lemma mapi_cons{A B sz} {f: int -> A -> B}:
  forall i acc a t,
    _mapi sz acc i f (a::t) = rev acc ++ f i a :: _mapi sz [] (i+sz a) f t.
Proof.
  intros. simpl. by rewrite mapi_acc, (cons1 _ (_mapi _ _ _ _ _)), app_assoc.
Qed.
Lemma mapi_nth{A B} {f: int -> A -> B}:
  forall l n x d, nth_error (mapi f l) n = Some x -> x = f ♯n (nth n l d).
Proof.
  unfold mapi. setoid_rewrite <-(plus_O_n) at 2. change 0 with ♯O. generalize O.
  intros. move l after n. revertall.
  induction l; intros.
    cbn in H. by rewrite nth_error_nil in H.
    rewrite mapi_cons in H. simpl in H. destruct n0.
      inversion H. f_equal. lia.
      simpl in *. rewrite <-Nat.add_succ_comm. apply IHl. rewrite <-H. repeat f_equal. lia.
Qed.
Goal forall a n c, nth_error (stage1 a) n = Some c -> c.(ci) = a.(bi) + ♯n.
Proof.
  intros. unfold stage1 in H. apply mapi_nth with (d:=0) in H. rewrite H. simpl. lia.
Qed.

Fixpoint findchunk c b i :=
  match c with
  | c::tail =>
      let l := @length int c.(cd) in
      if (b <=? i)%nat && (i <? b + l)%nat
      then ♮c.(ci)
      else findchunk tail (b + l)%nat i
  | nil => i
  end.
Notation cmap f l := (map f (map cd l)).
Definition Nonempty{A} x := cd x <> @nil A.
Notation NoOverflow b c := (b + nsum (cmap (@length int) c) < Z.to_nat (2 ^ 62))%nat.
Definition nsum_nil : nsum [] = O := eq_refl.
Lemma inj_sum:
  forall lst, ♮(isum lst) = (nsum (map toNat lst) mod Z.to_nat wB)%nat.
Proof.
  unfold isum, nsum. change O with ♮0.
  intro. generalize lst 0%uint63.
  induction lst0; cbn [map fold_left].
    lia.
    intro. unfold toNat in *. now rewrite nfls, ifls, !I2Z.inj_add, !Z2Nat.inj_mod, !Z2Nat.inj_add, !Z2Nat.inj_mod,
      !Z2Nat.inj_add, IHlst0, Nat.Div0.add_mod_idemp_l, Nat.Div0.add_mod_idemp_r by lia.
Qed.
Lemma i2ninj: forall i j, ♮i = ♮j -> i = j. Proof. lia. Qed.
Lemma isumn:
  forall lst, isum lst = ♯(nsum (map toNat lst)).
Proof. intros. apply i2ninj. rewrite inj_sum. lia. Qed.

Ltac eqapply H := eapply ZifyClasses.eq_iff;[|exact H];repeat f_equal.
Lemma to_of_nat : forall x, ♮♯x = (x mod Z.to_nat wB)%nat. Proof. lia. Qed.

Lemma findchunk_out:
  forall c b i
    (NO: NoOverflow b c)
    (I: (i < b)%nat ∨ (b + nsum (cmap length c) <= i)%nat),
  findchunk c b i = i.
Proof.
  induction c; intros.
    reflexivity.
    simpl. fif. rewrite IHc; auto.
    all: simpl in *; rewrite nsum_cons in *; lia.
Qed.
Lemma nsum_firstn_le:
  forall l n,
  (nsum (firstn n l) <= nsum l)%nat.
Proof.
  induction l; intros.
    now rewrite firstn_nil.
    destruct n; simpl. cbn. lia. rewrite !nsum_cons. specialize (IHl n). lia.
Qed.
Lemma findchunk_in:
  forall c b n d
    (NE: Forall Nonempty c)
    (N: n < length c),
    findchunk c b (b + nsum (firstn n (cmap length c))) = ♮(nth n c d).(ci).
Proof.
  induction c; intros.
    easy.
    destruct n; simpl.
    - tif.
        reflexivity. rewrite nsum_nil. inversion NE. unfold Nonempty in H1.
        destruct a.(cd). done. simpl. lia.
    - fif. rewrite nsum_cons, Nat.add_assoc, IHc with (d:=d).
        reflexivity.
        by inversion NE.
        simpl in N. lia.
      rewrite nsum_cons, Nat.add_assoc. lia.
Qed.
Lemma nconcat_concat:
  forall l (L: Forall (.≠ Lst0) l),
    nconcat l = concat (map l3l l).
Proof.
  destruct l; intros; auto.
  cbn. rewrite <-rev_alt.
  replace (match l with Lst0 => _ | _ => _ end) with (rev (l3l l)) by now destruct l.
  inversion L; subst. assert (l3l l <> []) by now destruct l.
  revert H. clear L H1. generalize (l3l l).
  induction l0; intros.
    simpl. now rewrite rev_involutive, app_nil_r.
    simpl. replace (napp _ _) with (rev (l1++l3l a)).
      rewrite IHl0.
        now rewrite app_assoc.
        now inversion H2.
        now destruct l1.
      decompose_Forall. rewrite rev_app_distr. enough (rev l1 <> nil).
        revert H2. generalize (rev l1). now destruct a, l2.
        destruct l1. easy. symmetry. apply app_cons_not_nil.
Qed.

Lemma napp_lst0: forall l, napp l Lst0 = []. Proof. by induction l. Qed.
Lemma nconcat_lst0:
  forall l, In Lst0 l -> nconcat l = nil.
Proof.
  intros. apply in_split in H as [? [? ?]]. subst.
  unfold nconcat. rewrite <-rev_alt. apply rev_inj. simpl. rewrite rev_involutive.
  destruct x; simpl.
    by induction x0.
    remember (match _ with Lst0 => _ | _ => _ end). generalize y. clear Heqy.
    induction x; intros. simpl. rewrite napp_lst0. by induction x0.
  simpl. by rewrite IHx.
Qed.
Lemma nconcat_notnil:
  forall l, nconcat l <> nil -> Forall (.≠ Lst0) l.
Proof.
  intros. apply Forall_forall. intros x I X. subst. now apply nconcat_lst0 in I.
Qed.
Lemma nonenil_correct:
  forall c, nonenil c = true <-> Forall Nonempty c.
Proof.
  induction c.
    easy.
    split; intros; cbn in *.
      constructor.
        unfold notnil, Nonempty in *. destruct a.(cd); auto.
          clear IHc. induction c; now try apply IHc.
        apply IHc. clear IHc. induction c; auto.
          cbn in *. destruct notnil; auto.
            clear IHc. exfalso. induction c; now try apply IHc.
      inversion H. apply IHc in H3. unfold nonenil, notnil, Nonempty in *. now destruct cd.
Qed.
Notation "a ∈ b , c" := (a = b \/ a = c) (at level 70, b at next level).
Lemma intleb_natle: forall i j, i <=? j = true -> ♮i <= ♮j. Proof. lia. Qed.
Lemma Nat2I_inj_add: forall a b, ♯(a + b) = ♯a + ♯b. Proof. lia. Qed.
Lemma chunksize_correct:
  forall x d i c
    (NE: Forall (.≠ Lst0) (instmapi i (isel d) x))
    (C: c.(cd) = x),
  len (nconcat (instmapi i (isel d) x)) = chunksize c.
Proof.
  unfold instmapi. intros. replace c with (c<|cd:=x|>) by (destruct c; now subst).
  clear C. revertall. induction x; intros; cbn in *.
  - reflexivity.
  - rewrite nconcat_concat, mapi_acc by assumption. rewrite mapi_acc, Forall_app in NE. simpl.
    rewrite len_length, length_app, Nat2I_inj_add, <-!len_length, <-nconcat_concat, IHx with (c:=c) by easy.
    unfold chunksize. simpl. rewrite isum_cons. f_equal.
  { apply proj1, Forall_inv in NE. clear -NE. remember (isel _ _ _) in *.
    unfold isel in Heql. destruct a.
    - now subst.
    - destruct sz.
      + destruct (_ _ _ r); now subst.
      + repeat case_match; now subst.
      + repeat case_match; now subst.
    - repeat case_match; now subst.
    - repeat case_match;
      repeat match type of Heql with
        context[?a <&> _] => destruct a; now subst
       end; now subst. }
Qed.
Ltac subst' H := rewrite H in *; clear H.

Lemma isum_bound:
  forall max l
    (B: Forall (λ x, x <=? max = true) l)
    (O: length l * ♮max < Z.to_nat wB),
    to_nat (isum l) <= length l * ♮max.
Proof.
  induction l; intros.
    cbn. lia.
    rewrite isum_cons. simpl in *. inversion B; subst.
    hintros IHl; auto; lia.
Qed.
Section rw2.
  Variable d : data.
  Variable cnks : chunklist (list int).
  Variable RW : rw2 d = Some cnks.

  Notation ai := d.(ai).
  Notation tc := d.(tc).
  Notation rel := d.(rel).
  Notation bi := d.(arg).(bi).
  Notation bi' := d.(arg).(bi').
  Notation pol := d.(arg).(pol).
  Notation dsets := d.(arg).(dsets).

  Variable MR : (rel, ai) = makerel d.(arg) d.(chunks).
  Variable NO : NoOverflow ♮bi' cnks.
  Variable CL : Forall (λ c, length c.(cd) < 100)%nat cnks.
  Variable CORD : forall n c, nth_error d.(chunks) n = Some c -> c.(ci) = bi + ♯n.
  Variable NN: csum bi' (map chunksize d.(chunks)) (len d.(chunks)) <=? ai = true.

  Definition irel i := findchunk cnks ♮bi' i.

  Lemma correct_lens:
    cmap len cnks = map chunksize d.(chunks).
  Proof.
    repeat so RW; subst; clear -Heqb. apply nonenil_correct in Heqb.
    rewrite !map_map in *. apply map_ext_in.
    intros; destruct a; simpl in *.
    erewrite chunksize_correct with (x:=cd); auto.
    rewrite Forall_forall in *.
    intros x I X; subst. apply nconcat_lst0 in I.
    eapply in_map, Heqb in H. simpl in H. now subst' I.
  Qed.
  Lemma correct_lengths:
    cmap length cnks = map toNat (map chunksize d.(chunks)).
  Proof.
    rewrite <-correct_lens. clear -CL. induction cnks; simpl.
      reflexivity.
      rewrite IHl, len_length by now inversion CL. f_equal. inversion CL. lia.
  Qed.
  Lemma no_lst0:
    forall a (A: In a d.(chunks)),
    Forall (.≠ Lst0) (instmapi (rel a.(ci)) (isel d) a.(cd)).
  Proof.
    repeat so RW; subst; clear -Heqb. apply nonenil_correct in Heqb.
    intros. rewrite !Forall_map, Forall_forall in Heqb. apply Heqb in A.
    now apply nconcat_notnil.
  Qed.
  Lemma chunk_equiv:
    cnks = chunkmap (λ x, concat (map l3l (instmapi (rel x.(ci)) (isel d) x.(cd)))) d.(chunks).
  Proof.
    pose proof no_lst0 as NL.
    repeat so RW; subst; clear -NL.
    rewrite map_map. apply map_ext_in.
    intros. now rewrite nconcat_concat by now apply NL.
  Qed.
  Lemma nonempty_cnks: Forall Nonempty cnks.
  Proof.
    repeat so RW. apply nonenil_correct in Heqb. now rewrite RW in Heqb.
  Qed.
  Lemma nth_ci:
    forall n c, nth_error cnks n = Some c -> c.(ci) = bi + ♯n.
  Proof.
    intros n c N. rewrite chunk_equiv in N.
    apply nth_error_nth with (d:=C 0 0 Decode.ignore []) in N as NTH.
    rewrite <-NTH, <-(map_nth ci), map_map in *. simpl.
    change 0 with ((C 0 0 Decode.ignore (@nil cinst)).(ci)).
    erewrite map_nth, CORD; auto. apply nth_error_nth'.
    apply nth_error_Some. intro. by rewrite nth_error_map, H in N.
  Qed.
  Lemma num_cnks: length cnks = length d.(chunks).
  Proof. now rewrite chunk_equiv, length_map. Qed.
  Lemma chunklenbound: Forall (λ c, length c.(cd) < 100) d.(chunks).
  Proof.
    pose proof no_lst0 as NL.
    rewrite chunk_equiv, Forall_map in CL. rewrite Forall_forall in *.
    intros x IN. specialize (CL _ IN). specialize (NL _ IN).
    destruct x. cbn in *. revert NL CL. clear.
    generalize 100%nat, (rel ci). induction cd; auto; simpl; intros.
    unfold instmapi in *. rewrite mapi_cons in *. cbn in *.
    rewrite length_app in CL. apply Nat.lt_add_lt_sub_l in CL.
    decompose_Forall. apply IHcd in CL; auto. destruct isel; simpl in CL; lia || done.
  Qed.
  Lemma instsizeb:
    forall i, (1 <=? instsize i) && (instsize i <=? 3) = true.
  Proof.
    intros. unfold instsize, intsize. now repeat case_match.
  Qed.
  Lemma maxchunks:
    length d.(chunks) < Z.to_nat (2 ^ 62).
  Proof.
    clear NN. pose proof nonempty_cnks. pose proof CL. pose proof chunklenbound.
    apply (Nat.le_lt_trans _ (nsum (cmap length cnks))); [|lia].
    rewrite correct_lengths. rewrite chunk_equiv in H, H0. clear -H H0 H1. induction chunks; simpl.
      easy.
      rewrite nsum_cons. decompose_Forall; subst. enough (0 < ♮(chunksize a)).
        hintros IHl; lia || by decompose_Forall.
        unfold chunksize. destruct cd.
          easy.
          simpl. rewrite isum_cons. pose proof (isum_bound 100 (map_single instsize y)) as B.
          rewrite length_map in B. hintros B.
            pose (instsizeb c). lia.
            simpl in *. lia.
            rewrite Forall_map, Forall_forall. intros. pose (instsizeb x). lia.
  Qed.
  Lemma irel_rel:
    forall i, irel ♮(rel i) ∈ ♮i, ♮ai.
  Proof.
    unfold irel.
    inversion MR. intro. subst' H0.
    assert (♮bi' + nsum (cmap length cnks) ≤ ♮ai) as A; subst' H1.
    { etransitivity; [|apply intleb_natle, NN].
      rewrite csum_def, firstn_all2, isumn, correct_lengths, !map_map.
        pose proof NO. rewrite correct_lengths, map_map in H. lia.
        rewrite len_length, length_map. pose proof maxchunks. lia. }
    repeat case_match.
    - rewrite csum_def, isumn, <-firstn_map, <-correct_lengths.
      rewrite len_length in H.
      rewrite I2Nat.inj_add, to_of_nat, Nat.Div0.add_mod_idemp_r, Nat.mod_small.
      rewrite findchunk_in with (d:=C 0 0 Decode.ignore []).
      erewrite nth_ci; [|apply nth_error_nth'; rewrite num_cnks; lia].
      left. lia. apply nonempty_cnks. rewrite num_cnks. lia.
      unfold NoOverflow in *. pose proof (nsum_firstn_le (cmap length cnks) ♮(i-bi)). lia.
    - rewrite findchunk_out; [now right | easy | lia].
    - rewrite findchunk_out; [now left | easy | lia].
  Qed.
End rw2.
