From Stdlib Require Import List Uint63 PString Lia ZifyUint63 ZArith Utf8.
From Kotori Require Export Strl.
Import SL.

Lemma lo_get:
  forall sl i, get sl i = nth (to_nat i) (LO sl) 0.
Proof.
  induction sl; intros; unfold list_of_strl.
    simpl. now destruct (_:nat).
    simpl. destruct ltb eqn:LT.
      rewrite app_nth1. apply get_spec.
      rewrite <-length_spec. lia.
    rewrite IHsl. rewrite app_nth2, <-length_spec. f_equal. lia.
    rewrite <-length_spec. lia.
Qed.
Lemma lo_cat:
  forall sl1 sl2, LO (cat sl1 sl2) = LO sl1 ++ LO sl2.
Proof.
  intros. unfold cat, list_of_strl. now rewrite map_app, concat_app.
Qed.
Lemma lo_sub:
  forall sl i n, LO (sub sl i n) = firstn (to_nat n) (skipn (to_nat i) (LO sl)).
Proof.
  unfold list_of_strl. induction sl; intros; simpl.
    destruct eqb; now rewrite skipn_nil, firstn_nil.
    destruct eqb eqn:EQ.
      apply eqb_correct in EQ. now rewrite EQ.
      destruct ltb eqn:LT.
      - simpl. rewrite IHsl, skipn_app, firstn_app.
        f_equal. apply sub_spec.
        f_equal. rewrite length_spec_int, sub_spec, length_firstn, length_skipn. lia.
        f_equal. rewrite <-length_spec. lia.
      - rewrite IHsl, skipn_app.
        f_equal. rewrite (skipn_all2 (to_list a)), app_nil_l.
        f_equal. rewrite <-length_spec. lia.
        rewrite <-length_spec. lia.
Qed.
Lemma lo_drop:
  forall sl n, LO (drop sl n) = skipn (to_nat n) (LO sl).
Proof.
  unfold list_of_strl. induction sl; intros; simpl.
    destruct eqb; now rewrite skipn_nil.
    destruct eqb eqn:EQ.
      apply eqb_correct in EQ. now rewrite EQ.
      destruct ltb eqn:LT.
      - simpl. rewrite sub_spec, firstn_all2, skipn_app, <-length_spec.
        now replace (_ - _)%nat with O by lia.
        rewrite length_skipn, <-length_spec. lia.
      - rewrite IHsl, skipn_app, <-length_spec, (skipn_all2 (to_list a)).
        simpl. f_equal. lia.
        rewrite <-length_spec. lia.
Qed.
Lemma fold_add:
  forall l n, fold_left add l n = fold_left add l 0 + n.
Proof.
  induction l. simpl. lia. simpl. intro. rewrite IHl, (IHl (0+a)). lia.
Qed.
Lemma lo_length:
  forall sl, length sl = of_nat (List.length (LO sl)).
Proof.
  intros. unfold list_of_strl.
  induction sl. easy.
  unfold length in *. simpl. rewrite fold_add.
  rewrite IHsl. rewrite length_app. rewrite <-length_spec. lia.
Qed.
Lemma lo_splice:
  forall sl1 i sl2,
    LO (splice sl1 i sl2) =
    firstn (to_nat i) (LO sl1)++LO sl2++skipn (to_nat (i + length sl2)) (LO sl1).
Proof.
  intros. unfold splice.
  now rewrite !lo_cat, !lo_sub, lo_drop, skipn_O, app_assoc.
Qed.

Lemma equiv_get:
  forall sl1 sl2 i, sl1 ≡ sl2 -> get sl1 i = get sl2 i.
Proof.
  intros. now rewrite !lo_get, H.
Qed.
Lemma sub_equiv_get:
  forall sl1 sl2 i j, sub sl1 i j ≡ sub sl2 i j ->
  (to_Z i + to_Z j < wB)%Z ->
  forall k, k <? j = true ->
  get sl1 (i+k) = get sl2 (i+k).
Proof.
  intros. rewrite !lo_get. rewrite !lo_sub in H.
  replace (to_nat _) with (to_nat i + to_nat k)%nat by lia.
  rewrite <-!nth_skipn.
  apply (f_equal (λ l, nth (to_nat k) l 0)) in H.
  rewrite !nth_firstn in H.
  now replace _ with true in H by lia.
Qed.
Definition get_before:
  forall sl i j, i <? j = true -> get sl i = get (sub sl 0 j) i.
Proof.
  intros. replace i with (0 + i). erewrite sub_equiv_get. easy.
  now rewrite !lo_sub, !skipn_O, firstn_firstn, Nat.min_id.
  all: lia.
Qed.
Definition get_sub:
  forall sl i j k, k <=? i = true -> i - k <? j = true -> get sl i = get (sub sl k j) (i - k).
Proof.
  intros. rewrite !lo_get, lo_sub.
  rewrite nth_firstn. replace (_ <? _)%nat with true by lia.
  rewrite nth_skipn. f_equal. lia.
Qed.
Lemma splice_before:
  forall sl1 sl2 i j, i <=? length sl1 = true -> i <=? j = true ->
  sub (splice sl1 j sl2) 0 i ≡ sub sl1 0 i.
Proof.
  intros. unfold splice.
  rewrite !lo_sub, !lo_cat, !lo_sub, !skipn_O, <-app_assoc.
  rewrite firstn_app, length_firstn, firstn_firstn.
  replace (_ - _)%nat with O by (rewrite lo_length in H; lia).
  rewrite firstn_O, app_nil_r. f_equal. lia.
Qed.
Lemma sub_splice:
  forall sl1 sl2 i j,
    i <? length sl1 = true ->
    to_Z j = Zlength (LO sl2) ->
    sub (splice sl1 i sl2) i j ≡ sl2.
Proof.
  intros. rewrite lo_sub, lo_splice.
  rewrite skipn_app, length_firstn, skipn_firstn_comm, Nat.sub_diag, firstn_O, app_nil_l.
  rewrite lo_length in H. replace (_-_)%nat with O by lia.
  rewrite skipn_O, firstn_app. rewrite Zlength_correct in H0.
  replace (_-_)%nat with O by lia. rewrite firstn_O, app_nil_r, firstn_all2.
  easy. lia.
Qed.

Lemma equiv_sub:
  forall sl1 sl2 i j, sl1 ≡ sl2 -> sub sl1 i j ≡ sub sl2 i j.
Proof.
  intros. now rewrite !lo_sub, H.
Qed.
Lemma cat_splice:
  forall sl1 sl2 sl3 i, i + length sl2 <? length sl1 = true ->
  (to_Z i + Zlength (LO sl2) < wB)%Z ->
  cat (splice sl1 i sl2) sl3 ≡ splice (cat sl1 sl3) i sl2.
Proof.
  intros. rewrite lo_cat, !lo_splice, lo_cat, <-!app_assoc.
  rewrite Zlength_correct in H0.
  f_equal. rewrite firstn_app. rewrite !lo_length in H. replace (_ - _)%nat with O. now rewrite app_nil_r. lia.
  rewrite skipn_app. replace (_ - _)%nat with O. easy.
  rewrite !lo_length in *. lia.
Qed.
Lemma sub_cat:
  forall sl1 sl2 i j, i+j <? length sl1 = true ->
  (to_Z i + to_Z j < wB)%Z ->
  sub (cat sl1 sl2) i j ≡ sub sl1 i j.
Proof.
  intros. rewrite !lo_sub, lo_cat.
  rewrite skipn_app, firstn_app.
  replace (_ - _)%nat with O.
  now rewrite firstn_O, app_nil_r.
  rewrite length_skipn. rewrite lo_length in H. lia.
Qed.
Lemma sub_cat1:
  forall sl1 sl2 i j,
  (to_Z i + to_Z j <= Zlength (LO sl1))%Z ->
  sub (cat sl1 sl2) i j ≡ sub sl1 i j.
Proof.
  intros. rewrite !lo_sub, lo_cat.
  rewrite skipn_app, firstn_app.
  replace (_ - _)%nat with O.
  now rewrite firstn_O, app_nil_r.
  rewrite length_skipn. rewrite Zlength_correct in H. lia.
Qed.
Lemma sub_cat2:
  forall sl1 sl2 i j,
  (Zlength (LO sl1) <= to_Z i)%Z ->
  sub (cat sl1 sl2) i j ≡ sub sl2 (i - length sl1) j.
Proof.
  intros. rewrite !lo_sub, lo_cat.
  rewrite Zlength_correct in H.
  rewrite skipn_app, skipn_all2, app_nil_l by lia.
  repeat f_equal. rewrite lo_length. lia.
Qed.
Lemma slltl:
  forall sl n, llt sl n = true <-> (Zlength (LO sl) < to_Z n)%Z.
Proof.
  setoid_rewrite Zlength_correct.
  induction sl; intros; simpl.
    destruct eqb eqn:E; lia.
    destruct eqb eqn:E. lia.
      unfold list_of_strl in *.
      rewrite map_cons, concat_cons, length_app, <-length_spec.
      destruct ltb eqn:L. lia.
        split; intro.
          apply IHsl in H. lia.
          apply IHsl. lia.
Qed.
Lemma length_splice:
  forall sl1 i sl2, i + length sl2 <? length sl1 = true ->
  (to_Z i + Zlength (LO sl2) < wB)%Z ->
  length (splice sl1 i sl2) = length sl1.
Proof.
  intros. rewrite Zlength_correct, !lo_length in *.
  rewrite lo_splice, !length_app, length_firstn, length_skipn, !lo_length in *. lia.
Qed.
Lemma length_splice':
  forall sl1 i sl2, i + length sl2 <? length sl1 = true ->
  (to_Z i + Zlength (LO sl2) < wB)%Z ->
  List.length (LO (splice sl1 i sl2)) = List.length (LO sl1).
Proof.
  intros. rewrite Zlength_correct, !lo_length in *.
  rewrite lo_splice, !length_app, length_firstn, length_skipn, !lo_length in *. lia.
Qed.
Lemma equiv_trans:
  forall sl1 sl2 sl3, sl1 ≡ sl2 -> sl2 ≡ sl3 -> sl1 ≡ sl3.
Proof. intros. now rewrite H. Qed.
