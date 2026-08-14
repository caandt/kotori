From Coq Require Import ZArith NArith Uint63 Lia ZifyUint63 ZifyN.
From Rewriter Require Import Util(xb,ones).
From Picinae Require Import theory.

Open Scope uint63.

Module notations.
  Notation toN a := (Z.to_N (to_Z a)).
  Notation ofN a := (of_Z (Z.of_N a)).
  Notation wN := (2 ^ N.of_nat size).
  Notation "% n" := (N.modulo n wN) (at level 1, format "% n") : N_scope.
  Notation "% z" := (Z.modulo z wB) (at level 1, format "% z") : Z_scope.
End notations.
Import notations.
Section I2N.
  Variable i j: int.
  Notation n := (toN i).
  Notation m := (toN j).

  Lemma id: ofN n = i. Proof. lia. Qed.
  Lemma inj: n = m -> i = j. Proof. lia. Qed.
  Lemma inj_iff: n = m <-> i = j. Proof. lia. Qed.
  Lemma inj_eqb: (n =? m)%N = (i =? j). Proof. lia. Qed.

  Lemma inj_add: toN (i + j) = %(n + m). Proof. lia. Qed.
  Lemma inj_sub: toN (i - j) = msub 63 n m.
  Proof.
    apply N2Z.inj. rewrite sub_spec, Z2N.id, N2Z_msub by lia. lia.
  Qed.
  Lemma inj_mul: toN (i * j) = %(n * m). Proof. lia. Qed.
  Lemma inj_mod: toN (i mod j) = (n mod m)%N.
  Proof. now rewrite mod_spec, Z2N.inj_mod by lia. Qed.

  Lemma inj_lsl: toN (i << j) = %(N.shiftl n m).
  Proof.
    now rewrite lsl_spec, N.shiftl_mul_pow2, Z2N.inj_mod, Z2N.inj_mul, Z2N.inj_pow by lia.
  Qed.
  Lemma inj_lsr: toN (i >> j) = N.shiftr n m.
  Proof.
    now rewrite lsr_spec, <-Z.shiftr_div_pow2, Z2N_inj_shiftr by lia.
  Qed.
  Lemma inj_land: toN (i land j) = N.land n m.
  Proof. now rewrite land_spec', Z2N_inj_land by lia. Qed.
  Lemma inj_lor: toN (i lor j) = N.lor n m.
  Proof. now rewrite lor_spec', Z2N_inj_lor by lia. Qed.
  Lemma inj_lxor: toN (i lxor j) = N.lxor n m.
  Proof. now rewrite lxor_spec', Z2N_inj_lxor by lia. Qed.
  Lemma inj_bit: bit i j = N.testbit n m.
  Proof. rewrite bitE, <-N2Z.inj_testbit. f_equal; lia. Qed.

  Lemma inj_compare: compare i j = N.compare n m.
  Proof. now rewrite compare_spec, Z2N.inj_compare by lia. Qed.
  Lemma inj_succ: toN (succ i) = %(N.succ n). Proof. lia. Qed.
  Lemma inj_pred: toN (pred i) = msub 63 n 1.
  Proof. apply N2Z.inj. rewrite pred_spec, Z2N.id, N2Z_msub by lia. lia. Qed.
  Lemma inj_min: toN (min i j) = N.min n m.
  Proof. rewrite min_spec. lia. Qed.
  Lemma inj_max: toN (max i j) = N.max n m.
  Proof. rewrite max_spec. lia. Qed.
  Lemma inj_lt: i <? j = true <-> n < m. Proof. lia. Qed.
  Lemma inj_le: i <=? j = true <-> n <= m. Proof. lia. Qed.
End I2N.
Lemma to_of_N : forall n, toN (ofN n) = %n.
Proof.
  intro. rewrite of_Z_spec, Z2N.inj_mod, N2Z.id; lia.
Qed.
Lemma mp2_pow2: forall a b, ((2 ^ a) mod (2 ^ b) = if a <? b then 2 ^ a else 0)%N.
Proof.
  intros. destruct N.ltb eqn:E.
    rewrite N.mod_small; try apply N.pow_lt_mono_r; lia.
    rewrite N.Lcm0.mod_divide. exists (2 ^ (a-b)).
      rewrite <-N.pow_add_r. f_equal. lia.
Qed.
Lemma inj_ones: forall i, toN (ones i) = %(N.ones (toN i)).
Proof.
  intros. unfold ones.
  rewrite inj_sub, inj_lsl. simpl.
  destruct %(_) eqn:N.
    rewrite msub_0_l_neg, N.ones_mod_pow2; auto.
    rewrite N.Lcm0.mod_divide, N.shiftl_mul_pow2, N.mul_1_l in N.
    apply N.divide_pos_le in N.
    now apply N.pow_le_mono_r_iff in N. lia.
    rewrite msub_sub, <-N by lia.
    rewrite N.ones_equiv, N.shiftl_mul_pow2, N.mul_1_l in *.
    rewrite (N.mod_small (2^_)). lia. rewrite mp2_pow2 in N.
    destruct N.ltb eqn:E. apply N.pow_lt_mono_r; lia. easy.
Qed.
Lemma inj_xb: forall n i w, toN (xb n i w) = xbits (toN n) (toN i) (toN i+toN w).
Proof.
  intros. unfold xb, xbits.
  rewrite N.add_sub_swap, N.sub_diag, N.add_0_l by lia.
  rewrite inj_land, inj_lsr, inj_ones.
  destruct (w<?63) eqn:E.
    rewrite N.mod_small, N.land_ones. easy.
    rewrite N.ones_equiv. etransitivity; [|apply (N.pow_lt_mono_r 2 (toN w))]; lia.
    rewrite N.ones_mod_pow2 by lia.
    rewrite N.land_ones. rewrite !N.mod_small;
    epose proof (N.shiftr_upper_bound (toN n) (toN i));
    epose proof (N.pow_le_mono_r 2 63 (toN w)); lia.
Qed.
Module I2Z. Section I2Z.
  Open Scope Z.
  Variable i j: int.
  Notation x := (to_Z i).
  Notation y := (to_Z j).

  Definition id := of_to_Z i.
  Definition inj := to_Z_inj i j.

  Definition inj_add := add_spec i j.
  Definition inj_sub := sub_spec i j.
  Definition inj_mul := mul_spec i j.
  Definition inj_mod := mod_spec i j.

  Lemma inj_lsl: to_Z (i << j) = %(Z.shiftl x y).
  Proof.
    now rewrite lsl_spec, Z.shiftl_mul_pow2 by lia.
  Qed.
  Lemma inj_lsr: to_Z (i >> j) = Z.shiftr x y.
  Proof.
    now rewrite lsr_spec, Z.shiftr_div_pow2 by lia.
  Qed.
  Definition inj_land := land_spec' i j.
  Definition inj_lor := lor_spec' i j.
  Definition inj_lxor := lxor_spec' i j.
  Definition inj_bit := bitE i j.

  Lemma inj_lt: (i <? j = true)%uint63 <-> x < y. Proof. lia. Qed.
  Lemma inj_le: (i <=? j = true)%uint63 <-> x <= y. Proof. lia. Qed.
End I2Z. End I2Z.

Ltac nify :=
  repeat match goal with
  | |- @eq int _ _ => apply inj
  | |- ?i <? ?j = true => apply inj_lt
  | |- ?i <=? ?j = true => apply inj_le
  | |- context[toN (?i + ?j)] => rewrite (inj_add i j)
  | |- context[toN (?i - ?j)] => rewrite (inj_sub i j)
  | |- context[toN (?i * ?j)] => rewrite (inj_mul i j)
  | |- context[toN (?i mod ?j)] => rewrite (inj_mod i j)
  | |- context[toN (?i << ?j)] => rewrite (inj_lsl i j)
  | |- context[toN (?i >> ?j)] => rewrite (inj_lsr i j)
  | |- context[toN (?i land ?j)] => rewrite (inj_land i j)
  | |- context[toN (?i lor ?j)] => rewrite (inj_lor i j)
  | |- context[toN (?i lxor ?j)] => rewrite (inj_lxor i j)
  | |- context[bit ?i ?j] => rewrite (inj_bit i j)
  | |- context[compare ?i ?j] => rewrite (inj_compare i j)
  end.
Ltac izify :=
  repeat match goal with
  | |- @eq int _ _ => apply I2Z.inj
  | |- ?i <? ?j = true => apply I2Z.inj_lt
  | |- ?i <=? ?j = true => apply I2Z.inj_le
  | |- context[to_Z (?i + ?j)] => rewrite (I2Z.inj_add i j)
  | |- context[to_Z (?i - ?j)] => rewrite (I2Z.inj_sub i j)
  | |- context[to_Z (?i * ?j)] => rewrite (I2Z.inj_mul i j)
  | |- context[to_Z (?i mod ?j)] => rewrite (I2Z.inj_mod i j)
  | |- context[to_Z (?i << ?j)] => rewrite (I2Z.inj_lsl i j)
  | |- context[to_Z (?i >> ?j)] => rewrite (I2Z.inj_lsr i j)
  | |- context[to_Z (?i land ?j)] => rewrite (I2Z.inj_land i j)
  | |- context[to_Z (?i lor ?j)] => rewrite (I2Z.inj_lor i j)
  | |- context[to_Z (?i lxor ?j)] => rewrite (I2Z.inj_lxor i j)
  | |- context[bit ?i ?j] => rewrite (I2Z.inj_bit i j)
  (* | |- context[compare ?i ?j] => rewrite (I2Z.inj_compare i j) *)
end.
Ltac change_ones :=
  let rec loop n :=
    match n with
    | O => change (to_Z 0) with Z0
    | S ?n' =>
      let z := eval compute in (Z.of_nat n) in
      let i := eval compute in (of_Z (Z.ones z)) in
      change (to_Z i) with (Z.ones z);
      loop n'
    end in
  loop 63%nat.
