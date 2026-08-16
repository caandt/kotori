From Coq Require Import PString ZArith.
From Rewriter Require Import proof.Util Strl ELF.
From Rewriter.proof Require Import I2N Strl.
From coqutil Require Import prove_Zeq_bitwise.
Import SL.

Definition u8_equiv : forall {s s' i} (E: s ≡ s'), getu8 s i = getu8 s' i := equiv_get.
Definition u16_equiv : forall {s s' i} (E: s ≡ s'), getu16 s i = getu16 s' i.
Proof. intros. unfold getu16. now rewrite !(u8_equiv E). Qed.
Definition u32_equiv : forall {s s' i} (E: s ≡ s'), getu32 s i = getu32 s' i.
Proof. intros. unfold getu32. now rewrite !(u16_equiv E). Qed.
Definition u64_equiv : forall {s s' i} (E: s ≡ s'), getu64 s i = getu64 s' i.
Proof. intros. unfold getu64. now rewrite (u8_equiv E), !(u32_equiv E). Qed.
Definition u8_before : forall s i j (J: i <? j = true), getu8 s i = getu8 (sub s 0 j) i := get_before.
Definition u16_before : forall s i j (I: (to_Z i < wB - 1)%Z) (J: i + 1 <? j = true), getu16 s i = getu16 (sub s 0 j) i.
Proof. intros. unfold getu16. now rewrite (u8_before s i j), (u8_before s (i+1) j) by lia. Qed.
Definition u32_before : forall s i j (I: (to_Z i < wB - 3)%Z) (J: i + 3 <? j = true), getu32 s i = getu32 (sub s 0 j) i.
Proof. intros. unfold getu32. now rewrite (u16_before s i j), (u16_before s (i+2) j) by lia. Qed.

Definition u64_before : forall s i j (I: (to_Z i < wB - 7)%Z) (J: i + 7 <? j = true), getu64 s i = getu64 (sub s 0 j) i.
Proof. intros. unfold getu64. now rewrite (u32_before s i j), (u32_before s (i+4) j), (u8_before s (i+7) j) by lia. Qed.

Lemma range_len:
  forall step i n, List.length (range step i n) = to_nat n.
Proof.
  intros. apply range_ind; intros. simpl. lia. simpl. rewrite H. lia.
Qed.
Lemma findn_bound:
  forall A f l n m, findn f l m = Some n -> to_nat n < to_nat m + @List.length A l.
Proof.
  induction l; simpl; intros.
    easy.
    destruct f.
      injection H. lia.
      apply IHl in H. lia.
Qed.
Lemma replaceable_seg_bound:
  forall phdrs n, replaceable_seg phdrs = Some n -> to_nat n < List.length phdrs.
Proof.
  intros. unfold replaceable_seg in H. destruct findn eqn:E.
    apply findn_bound in E. injection H. lia.
    now apply findn_bound in H.
Qed.
Lemma landland:
  forall a b, a land b land b = a land b.
Proof. zify. apply Z.bits_inj. intro. rewrite !Z.land_spec. lia. Qed.
Lemma phdr_data_len:
  forall p, List.length (LO (phdr_data p)) = 56%nat.
Proof.
  intros. unfold list_of_strl, phdr_data.
  cbv [map]. rewrite !to_of_list.
  all: easy || unfold u64, u32, u16, u8, char63_valid; repeat constructor.
  all: now rewrite landland.
Qed.
Lemma addl: forall i j, i <? i + j = true -> (to_Z i + to_Z j < wB)%Z. Proof. lia. Qed.
Lemma add_0_int: forall i, i = 0 + i. Proof. lia. Qed.

Lemma parse_elf_data:
  forall {bin elf} (E: parse_elf bin = Some elf),
    data elf = bin.
Proof.
  intros. repeat so E. now subst.
Qed.
Lemma eident_same {bin eident bin'}
  (E: parse_eident bin = Some eident)
  (S: sub bin 0 64 ≡ sub bin' 0 64):
  parse_eident bin' = Some eident.
Proof.
  unfold parse_eident in *.
  repeat so E. repeat sog; subst;
  f_equal; unfold getu32, getu16; simpl;
    repeat match goal with
           | |- context [getu8 _ ?A] =>
               lazymatch A with
               | 0 + _ => fail
               | _ => rewrite (add_0_int A)
               end
           end;
    rewrite !(sub_equiv_get bin' bin 0 64); auto; lia.
Qed.
Lemma ehdr_same {bin ehdr bin'}
  (E: parse_ehdr bin = Some ehdr)
  (S: sub bin 0 64 ≡ sub bin' 0 64):
  parse_ehdr bin' = Some ehdr.
Proof.
  unfold parse_ehdr in *.
  repeat so E. rewrite <-E. rewrite (eident_same H S). repeat sog;
  f_equal; unfold getu64, getu32, getu16; simpl;
    repeat match goal with
           | |- context [getu8 _ ?A] =>
               lazymatch A with
               | 0 + _ => fail
               | _ => rewrite (add_0_int A)
               end
           end;
    try (rewrite !(sub_equiv_get bin' bin 0 64); auto); lia.
Qed.
Lemma maybe_map_len:
  forall A B (f: A -> option B) l l', maybe_map f l = Some l' -> List.length l' = List.length l.
Proof.
  intros. unfold maybe_map, mapfold in H.
  generalize l l' H. clear. induction l; intros. now inversion H.
  repeat so H. apply IHl in H1. subst. simpl. lia.
Qed.
Lemma phdr_len:
  forall s ehdr p, parse_phdr s ehdr = Some p -> List.length p = to_nat ehdr.(e_phnum).
Proof.
  intros. do 2 so H. apply maybe_map_len in H. unfold phdr_offsets in H. now rewrite range_len in H.
Qed.

Variant IsPhoff (data: list string) : int -> Prop :=
  | isphoff i (I: getu64 data 32 = Some i) : IsPhoff data i.
Variant IsPhnum (data: list string) : int -> Prop :=
  | isphnum i (I: getu16 data 56 = i) : IsPhnum data i.
Variant IsPhdr (data: list string) : list string -> Prop :=
  | isphdr phoff phnum i p
      (O: IsPhoff data phoff)
      (N: IsPhnum data phnum)
      (I: i <? phnum = true)
      (P: sub data (phoff + 56 * i) 56 ≡ p) : IsPhdr data p.
Variant IsLoad (seg: list string) : Prop :=
  | isload (S: getu32 seg 0 = PT_LOAD).
Variant IsRX (seg: list string) : Prop :=
  | isrx (S: getu32 seg 4 = PF_RX).
Variant HasOffset (seg: list string) : int -> Prop :=
  | hasoffset offset (S: getu64 seg 8 = Some offset) : HasOffset seg offset.
Variant IsAt (seg: list string) : int -> Prop :=
  | isat vaddr (S: getu64 seg 16 = Some vaddr) : IsAt seg vaddr.
Variant HasSize (seg: list string) : int -> Prop :=
  | haslength filesz (S: getu64 seg 32 = Some filesz) : HasSize seg filesz.
Variant HasContent (data: list string) (seg: list string) : list string -> Prop :=
  | hascontent content offset vaddr filesz
      (S: IsPhdr data seg)
      (O: HasOffset seg offset)
      (V: IsAt seg vaddr)
      (F: HasSize seg filesz)
      (C: sub data offset filesz ≡ content) : HasContent data seg content.

Lemma getu8_bound:
  forall sl i, getu8 sl i <? 256 = true.
Proof.
  induction sl. easy. intros. simpl. destruct (ltb i). pose proof (get_char63_valid a i).
  unfold char63_valid in H. zify. change 255%Z with (Z.ones 8) in H. rewrite Z.land_ones in H. lia. lia.
  easy.
Qed.
Lemma getu16_bound:
  forall sl i, getu16 sl i <? 0x10000 = true.
Proof.
  unfold getu16. intros. pose (getu8_bound sl i). pose (getu8_bound sl (i+1)). lia.
Qed.
Lemma getu64_sub:
  forall sl i, (to_Z i + 8 <= wB)%Z -> getu64 sl i = getu64 (sub sl i 8) 0.
Proof.
  intros. unfold getu64, getu32, getu16.
  rewrite <-!add_assoc. simpl.
  repeat match goal with |- context [getu8 sl (i + ?k)] => rewrite (get_sub sl (i + k) 8 (i)) end.
  rewrite (get_sub sl i 8 i).
  all: try lia.
  remember (negb _). remember (negb _) in |-*. replace b0 with b. destruct b. simpl.
  repeat f_equal; lia. easy. subst. repeat f_equal. lia.
Qed.
Lemma getu64_equiv:
  forall sl sl2 i, sl ≡ sl2 -> getu64 sl i = getu64 sl2 i.
Proof.
  intros. unfold getu64, getu32, getu16. now rewrite !(equiv_get _ _ _ H).
Qed.
Lemma makeu8:
  forall a, of_list (u8 a) = make 1 a.
Proof.
  intros. simpl. apply to_list_inj. now rewrite cat_spec, !make_spec, landland.
Qed.
Lemma getu8_u8:
  forall a, getu8 [of_list (u8 a)] 0 = a land 255.
Proof.
  intros. cbv.
  now rewrite get_spec, length_spec_int, !cat_spec, make_spec, landland.
Qed.
Lemma byte: forall i mask s, ((i >> s) land mask) << s = i land (mask << s).
Proof.
  intros. izify.
  unfold wB. rewrite <-!Z.land_ones by lia.
  prove_Zeq_bitwise. repeat f_equal. lia.
Qed.
Lemma lsl_add: forall a b s, (a + b) << s = a << s + b << s.
Proof.
  intros. izify. rewrite !Z.shiftl_mul_pow2 by lia. lia.
Qed.
Lemma lsr_lsr: forall a b c, (to_Z b + to_Z c < wB)%Z -> a >> b >> c = a >> (b + c).
Proof.
  intros. izify. unfold wB. rewrite Z.mod_small by lia.
  prove_Zeq_bitwise.
Qed.

Lemma add_lor: forall a b, a land b = 0 -> a + b = a lor b.
Proof.
  intros. izify. apply eq_int_inj in H. rewrite I2N.I2Z.inj_land in H.
  rewrite <-BitOps.or_to_plus by lia. unfold wB. rewrite <-Z.land_ones by lia.
  rewrite Z.land_lor_distr_l. f_equal; rewrite Z.land_ones; lia.
Qed.
Lemma land2: forall a b c, (a land b) land (a land c) = a land (b land c).
Proof. intros. now rewrite !landA, (landC a b), landland. Qed.
Lemma lan: forall a b c d, (a land b) land (c land d) = (a land c) land (b land d).
Proof. intros. izify. prove_Zeq_bitwise. Qed.
Lemma getu64_u64:
  forall a, getu64 [of_list (u64 a)] 0 = Some a.
Proof.
  intros. unfold getu64, getu32, getu16, getu8.
  remember (S.length _). simpl in Heqi.
  rewrite length_spec_int in Heqi.
  rewrite !cat_spec, !make_spec in Heqi. simpl in Heqi. cbv in Heqi.
  subst i. cbv[ add ltb].
  simpl.
  rewrite !get_spec, !cat_spec_valid_length, !make_spec by (rewrite ?cat_length_spec, !make_length_spec; cbn; lia).
  repeat match goal with |- context[Nat.min ?a _] => replace (Nat.min a _) with a by lia end.
  simpl. rewrite !landland. sog. sog.
  2: now rewrite land_spec, andb_true_r, !bit_lsr, bit_M by lia.
  rewrite !byte. rewrite !lsl_add, !byte.
  rewrite !add_assoc.
  Ltac a := izify; unfold wB; rewrite <-!Z.land_ones by lia; change_ones; prove_Zeq_bitwise.
  rewrite (add_lor (_ land _)) by a.
  replace (_ lor _) with (a land 0xffff) by a.
  rewrite (add_lor (_ land _)) by a.
  replace (_ lor _) with (a land 0xffffff) by a.
  rewrite (add_lor (_ land _)) by a.
  replace (_ lor _) with (a land 0xffffffff) by a.
  rewrite (add_lor (_ land _)) by a.
  replace (_ lor _) with (a land 0xffffffffff) by a.
  rewrite (add_lor (_ land _)) by a.
  replace (_ lor _) with (a land 0xffffffffffff) by a.
  rewrite (add_lor (_ land _)) by a.
  replace (_ lor _) with (a land 0xffffffffffffff) by a.
  rewrite (add_lor (_ land _)) by a.
  replace (_ lor _) with (a land 0x7fffffffffffffff) by a.
  izify. change_ones. rewrite Z.land_ones; lia.
Qed.
Theorem add_code_correct:
  forall bin bin' content addr
    (B: add_code bin content addr = Some bin'),
  exists seg,
    IsPhdr bin' seg /\
    IsLoad seg /\
    IsRX seg /\
    IsAt seg addr /\
    HasContent bin' seg content.
Proof.
  intros. repeat so B. repeat so H0.
  remember (phdr_data _). exists l.
  repeat so H. repeat so H2.
  rename x4 into eident, x5 into entry, x6 into phoff, x7 into shoff, x1 into idx, x2 into ehdr, x into elf, x3 into phdrs;
    move entry after elf; move phoff after elf;
    move shoff after elf; move idx after elf.
  rename H4 into Beident, H5 into Bentry, H6 into Bphoff, H7 into Bshoff; move Bshoff after Heqb1.
  subst elf x0 ehdr. simpl in *.
  rename Heqb into Maxlen, Heqb0 into LenContent, Heqb2 into MinLen, Heqb3 into PhoffGT, Heqb4 into PhentSize, Heqb5 into NoOverflow, H1 into Idx.
  rename l into phdr, Heql into PHDR. move eident after addr; move phdrs after addr; move phdr after addr.
  rename Heqb1 into IdxInBound.
  apply replaceable_seg_bound in Idx. apply phdr_len in H3; simpl in H3.
  assert (PH: phoff + 56 * idx <? length bin = true) by (pose proof (getu16_bound bin 56); lia).
  assert (IsPhdr bin' phdr).
  {
    assert (SameEhdr: sub bin' 0 64 ≡ sub bin 0 64). {
      subst bin'.
      pose proof (getu16_bound bin 56).
      rewrite lo_length in MinLen.
      rewrite !sub_cat1 by (rewrite Zlength_correct, ?lo_cat, !lo_splice, !length_app, length_firstn; lia).
      now rewrite splice_before by lia. }
    econstructor.
    + constructor. erewrite (u64_before _ _ 64), u64_equiv, <-(u64_before _ _ 64), Bphoff; lia || auto.
    + constructor. erewrite (u16_before _ _ 64), u16_equiv, <-(u16_before _ _ 64); lia || auto.
    + assert (idx <? getu16 bin 56 = true) by lia. erewrite (u16_before _ _ 64), u16_equiv, <-(u16_before _ _ 64); [apply H | lia || auto ..].
    + rewrite lo_length in PH.
      rewrite B, !sub_cat1 by (subst; rewrite Zlength_correct, ?lo_cat, lo_splice, !length_app, length_firstn, phdr_data_len; lia).
      rewrite <-lo_length in PH.
      rewrite sub_splice; subst; now try rewrite Zlength_correct, phdr_data_len.
  }
  Ltac sub_phdr := rewrite lo_sub; unfold list_of_strl, phdr_data; cbv[map]; rewrite !to_of_list;
    easy || unfold u64, u32, u16, u8, char63_valid; repeat constructor;
    try now rewrite landland.
  assert (getu64 phdr 16 = Some addr).
  { rewrite getu64_sub by lia.
    rewrite (getu64_equiv _ (of_list (u64 addr)::nil)).
    apply getu64_u64.
    subst phdr. sub_phdr.
  }
  repeat split. 1-4: now subst.
  eapply (hascontent _ _ _ _ addr (length content)). easy.
  1-3: constructor; rewrite getu64_sub by lia;
    erewrite (getu64_equiv _ (of_list (u64 _)::nil));
    [apply getu64_u64 | subst phdr; sub_phdr].
  subst. simpl.
  remember (padding _ _) as pad; remember (cat (splice _ _ _) _) as padded.
  assert (List.length (LO padded) = List.length (LO bin) + to_nat pad)%nat.
    subst padded. rewrite !lo_length, lo_cat, length_app, length_splice'.
    setoid_rewrite length_concat at 2. simpl. rewrite <-length_spec, make_length_spec. clear; lia.
    subst. unfold padding. simpl. izify. change_ones. clear; rewrite Z.land_ones; lia.
    rewrite lo_length, phdr_data_len. clear -IdxInBound; lia.
    rewrite Zlength_correct, phdr_data_len. pose proof (getu16_bound bin 56); lia.
  rewrite sub_cat2.
  replace (_-_) with 0. rewrite lo_sub, skipn_O, firstn_all2. easy. apply slltl in LenContent. rewrite Zlength_correct in LenContent. rewrite lo_length. lia.
  rewrite !lo_length. lia. rewrite lo_length, Zlength_correct, H1.
  izify. rewrite of_Z_spec, Z.add_mod_idemp_l, Z.mod_small. lia. split. lia.
  apply slltl in Maxlen. rewrite Zlength_correct in Maxlen. enough (pad <? 0x1000 = true). lia.
  subst pad. unfold padding. simpl. izify. change_ones. clear; rewrite Z.land_ones; lia. lia.
Qed.
