From Kotori Require Export Util.
From Stdlib Require Import ZArith.
Global Set Printing Projections.

Ltac unfold_first x H :=
  match x with
  | ?a _ => unfold_first a H
  | _ => unfold x in H; simpl in H
  end.
Ltac so H :=
  match type of H with
  | (assert _; _) = Some _ =>
      let A := fresh "A" in
      let B := fresh "B" in
      apply bind_Some in H as (A&B&H);
      destruct (_:bool) eqn:? in B; [|discriminate]; clear A B
  | _ ≫= _ = Some _ => apply bind_Some in H as (?&?&H)
  | _ <&> _ = Some _ => apply fmap_Some in H as (?&?&H)
  | (return _) = Some _ => injection H as H
  | Some _ = Some _ => injection H as H
  | (?a = Some _) => unfold_first a H
  | (match ?a with _ => _ end = Some _) => destruct a eqn:?oe; try easy
  end.
Ltac sog :=
  match goal with
  | |- (assert ?E; _) = Some _ => replace E with true; simpl
  | |- (return _) = Some _ => f_equal
  | |- (?E <&> _) = Some _ =>
      let H := fresh "H" in eenough (E = Some _) as H; rewrite ?H; simpl
  | |- (?E ≫= _) = Some _ =>
      let H := fresh "H" in eenough (E = Some _) as H; rewrite ?H; simpl
  end.

Ltac hintro H :=
  match type of H with
  | ?A -> ?B => let x := fresh "X" in enough A as x; [specialize (H x)| clear H]
  end.
Ltac hintros H :=
  repeat hintro H.
Ltac subst' H := rewrite H in *; clear H.
Ltac subst'' H := rewrite <-H in *; clear H.
Ltac eqapply H := eapply ZifyClasses.eq_iff;[|exact H];repeat f_equal.
(* Ltac splitif := *)
(*   match goal with *)
(*     |- context[if ?a then _ else _] => destruct a eqn:?IF *)
(*   end. *)
(* Tactic Notation "splitif" "in" constr(H) := *)
(*   match type of H with *)
(*     context[if ?a then _ else _] => destruct a eqn:?IF *)
(*   end. *)
Ltac tif := match goal with |- context[if ?a then _ else _] => replace a with true;[|symmetry] end.
Tactic Notation "tif" "in" constr(H) := match type of H with context[if ?a then _ else _] => replace a with true in H;[|symmetry] end.
Ltac fif := match goal with |- context[if ?a then _ else _] => replace a with false;[|symmetry] end.
Tactic Notation "fif" "in" constr(H) := match type of H with context[if ?a then _ else _] => replace a with false in H;[|symmetry] end.

Ltac revertall := repeat match goal with H: _ |- _ => revert H end.
Lemma add_0_l: forall i, 0 + i = i. Proof. lia. Qed.
Lemma add_0_r: forall i, i + 0 = i. Proof. lia. Qed.
Lemma ifls: forall l a, fold_left add l a = a + fold_left add l 0.
Proof. induction l; intro; simpl. lia. rewrite IHl, (IHl (_ + _)). lia. Qed.
Lemma nfls: forall l a, fold_left N.add l a = N.add a (fold_left N.add l N0).
Proof. induction l; intro; simpl. lia. rewrite IHl, (IHl (N.add _ _)). lia. Qed.
Lemma isum_cons: ∀ t a, isum (a::t) = a + isum t.
Proof. unfold isum. intros. simpl. rewrite ifls. lia. Qed.
Definition nsum lst := List.fold_left N.add lst N0.
Lemma nsum_cons: ∀ t a, nsum (a::t) = (a + nsum t)%N.
Proof. unfold nsum. intros. simpl. rewrite nfls. lia. Qed.

Definition toNat x := to_nat x.
Definition ofNat x := of_nat x.
Notation "♮ x" := (toNat x) (at level 2, format "♮ x") : nat_scope.
Notation "♯ x" := (ofNat x) (at level 1, format "♯ x") : nat_scope.
#[refine]
Global Instance Op_toNat: ZifyClasses.UnOp toNat := { TUOp x := x }.
Proof.
  intros. setoid_rewrite Z2Nat.id.
    reflexivity.
    apply to_Z_bounded.
Defined.
#[refine]
Global Instance Op_ofNat: ZifyClasses.UnOp ofNat := { TUOp x := Z.modulo x 9223372036854775808 }.
Proof.
  intros. now setoid_rewrite of_Z_spec.
Defined.
Add Zify UnOp Op_toNat.
Add Zify UnOp Op_ofNat.
Definition toN x := Z.to_N (to_Z x).
Definition ofN x := of_Z (Z.of_N x).
#[refine]
Global Instance Op_toN: ZifyClasses.UnOp toN := { TUOp x := x }.
Proof.
  intros. setoid_rewrite Z2N.id.
    reflexivity.
    apply to_Z_bounded.
Defined.
#[refine]
Global Instance Op_ofN: ZifyClasses.UnOp ofN := { TUOp x := Z.modulo x 9223372036854775808 }.
Proof.
  intros. now setoid_rewrite of_Z_spec.
Defined.
Add Zify UnOp Op_toN.
Add Zify UnOp Op_ofN.
Notation "♮ x" := (toN x) : N_scope.
Notation "♯ x" := (ofN x) : N_scope.
Notation "♭ x" := (N.to_nat x) (at level 2, format "♭ x") : N_scope.
Notation "A ⇀ B" := (A → option B) (at level 100).
Lemma csum_def {lst sum n} : csum sum lst n = sum + isum (firstn ♮n lst).
Proof.
  revertall. induction lst; intros.
    rewrite firstn_nil. cbv. lia.
    simpl. case_match eqn:N.
      rewrite (eqb_correct n 0 N), firstn_O. cbv. lia.
      replace ♮n with (S ♮(n - 1)) by lia.
        rewrite IHlst, firstn_cons, isum_cons. lia.
Qed.

Lemma len_length:
  forall A l, @len A l = ♯(List.length l).
Proof.
  intros. unfold len. rewrite <-(add_0_r (ofNat _)).
  generalize 0.
  induction l. simpl. lia.
  intro. rewrite IHl. cbn. lia.
Qed.
Lemma len_cons {A} {a:A} {t} : len (a::t) = succ (len t).
Proof. rewrite !len_length. cbn. lia. Qed.
Lemma ith_nth_error:
  forall A l n, @ith A l n = nth_error l ♮n.
Proof.
  induction l; intro.
    now rewrite nth_error_nil.
    simpl. case_match.
      now replace ♮n with O by lia.
      now replace ♮n with (S ♮(n - 1)) by lia.
Qed.
