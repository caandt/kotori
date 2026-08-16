From Rewriter Require Export Util.

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
      destruct (_:bool) eqn:? in B; try easy; clear A B
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

Ltac splitif :=
  match goal with
    |- context[if ?a then _ else _] => destruct a eqn:?IF
  end.
Tactic Notation "splitif" "in" constr(H) :=
  match type of H with
    context[if ?a then _ else _] => destruct a eqn:?IF
  end.

Global Set Printing Projections.
Ltac revertall := repeat match goal with H: _ |- _ => revert H end.
Lemma add_0_int: forall i, i = 0 + i. Proof. lia. Qed.
Lemma nsum_cons: ∀ t a, nsum (a::t) = a + nsum t.
Proof.
  unfold nsum. simpl. setoid_rewrite <-add_0_int.
  induction t; intros.
    cbv. lia.
    simpl. rewrite <-add_0_int, IHt, (IHt a). lia.
Qed.
Notation "! x" := (to_nat x) (at level 1, format "! x").
Notation "^ x" := (of_nat x) (at level 1, format "^ x").
Lemma csum_def {lst sum n} : csum sum lst n = sum + nsum (firstn !n lst).
Proof.
  revertall. induction lst; intros.
    rewrite firstn_nil. cbv. lia.
    simpl. splitif.
      rewrite (eqb_correct n 0 IF), firstn_O. cbv. lia.
      replace !n with (S !(n - 1)) by lia.
        rewrite IHlst, firstn_cons, nsum_cons. lia.
Qed.

Lemma len_cons {A} {a:A} {t} : len (a::t) = succ (len t).
Proof. unfold len. cbn. lia. Qed.
