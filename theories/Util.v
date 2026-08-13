Require Export Uint63 List Bool Recdef Lia ZifyUint63.
Require Import Orders MSetRBT ZArith.
From stdpp Require Import countable gmap.
From stdpp Require Export option.
Require PrimString.
Export PrimString.PStringNotations PrimString(string).
Open Scope uint63.

Definition xb (n i j: int) := (n >> i) land (1 << (j - i) - 1).
Notation "n :[ i , j ]" := (xb n i j) (at level 30, format "n :[ i ,  j ]").
Notation "n :[ b ]" := (xb n b%uint63 (b%uint63 + 1)) (at level 30, format "n :[ b ]").

Notation "m ≫= f" := (m ≫= f) (format "m  ≫=  '/' f").
Notation "m ≫= 'λ' x .. y f" := (m ≫= (fun x => .. (fun y => f) ..))
  (only printing, x binder, y binder,
   format "m  ≫=  'λ'  x  ..  y  '/' f",
   f at level 200, at level 60).
Notation "m <&> f" := (fmap f m) (at level 61, left associativity).
Notation "'return' x " := (mret x) (at level 60).
Definition asrt (x:bool) : option unit := if x then Some tt else None.
Notation "'assert' x ; f" := (_ ← asrt x; f) (at level 60, right associativity).
Notation "x 'orelse' y" := (default y x) (at level 10).
Definition issome {A} (x: option A) := if x then true else false.
Coercion issome : option >-> bool.

Fixpoint _mapi {A B} sz acc i f (l: list A) : list B :=
  match l with
  | nil => rev acc
  | a::t => _mapi sz (f i a::acc) (i+sz a) f t
  end.
Definition mapi {A B} := @_mapi A B (const 1) nil 0.
Definition mapisz {A B} sz := @_mapi A B sz nil 0.

Definition clearlow12 n := n land (max_int lxor 0xfff).
Definition maybe_op {A B C} (op: A -> B -> C) x y := x ≫= λ x, y ≫= λ y, Some (op x y).
Definition mapfold {A B C} op (f:A->B) l b : C := fold_right op b (map f l).
Definition maybe_map {A B} (f:A->option B) l := mapfold (maybe_op cons) f l (Some nil).

Definition len {A} (l:list A) := of_nat (List.length l).
Definition ith {A} (l:list A) n := List.nth_error l (to_nat n).
Extract Constant ith => "(fun l n -> List.nth_opt l (Uint63.to_int2 n |> snd))".

Function init n (x:int) {measure to_nat n} :=
  if (n =? 0) then nil else x::init (n-1) x.
Proof. lia. Defined.
Definition rpad l n x :=
  let len := len l in
  if len <? n then l ++ init (n - len) x else l.

Variant _letintoken := _letintokenIN | _letintokenEXTRACTION.
Definition _letin{A B} (a:A) (_:{x:_letintoken|x=_letintokenIN}) (b:A->B) (_:{x:_letintoken|x=_letintokenEXTRACTION}) := b a.
Notation "'let*' x := y 'in' z" :=
  (_letin y (exist _ _ eq_refl) (fun x => z) (exist _ _ eq_refl))
  (at level 200, x pattern, right associativity,
   format "'[v' 'let*'  x  :=  y  'in'  '/' z ']'").
Extract Inductive _letintoken => "" ["in" "_ROCQ_LET_IN_EXTRACTION"].
Extract Inlined Constant _letin => "let _ROCQ_LET_IN_EXTRACTION =".

Axiom print_endline : string -> unit.
Extract Constant print_endline => "(fun x -> print_endline (Pstring.to_string x))".
Axiom print_int : int -> unit.
Extract Constant print_int => "(fun x -> print_int (Int64.to_int (Uint63.to_int64 x)))".

Fixpoint csum sum lst n :=
  match lst with
  | nil => sum
  | a::t =>
      if n =? 0
      then sum
      else csum (a + sum) t (n - 1)
  end.
Extract Constant csum => "(fun sum lst ->
  let arr = Array.of_list lst in
  let n = Array.length arr in
  let table = Array.make n Uint63.zero in
  let acc = ref sum in
  for i = 0 to n - 1 do
    table.(i) <- !acc;
    acc := Uint63.add arr.(i) !acc
  done;
  fun x ->
    let i = x |> Uint63.to_int2 |> snd in
    if i < n then table.(i)
    else !acc
)".

Definition sext n w := asr (n << (63 - w)) (63 - w).
Definition padding x b := (1 << b - x land (1 << b - 1)) land (1 << b - 1).
Definition pad_to x b := x + padding x b.

(* copy of map, to avoid using parmap extraction *)
Fixpoint map_single {A B} (f:A->B) l :=
  match l with
  | nil => nil
  | a::t => f a::map_single f t
  end.

Global Instance int_eq_dec : EqDecision int.
Proof.
  intros x y. destruct (x =? y) eqn:E.
    left. now apply eqb_correct.
    right. now apply eqb_false_correct.
Defined.
Global Instance int_countable : Countable int.
Proof.
  constructor 1 with (Z.to_pos ∘ Z.succ ∘ to_Z) (Some ∘ of_Z ∘ Z.pred ∘ Zpos).
  simpl. intro. f_equal. now rewrite Z2Pos.id, Z.pred_succ, of_to_Z by apply Zle_lt_succ, to_Z_bounded.
Defined.

Definition iimap_empty : gmap.gmap int int := gmap.gmap_empty.
Definition iimap_lookup i (m: gmap.gmap int int) := lookup i m.
Function iseq n l {measure to_nat n} :=
  if (n =? 0) then l else iseq (n-1) (n-1::l).
Proof. lia. Defined.

Module IntOT <: UsualOrderedType.
  Definition t := int.
  Definition eq := @eq int.
  Definition eq_equiv := @eq_equivalence int.
  Definition lt x y := (x <? y = true).
  Definition lt_strorder : StrictOrder lt.
  Proof.
    unfold lt. split. intros x LT. lia.
    intros x y z LT LT2. lia.
  Defined.
  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
  Proof.
    intros a b EQ x y EQ2. unfold lt. subst. lia.
  Defined.
  Definition compare := Uint63.compare.
  Definition compare_spec : forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros x y. unfold compare, lt.
    rewrite Uint63.compare_spec.
    destruct (Z.compare_spec (to_Z x) (to_Z y)); constructor; auto; lia.
  Defined.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof. apply int_eq_dec. Defined.
End IntOT.
Module MSet := Make IntOT.
