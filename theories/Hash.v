From Kotori Require Import Util.
From Kotori Require Asm.
From Stdlib Require Import ZArith Orders Lia ZifyUint63 MSetRBT.
Import ListNotations.

Section Hashing.
  Variant hash :=
    | H_UBFX (lsb width: int)
    | H_EOR_UBFX (shift lsb width: int).
  Definition hash_size h :=
    match h with
    | H_UBFX _ width
    | H_EOR_UBFX _ _ width =>
        1 << width
    end.
  Definition hash_func h v :=
    match h with
    | H_UBFX lsb width => (v >> lsb) mod (1 << width)
    | H_EOR_UBFX shift lsb width => ((v lxor (v >> shift)) >> lsb) mod (1 << width)
    end.
  Fixpoint _valid_hash h D D' s :=
    match D, D' with
    | i::t, i'::t' =>
        let k1 := hash_func h (i<<2) in
        let k2 := hash_func h (i'<<2) in
        if (MSet.mem k1 s) || (MSet.mem k2 s)
        then false
        else let s' := MSet.add k2 (MSet.add k1 s) in
             _valid_hash h t t' s'
    | _, _ => true
    end.
  Section find_valid.
    Variable max : int.
    Function find_valid (f: int -> bool) x {measure (λ x, to_nat (max - x)) x} :=
      if (x <? max) then
        if (f x) then Some x else find_valid f (x+1)
      else None.
    Proof. lia. Defined.
  End find_valid.
  Section f. Variable l : int.
  Definition valid_hash h D D' s := if hash_size h <? l then false else _valid_hash h D D' s.
  Definition find_ubfx_lsb width D D' := find_valid 32 (λ lsb, valid_hash (H_UBFX lsb width) D D' MSet.empty) 0.
  Definition find_ubfx_width D D' := find_valid 12 (λ width, find_ubfx_lsb width D D') 3.
  Definition find_eorubfx_lsb shift width D D' := find_valid 32 (λ lsb, valid_hash (H_EOR_UBFX shift lsb width) D D' MSet.empty) 0.
  Definition find_eorubfx_shift width D D' := find_valid 32 (λ shift, find_eorubfx_lsb shift width D D') 1.
  Definition find_eorubfx_width D D' := find_valid 30 (λ width, find_eorubfx_shift width D D') 8.
  Definition find_ubfx D D' :=
    width ← find_ubfx_width D D';
    lsb ← find_ubfx_lsb width D D';
    return H_UBFX lsb width.
  Definition find_eorubfx D D' :=
    width ← find_eorubfx_width D D';
    shift ← find_eorubfx_shift width D D';
    lsb ← find_eorubfx_lsb shift width D D';
    return H_EOR_UBFX shift lsb width.
  End f.
  Definition find_hash D D' :=
    let l := len D in
    let l := l + l>>1 in
    match find_ubfx l D D' with
    | Some h => Some h
    | _ => find_eorubfx l D D'
    end.
End Hashing.

Section Table.
  Definition compute_table_m h ai D D' :=
    let m := fold_left (λ m p,
      let a := p.1<<2 in
      let a' := p.2<<2 in
      iimap_insert (hash_func h a) a'
      (iimap_insert (hash_func h a') a' m)
    ) (combine D D') (iimap_empty (hash_size h)) in
    map_single (fun n => iimap_lookup n m orelse (ai<<2)) (iseq (hash_size h) []).
End Table.
