From stdpp Require Import gmap.
Require Import Util.
Require Hash Decode Asm.
Import Decode(ityp(..),decode).
Import ListNotations.

Variant reloc :=
  | Rimm (i: int)
  | Raddr (i: int)
  | Rrt (i: int)
  | Rtbl (i: int).
Variant isize :=
  | Sz1
  | Sz2
  | Sz3.
Definition intsize sz :=
  match sz with
  | Sz1 => 1
  | Sz2 => 2
  | Sz3 => 3
  end.
Variant list3 :=
  | Lst0 : _
  | Lst1 : int -> _
  | Lst2 : int -> int -> _
  | Lst3 : int -> int -> int -> _.
Variant cinst :=
  | Inum (n: int)
  | Iimm (sz:isize) (r: int) (imm: reloc)
  | Ihsh (r lbl: int)
  | Ib   (sz:isize) (t: ityp) (d: reloc).
Definition instsize inst :=
  match inst with
  | Inum _ => 1
  | Ihsh _ _ => 2
  | Iimm sz _ _
  | Ib sz _ _ => intsize sz
  end.
Record chunk A := C {
  cn: int;
  ci: int;
  ct: ityp;
  cd: A;
}.
Notation chunklist A := (list (chunk A)).
Arguments cn {_}.
Arguments ci {_}.
Arguments ct {_}.
Arguments cd {_}.
Arguments C {_}.

Record args := {
  code: list int;
  pol: int → int;
  dsets: list (list int);
  bi: int;
  bi': int;
  nrelax: nat;
  rtlen: int;
  orig_lr: bool;
}.
Record data := {
  chunks: chunklist (list cinst);
  rel: int → int;
  ai: int;
  bti: int;
  tc: list (Hash.hash * list int * int);
  arg: args;
  rets: list int;
  devs: list int;
}.
Definition setd{A B} (c: chunk A) (d: B) := C c.(cn) c.(ci) c.(ct) (d).
Definition chunkmap{A B} (f: chunk A -> B) l := map (λ c, setd c (f c)) l.
Definition instmapi{A} := @_mapi _ A instsize [].
Definition chunkmapi{A} rel f := chunkmap (λ c, @instmapi A (rel c.(ci)) f c.(cd)).
Section ChunkGeneration.
  Variable a : args.
  Notation pol := a.(pol).
  Notation dsets := a.(dsets).
  Notation bi := a.(bi).
  Notation bi' := a.(bi').
  Definition stage1 := mapi (λ idx n, C n (bi + idx) (decode n) ()) a.(code).
  Section InstRewriter.
    Variable c : chunk ().
    Notation n := (c.(cn)).
    Notation i := (c.(ci)).
    Notation t := (c.(ct)).
    Notation lbl := (pol c.(ci)).
    Notation dset := (ith dsets lbl orelse []).
    Definition rw_indirect rn n :=
      match dset with
      | [] => [Ib Sz1 (BL 0) (Rrt 0)]
      | [d] => [Iimm Sz3 rn (Raddr d); Inum n]
      | _ =>
          let rtmp := b2i (is_zero rn) in
          [ Inum (Asm.PUSH2 rtmp 31)
          ; Ihsh rn lbl
          ; Iimm Sz2 rtmp (Rtbl lbl)
          ; Inum (Asm.LDR_r64 rn rtmp rn)
          ; Inum (Asm.POP2 rtmp 31)
          ; Inum n ]
      end.
    Definition rw_inst :=
      match t with
      | ignore => [Inum n]
      | invalid => [Ib Sz1 (BL 0) (Rrt 0)]
      | ADR imm rd => [Iimm Sz2 rd (Rimm ((i<<2)+sext imm 21))]
      | ADRP imm rd => [Iimm Sz3 rd (Rimm (clearlow12 (i<<2)+sext (imm<<12) 33))]
      | Bcond imm _ | CBZ _ _ imm _ => [Ib Sz2 t (Raddr (i+sext imm 19))]
      | B imm => [Ib Sz1 t (Raddr (i+sext imm 26))]
      | BL imm =>
          if a.(orig_lr) then
            [ Iimm Sz3 30 (Rimm ((i+1)<<2))
            ; Ib Sz1 (B imm) (Raddr (i+sext imm 26)) ]
          else
            [Ib Sz1 t (Raddr (i+sext imm 26))]
      | TBZ _ _ _ imm _ => [Ib Sz2 t (Raddr (i+sext imm 14))]
      | BR rn | RET rn => rw_indirect rn n
      | BLR rn =>
          if a.(orig_lr) then
            Iimm Sz3 30 (Rimm ((i+1)<<2))::
            rw_indirect rn (n lxor (1<<21))
          else
            rw_indirect rn n
      end.
  End InstRewriter.
  Definition stage2 := chunkmap rw_inst.
  Section Relaxation.
    Definition chunksize c := fold_left add (map_single instsize c.(cd)) 0.
    Definition makerel chunks :=
      let lens := map chunksize chunks in
      let csum := csum bi' lens in
      let rel x := csum (x - bi) in
      let ei := bi + len chunks in
      λ x, if (bi <=? x) && (x <=? ei)
           then rel x
           else x.
    Definition fits bw n := (lesb (-1<<(bw-1)) n) && (ltsb n (1<<(bw-1))).
    Definition relaxi rel i' inst :=
      match inst with
      | Iimm Sz1 _ _ => inst
      | Iimm _ r (Rimm imm) =>
          if (clearlow12 imm =? imm) && (fits 21 (asr imm 12-i'>>10)) then Iimm Sz1 r (Rimm imm)
          else if fits 21 (imm-i'<<2) then Iimm Sz1 r (Rimm imm)
          else if fits 21 (asr imm 12-i'>>10) then Iimm Sz2 r (Rimm imm)
          else if imm <? 1 << 32 then Iimm Sz2 r (Rimm imm)
          else inst
      | Ib Sz2 t (Raddr d) =>
          let bw := match t with
                    | Bcond _ _ | CBZ _ _ _ _ => 19
                    | TBZ _ _ _ _ _ => 14 | _ => 0 end in
          if fits bw (i'-rel d) then Ib Sz1 t (Raddr d)
          else inst
      | _ => inst
      end.
    Definition relax chunks :=
      let rel := makerel chunks in
      chunkmapi rel (relaxi rel) chunks.
  End Relaxation.
  Definition stage3 := Nat.iter a.(nrelax) relax.
  Definition compute_tables rel ai bti dsets :=
    maybe_map (λ D,
      let D' := map_single rel D in
      Hash.find_hash D D' <&> λ h,
      (h, Hash.compute_table_m h ai D D')
    ) dsets <&> λ l,
      rev (fst (fold_left (λ '(acc, ti) '(h, tbl),
        ((h, tbl, ti)::acc, ti + 2 * len tbl)
      ) l ([], bti))).
  Definition indirect_reg{A} c :=
    match c.(ct A) with
    | BR Rn | BLR Rn | RET Rn => Some Rn
    | _ => None
    end.
  Definition replace_indirect{A} f c :=
    (f c <$> indirect_reg c) orelse c.(cd A).
  Definition retlist{A} (chunks: chunklist A) :=
    map ci (filter (issome ∘ indirect_reg) chunks).
  Fixpoint deviations idx cum lens :=
    match lens with
    | nil => nil
    | size::t =>
        let dev := size - 1 in
        let next_cum_dev := cum + dev in
        if size =? 1 then deviations (idx+1) next_cum_dev t
        else idx::next_cum_dev::deviations (idx+1) next_cum_dev t
    end.
  Definition makedata chunks :=
    let rel := makerel chunks in
    let ai := pad_to (rel (bi + len a.(code))) 10 in
    let bti := pad_to (ai + a.(rtlen)>>2) 10 in
    let rets := retlist chunks in
    let devs := deviations 0 0 (map chunksize chunks) in
    tc ← compute_tables rel ai bti dsets;
    return {|
      arg := a; chunks := chunks; rel := rel;
      ai := ai; bti := bti; tc := tc;
      rets := rets; devs := devs;
    |}.
  Definition rw_hook hook := makedata (stage3 (hook (stage2 (stage1)))).
  Section PolHook.
    Fixpoint index{A} {eqd : EqDecision A} l x i :=
      match l with
      | nil => None
      | a::t => if eqd a x then Some i else index t x (succ i)
      end.
    Definition call_polhook{A} f c Rn :=
      [ Inum (Asm.PUSH2 Rn 30)
      ; Inum (Asm.PUSH2 16 17) ] ++ f c ++
      [ Ib Sz1 (BL 0) (Rrt 2)
      ; Inum (Asm.POP2 Rn (30 + (Rn =? 30)))
      ; Inum c.(cn A) ].
    Definition polhook chunks :=
      let rets := retlist chunks in
      let f c := [Iimm Sz2 16 (Rimm (index rets c.(ci) 0 orelse 0))] in
      chunkmap (replace_indirect (call_polhook f)) chunks.
    Definition polhook2 chunks :=
      chunkmap (replace_indirect (call_polhook (const nil))) chunks.
  End PolHook.
End ChunkGeneration.
Section InstSelection.
  Variable d : data.
  Notation ai := d.(ai).
  Notation tc := d.(tc).
  Notation rel := d.(rel).
  Definition resolve reloc :=
    match reloc with
    | Rimm i => i
    | Raddr i => rel i << 2
    | Rrt i => (ai + i) << 2
    | Rtbl i => ((snd <$> ith tc i) orelse 0) << 2
    end.
  Definition isel i' inst :=
    match inst with
    | Inum n => Lst1 n

    | Ihsh r lbl =>
        match (fst ∘ fst) <$> ith tc lbl with
        | Some (Hash.H_UBFX lsb width) =>
            Lst2 Asm.NOP (Asm.UBFX true r r lsb width)
        | Some (Hash.H_EOR_UBFX shift lsb width) =>
            Lst2 (Asm.EOR_lsr r r r shift) (Asm.UBFX true r r lsb width)
        | _ => Lst0
        end

    | Iimm Sz1 r reloc =>
        let imm := resolve reloc in
        let asm := if clearlow12 imm =? imm then Asm.ADRP else Asm.ADR in
        (Lst1 <$> asm i' imm r) orelse Lst0
    | Iimm Sz2 r reloc =>
        let imm := resolve reloc in
        if fits 21 (asr imm 12-i'>>10) then
          Lst2 (Asm.ADRP i' imm r orelse Asm.UDF)
               (Asm.Encode.MOVK 1 0 (imm land 0xffff) r)
        else if imm >> 32 =? 0 then
          Lst2 (Asm.Encode.MOVZ 1 1 (imm >> 16) r)
               (Asm.Encode.MOVK 1 0 (imm land 0xffff) r)
        else Lst0
    | Iimm Sz3 r reloc =>
        let imm := resolve reloc in
        if i' >> 46 =? imm >> 48 then
          Lst3 (Asm.ADRP (i' land (0xffff_ffff>>2)) (imm land 0xffff_ffff) r orelse Asm.UDF)
               (Asm.Encode.MOVK 1 2 ((imm >> 32) land 0xffff) r)
               (Asm.Encode.MOVK 1 0 (imm land 0xffff) r)
        else if imm >> 48 =? 0 then
          Lst3 (Asm.Encode.MOVZ 1 2 ((imm >> 32) land 0xffff) r)
               (Asm.Encode.MOVK 1 1 ((imm >> 16) land 0xffff) r)
               (Asm.Encode.MOVK 1 0 (imm land 0xffff) r)
        else Lst0

    | Ib Sz1 (B _) r =>
        (Lst1 <$> Asm.B i' (resolve r>>2)) orelse (Lst1 Asm.UDF)
    | Ib Sz1 (BL _) r =>
        (Lst1 <$> Asm.BL i' (resolve r>>2)) orelse (Lst1 Asm.UDF)
    | Ib Sz1 (Bcond _ cond) r =>
        (Lst1 <$> Asm.Bcond i' (resolve r>>2) cond) orelse Lst0
    | Ib Sz1 (CBZ sf op _ Rt) r =>
        (Lst1 <$> Asm.CBZ sf op i' (resolve r>>2) Rt) orelse Lst0
    | Ib Sz1 (TBZ b5 op b40 _ Rt) r =>
        (Lst1 <$> Asm.TBZ b5 op b40 i' (resolve r>>2) Rt) orelse Lst0

    | Ib Sz2 (Bcond _ cond) r =>
        let inv := (Asm.Bcond i' (i'+2) (cond lxor 1)) orelse Asm.UDF in
        (Lst2 inv <$> Asm.B (i'+1) (resolve r>>2)) orelse Lst0
    | Ib Sz2 (CBZ sf op _ Rt) r =>
        let inv := (Asm.CBZ sf (b2i (is_zero op)) i' (i'+2) Rt) orelse Asm.UDF in
        (Lst2 inv <$> Asm.B (i'+1) (resolve r>>2)) orelse Lst0
    | Ib Sz2 (TBZ b5 op b40 _ Rt) r =>
        let inv := (Asm.TBZ b5 (b2i (is_zero op)) b40 i' (i'+2) Rt) orelse Asm.UDF in
        (Lst2 inv <$> Asm.B (i'+1) (resolve r>>2)) orelse Lst0

    | _ => Lst0
    end.
  Definition emit chunks :=
    maybe_map (λ c,
      fold_left (λ a s,
        match a, s with
        | Some l, Lst1 a => Some (a::l)
        | Some l, Lst2 a b => Some (b::a::l)
        | Some l, Lst3 a b c => Some (c::b::a::l)
        | _, _ => None
        end)
      (c.(cd)) (Some nil) <&> @rev int <&> setd c
    ) chunks.
  Definition rw2 :=
    emit (chunkmapi rel isel d.(chunks)).
End InstSelection.
