From Stdlib Require Import PString.
From Rewriter Require Import Util Rewrite Strl.
From RecordUpdate Require Import RecordUpdate.

Import SL.
Notation getu8 := get.
Definition getu16 s i := (getu8 s i) + (getu8 s (i+1)) << 8.
Definition getu32 s i := (getu16 s i) + (getu16 s (i+2)) << 16.
Definition getu64 s i :=
  assert negb (bit (getu8 s (i+7)) 7);
  return (getu32 s i) + (getu32 s (i+4)) << 32.
Definition u8 i := i land 0xff::nil.
Definition u16 i :=  u8 i ++  u8 (i >> 8).
Definition u32 i := u16 i ++ u16 (i >> 16).
Definition u64 i := u32 i ++ u32 (i >> 32).

Definition ELFMAG := 0x464c457f.
Definition ELFCLASS64 := 2.
Definition EV_CURRENT := 1.
Definition PT_NULL := 0.
Definition PT_LOAD := 1.
Definition PT_NOTE := 4.
Definition PF_RX := 5.

Definition uu64 := of_list ∘ u64.
Extract Constant uu64 => "(fun n ->
  let n = n |> Uint63.to_int2 |> snd in
  let s = Bytes.create 8 in
  for i = 0 to 7 do
    Bytes.set s i (Char.chr ((n lsr (8 * i)) land 0xff))
  done;
  Pstring.unsafe_of_string (Bytes.unsafe_to_string s)
)".
Record Eident := {
  ei_mag: int;
  ei_class: int;
  ei_data: int;
  ei_version: int;
  ei_osabi: int;
  ei_abiversion: int;
}.
Record Ehdr := {
  e_ident: Eident;
  e_type: int;
  e_machine: int;
  e_version: int;
  e_entry: int;
  e_phoff: int;
  e_shoff: int;
  e_flags: int;
  e_ehsize: int;
  e_phentsize: int;
  e_phnum: int;
  e_shentsize: int;
  e_shnum: int;
  e_shstrndx: int;
}.
Record Phdr := {
  p_type: int;
  p_flags: int;
  p_offset: int;
  p_vaddr: int;
  p_paddr: int;
  p_filesz: int;
  p_memsz: int;
  p_align: int;
}.
Record ELF := {
  ehdr: Ehdr;
  phdrs: list Phdr;
  data: list string;
}.

Definition parse_eident bin :=
  let ei_mag := getu32 bin 0 in
  let ei_class := getu8 bin 4 in
  let ei_data := getu8 bin 5 in
  let ei_version := getu8 bin 6 in
  let ei_osabi := getu8 bin 7 in
  let ei_abiversion := getu8 bin 8 in
  assert ei_mag =? ELFMAG;
  assert ei_class =? ELFCLASS64;
  assert ei_version =? EV_CURRENT;
  return {|
    ei_mag := ei_mag;
    ei_class := ei_class;
    ei_data := ei_data;
    ei_version := ei_version;
    ei_osabi := ei_osabi;
    ei_abiversion := ei_abiversion;
  |}.
Definition parse_ehdr bin :=
  e_ident ← parse_eident bin;
  let e_type := getu16 bin 16 in
  let e_machine := getu16 bin 18 in
  let e_version := getu32 bin 20 in
  e_entry ← getu64 bin 24;
  e_phoff ← getu64 bin 32;
  assert 64 <=? e_phoff;
  e_shoff ← getu64 bin 40;
  let e_flags := getu32 bin 48 in
  let e_ehsize := getu16 bin 52 in
  let e_phentsize := getu16 bin 54 in
  assert e_phentsize =? 56;
  let e_phnum := getu16 bin 56 in
  assert e_phoff <? e_phoff + 56 * e_phnum;
  let e_shentsize := getu16 bin 58 in
  let e_shnum := getu16 bin 60 in
  let e_shstrndx := getu16 bin 62 in
  return {|
    e_ident := e_ident;
    e_type := e_type;
    e_machine := e_machine;
    e_version := e_version;
    e_entry := e_entry;
    e_phoff := e_phoff;
    e_shoff := e_shoff;
    e_flags := e_flags;
    e_ehsize := e_ehsize;
    e_phentsize := e_phentsize;
    e_phnum := e_phnum;
    e_shentsize := e_shentsize;
    e_shnum := e_shnum;
    e_shstrndx := e_shstrndx;
  |}.
Definition parse_phdr_at bin i :=
  let p_type := getu32 bin i in
  let p_flags := getu32 bin (i+4) in
  p_offset ← getu64 bin (i+8);
  p_vaddr ← getu64 bin (i+16);
  p_paddr ← getu64 bin (i+24);
  p_filesz ← getu64 bin (i+32);
  p_memsz ← getu64 bin (i+40);
  p_align ← getu64 bin (i+48);
  return {|
    p_type := p_type;
    p_flags := p_flags;
    p_offset := p_offset;
    p_vaddr := p_vaddr;
    p_paddr := p_paddr;
    p_filesz := p_filesz;
    p_memsz := p_memsz;
    p_align := p_align;
  |}.
Function range step i n {measure to_nat n} :=
  if (n =? 0) then nil else i::range step (i+step) (n-1).
Proof. lia. Defined.
Definition phdr_offsets := range 56.
Definition to_words sl := map (getu32 sl) (range 4 0 (length sl >> 2)).
Definition of_chunks32 := map (λ x, of_list (List.concat (map_single u32 x.(cd)))).
Definition of_chunks64 l := List.concat (map (λ x, (map_single uu64 x)) l).
Definition of_chunks64' := flat_map (λ x, (map (λ y, uu64 y) x)).
Definition parse_phdr bin ehdr :=
  let n := ehdr.(e_phnum) in
  assert negb (n =? 0xffff);
  maybe_map (parse_phdr_at bin) (phdr_offsets ehdr.(e_phoff) n).
Definition parse_elf data :=
  assert 64 <? length data;
  ehdr ← parse_ehdr data;
  phdrs ← parse_phdr data ehdr;
  return {| ehdr := ehdr; phdrs := phdrs; data := data |}.

Fixpoint findn {A} (f:A -> bool) l n :=
  match l with | nil => None | a::t => if (f a) then Some n else findn f t (n+1) end.
Definition is_txt_seg p := (p.(p_type) =? PT_LOAD) && (bit p.(p_flags) 0).

Definition replaceable_seg phdrs :=
  match findn (λ x, x.(p_type) =? PT_NULL) phdrs 0 with
  | None => (findn (λ x, x.(p_type) =? PT_NOTE) phdrs 0)
  | Some n => Some n
  end.
Definition txt_seg elf := find is_txt_seg elf.(phdrs).
Definition load_seg offset vaddr content :=
  Build_Phdr PT_LOAD PF_RX offset vaddr vaddr (length content) (length content) 0x1000.
Definition phdr_data p :=
  map of_list (
    u32 p.(p_type)::
    u32 p.(p_flags)::
    u64 p.(p_offset)::
    u64 p.(p_vaddr)::
    u64 p.(p_paddr)::
    u64 p.(p_filesz)::
    u64 p.(p_memsz)::
    u64 p.(p_align)::nil
  ).
Definition listreplace {A} l n (x:A) := firstn n l++x::skipn (S n) l.
Definition replace_phdr elf phdr i :=
  let phdr_offset := elf.(ehdr).(e_phoff) + 56 * i in
  elf <| phdrs ::= λ p, listreplace p (to_nat i) phdr |>
      <| data ::= λ d, splice d phdr_offset (phdr_data phdr) |>.
Definition map_phdrs (f: Phdr -> option Phdr) elf :=
  let g '(e,i) p := match f p with None => (e,i+1) | Some p => (replace_phdr e p i, i+1) end in
  fst (fold_left g elf.(phdrs) (elf, 0)).
Definition with_load_seg elf content vaddr :=
  idx ← replaceable_seg elf.(phdrs);
  assert elf.(ehdr).(e_phoff) + 56 * idx + 56 <? length elf.(data);
  let padding := padding (length elf.(data)) 12 in
  let offset := length elf.(data) + padding in
  let elf := replace_phdr elf (load_seg offset vaddr content) idx in
  return elf <| data ::= λ d, cat (cat d [make padding 0]) content |>.
Definition set_nx := map_phdrs (λ p,
  assert is_txt_seg p;
  return p <| p_flags ::= Uint63.pred |>
).
Definition set_entrypoint elf entry :=
  elf <| ehdr; e_entry := entry |>
      <| data ::= λ d, splice d 24 (of_list (u64 entry)::nil) |>.
Definition get_page_after elf :=
  let f p := p.(p_vaddr) + p.(p_memsz) in
  let m := fold_left Uint63.max (map f elf.(phdrs)) 0 in
  ((m >> 12) + 2) << 10.
Definition phdr_content elf phdr :=
  sub elf.(data) phdr.(p_offset) phdr.(p_filesz).
Definition add_code bin code addr :=
  assert llt bin (max_int-0x1000);
  assert llt code max_int;
  elf ← parse_elf bin;
  with_load_seg elf code addr <&> data.
Definition replace_code bin code addr entry :=
  let bin := splice bin 24 [of_list (u64 entry)] in
  add_code bin code addr.

(*
   runtime data:
   {
     u64 text_start;
     u64 text_end;
     u64 new_text_start;
     u64 new_text_end;
     u64 real_entry;
     u64 nrets;
     u64 dsize;
     u32 d[];
   }
*)
Definition rtd d entry :=
  map (of_list ∘ u64) [
    d.(arg).(bi) << 2;
    (d.(arg).(bi) + len d.(arg).(code)) << 2;
    d.(arg).(bi') << 2;
    d.(bti) << 2;
    entry;
    len d.(rets);
    (len d.(devs)) >> 1
  ] ++ map (of_list ∘ u32) (
    d.(devs)
  ).

Definition elf_rw hook bin runtime pol dsets nrelax orig_lr :=
  elf ← parse_elf bin;
  ts ← txt_seg elf;
  let code := phdr_content elf ts in
  let bi := ts.(p_vaddr) >> 2 in
  let bi' := get_page_after elf in
  let arg := {|
    bi := bi; bi' := bi'; code := to_words code;
    pol := pol; dsets := dsets; nrelax := nrelax;
    rtlen := length runtime; orig_lr := orig_lr;
  |} in
  d' ← rw_hook arg hook;
  code' ← rw2 d';
  let entry_i := d'.(rel) (elf.(ehdr).(e_entry) >> 2) in
  let rtd := rtd d' (entry_i << 2) in
  let code' := of_chunks32 code' in
  let ofchunks64 := (if len d'.(tc) <? 3 then of_chunks64' else of_chunks64) in
  let tables := ofchunks64 (map_single tblcontent d'.(tc)) in
  let pad1 := padding (length code') 12 in
  let pad2 := padding (arg.(rtlen)) 12 in
  let pad3 := padding (length tables) 12 in
  let rtda := d'.(bti) << 2 + length tables + pad3 in
  let runtime := splice (runtime) 12 [of_list (u64 rtda)] in
  let content :=
    code' ++ [make pad1 0] ++
    runtime ++ [make pad2 0] ++
    tables ++ [make pad3 0] ++
    rtd in
  bin' ← replace_code ((set_nx elf).(data)) content (bi'<<2) (d'.(ai) << 2 + 4);
  return (bin', d').
