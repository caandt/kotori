open Uint63

let lsr2 x = l_sr x (of_int 2)
let lsl2 x = l_sl x (of_int 2)
let ( % ) = Fun.compose
let to64 = Uint63.to_int64
let toint = Int64.to_int % to64
let hex = Printf.sprintf "%Lx" % to64

let (let*) (opt, e) f =
  match opt with
  | Some x -> f x
  | None -> Error e
let (let^) = Option.bind

module Uint63 = struct
  include Uint63
  let pp fmt x = Format.pp_print_string fmt (hex x)
end
type ityp = [%import: Kotori.ityp] [@@deriving show]
type eident = [%import: Kotori.eident] [@@deriving show]
type ehdr = [%import: Kotori.ehdr] [@@deriving show]
type phdr = [%import: Kotori.phdr] [@@deriving show]
type hash = [%import: Kotori.hash] [@@deriving show]
type isize = [%import: Kotori.isize] [@@deriving show]
type reloc = [%import: Kotori.reloc] [@@deriving show]
type cinst = [%import: Kotori.cinst] [@@deriving show]
type 'a chunk = [%import: 'a Kotori.chunk] [@@deriving show]
type nat = [%import: Kotori.nat] [@@deriving show]
type args = [%import: Kotori.args] [@@deriving show]
type table = [%import: Kotori.table] [@@deriving show]
type data = [%import: Kotori.data] [@@deriving show]

let vdso = List.map (lsr2 % of_int) [0x7ff7ffe320;0x7ff7ffe820;0x7ff7ffe5c0;0x7ff7ffe808;0x7ff7ffe770]

let rec to_nat n =
  if n = 0 then Kotori.O
  else S (to_nat (n-1))

let default_pol path =
  let^ elf = Packager.load path in
  let^ code, va = Packager.get_text elf in
  let bi = lsr2 va in
  let pol _ = zero in
  let dset = List.init (List.length code) (fun x -> add bi (of_int x)) in
  Some (pol, [vdso @ dset])

let make_args ?(pol=Fun.const zero) ?(dsets=[]) ?(runtime=Runtime.base) ?(nrelax=3) path =
  let^ elf = Packager.load path in
  let^ code, va = Packager.get_text elf in
  let bi = lsr2 va in
  let bi' = Packager.get_after elf |> lsr2 in
  let nrelax = to_nat nrelax in
  let rtlen = String.length runtime |> of_int in
  Some { code; pol; dsets; bi; bi'; nrelax; rtlen; orig_lr = true }

let global_data ?(pol=Fun.const zero) ?(dsets=[]) ?(runtime=Runtime.base) ?(nrelax=3) ?(hook=Fun.id) path =
  let^ a = make_args ~pol ~dsets ~runtime ~nrelax path in
  Kotori.rw_hook a hook

let to_strl s =
  let len = String.length s in
  let slen = toint Pstring.max_length in
  let rec aux i acc =
    if i >= len then List.rev acc
    else
      let sublen = min slen (len - i) in
      let str = String.sub s i sublen |> Pstring.of_string |> Option.get in
      aux (i + slen) (str::acc)
  in aux 0 []
