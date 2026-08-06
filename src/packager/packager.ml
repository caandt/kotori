open Ctypes
open Foreign
open Unsigned

let ( % ) = Fun.compose

let u63_of_u32 = Uint63.of_int64 % UInt32.to_int64
let u32_of_u63 = UInt32.of_int64 % Uint63.to_int64
let u64_of_u63 = UInt64.of_int64 % Uint63.to_int64
let u63_of_u64 = Uint63.of_int64 % UInt64.to_int64
let to_u63_list = List.map u63_of_u32 % CArray.to_list
let of_u63_list = CArray.of_list uint32_t % List.map u32_of_u63

let load filepath =
  let handle = Lief.parse filepath in
  if is_null handle then None else Some handle

let load_mem data =
  let arr = CArray.of_string data in
  let ptr = coerce (ptr char) (ptr uint8_t) @@ CArray.start arr in
  let len = CArray.length arr |> Size_t.of_int in
  let handle = Lief.parse_mem ptr len in
  if is_null handle then None else Some handle

let get_text elf =
  let elements_ptr = allocate size_t (Size_t.of_int 0) in
  let va_ptr = allocate uint64_t (UInt64.of_int 0) in
  let data_ptr = Lief.get_text elf elements_ptr va_ptr in

  if is_null data_ptr then None
  else
    let elements = Size_t.to_int (!@ elements_ptr) in
    let arr = CArray.from_ptr data_ptr elements in
    Some (to_u63_list arr, u63_of_u64 (!@ va_ptr))

let get_after = u63_of_u64 % Lief.get_after
let get_entrypoint = u63_of_u64 % Lief.get_entrypoint
let set_nx = Lief.set_nx

let set_entrypoint elf (entry: Uint63.t) =
  let entry = u64_of_u63 entry in
  Lief.set_entrypoint elf entry

let add_segment elf (data: Uint63.t list) (addr: Uint63.t) =
  let arr = of_u63_list data in
  let ptr = CArray.start arr in
  let len = CArray.length arr |> Size_t.of_int in
  let addr = addr |> Uint63.to_int64 |> UInt64.of_int64 in
  if Lief.add_segment elf ptr len addr then Some () else None

let add_segment_str elf (data: string) (addr: Uint63.t) =
  let arr = CArray.of_string data in
  let ptr = coerce (ptr char) (ptr uint32_t) @@ CArray.start arr in
  let len = String.length data / 4 |> Size_t.of_int in
  let addr = addr |> Uint63.to_int64 |> UInt64.of_int64 in
  if Lief.add_segment elf ptr len addr then Some () else None

let update_symbols elf (rel: Uint63.t -> Uint63.t) =
  let rel' u64 = u63_of_u64 u64 |> rel |> u64_of_u63 in
  Lief.update_symbols elf rel'

let update_dynamic_entry elf (rel: Uint63.t -> Uint63.t) =
  let rel' u64 = u63_of_u64 u64 |> rel |> u64_of_u63 in
  Lief.update_dynamic_entry elf rel'

let write_and_free = Lief.write_and_free
