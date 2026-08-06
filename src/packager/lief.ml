open Ctypes
open Foreign

type elf = unit ptr
let elf: elf typ = ptr void
let rel_t = funptr (uint64_t @-> returning uint64_t)

let parse = foreign "lief_parse" (string @-> returning elf)
let parse_mem = foreign "lief_parse_mem" (ptr uint8_t @-> size_t @-> returning elf)
let get_text = foreign "lief_get_text" (elf @-> ptr size_t @-> ptr uint64_t @-> returning (ptr uint32_t))
let get_after = foreign "lief_get_after" (elf @-> returning uint64_t)
let get_entrypoint = foreign "lief_get_entrypoint" (elf @-> returning uint64_t)
let set_nx = foreign "lief_set_nx" (elf @-> returning void)
let set_entrypoint = foreign "lief_set_entrypoint" (elf @-> uint64_t @-> returning void)
let add_segment = foreign "lief_add_segment" (elf @-> ptr uint32_t @-> size_t @-> uint64_t @-> returning bool)
let write_and_free = foreign "lief_write_and_free" (elf @-> string @-> returning void)
let update_symbols = foreign "lief_update_symbols" (elf @-> rel_t @-> returning void)
let update_dynamic_entry = foreign "lief_update_dynamic_entry" (elf @-> rel_t @-> returning void)

(* force the linker to keep lief.cpp in the archive *)
external _force_link : unit -> unit = "_force_link"
