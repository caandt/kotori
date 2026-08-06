type config = {
  name: string;
  cflags: string;
}

let configs = [
  { name = "polhook"; cflags = "-DA8_POL_HOOK=1 -DA8_NO_ASLR=1 -DA8_PRELOAD_REL=1" };
  { name = "polhook2"; cflags = "-DA8_POL_HOOK=2 -DA8_NO_ASLR=1 -DA8_PRELOAD_REL=1" };
  { name = "base"; cflags = "-DA8_NO_ASLR=1" };
]

let print_rules config =
  Printf.printf {|
(rule
 (target %s_polhook.o)
 (deps ../polhook.c ../runtime.h)
 (action
  (bash "a64-gcc -c -ffreestanding -fno-stack-protector -nostdlib -fPIE -O3 -fcall-saved-x{0..28} %s ../polhook.c -I. -o %%{target}")))

(rule
 (target %s_runtime.o)
 (deps ../runtime.c ../runtime.h)
 (action
  (bash "a64-gcc -c -ffreestanding -fno-stack-protector -nostdlib -fPIE -O3 %s ../runtime.c -I. -o %%{target}")))

(rule
 (target %s.elf)
 (action
  (run a64-ld -T %%{dep:../link.ld} -nostdlib %%{dep:%s_runtime.o} %%{dep:%s_polhook.o} -o %%{target})))

(rule
 (target %s.bin)
 (action
  (run a64-objcopy -O binary -j .text -j .got -j .got.plt %%{dep:%s.elf} %%{target})))
|}
    config.name config.cflags
    config.name config.cflags
    config.name config.name config.name
    config.name config.name

let _ =
  List.iter print_rules configs;
  Printf.printf {|
(rule
 (target runtime.ml)
 (deps ../gen_library.ml)
 (action
  (with-stdout-to %%{target}
   (run ocaml ../gen_library.ml %s))))
  |} (String.concat " " (List.map (fun x -> Printf.sprintf "%s %%{dep:%s.bin}" x.name x.name) configs))
