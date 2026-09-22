From Kotori Require Import Rewrite ELF Util.
From Stdlib Require Import Extraction ExtrOCamlInt63 ExtrOcamlBasic ExtrOCamlPArray ExtrOCamlPString PArray.

Extraction Language OCaml.
Extract Constant List.map => "(fun f l -> Parmap.parmap f (Parmap.L l))".
Extract Constant Util.mapi => "(fun f l -> Parmap.parmapi (fun i -> f (Uint63.of_int i)) (Parmap.L l))".
Extract Constant iimap => "(Uint63.t,Uint63.t)Hashtbl.t".
Extract Constant iimap_empty => "(fun sz -> Hashtbl.create (Int64.to_int @@ Uint63.to_int64 sz))".
Extract Constant iimap_insert => "(fun k v m -> Hashtbl.add m k v; m)".
Extract Constant iimap_lookup => "(fun k m -> Hashtbl.find_opt m k)".

Set Extraction Output Directory ".".
Extraction "kotori" elf_rw polhook counthook.
