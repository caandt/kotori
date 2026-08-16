From Rewriter Require Import Rewrite ELF.
From Stdlib Require Import Extraction ExtrOCamlInt63 ExtrOcamlBasic ExtrOCamlPArray ExtrOCamlPString PArray.

Extraction Language OCaml.
Extract Constant array "'a" => "'a Parray.t".
Extract Constant List.map => "(fun f l -> Parmap.parmap f (Parmap.L l))".
Extract Constant Util.mapi => "(fun f l -> Parmap.parmapi (fun i -> f (Uint63.of_int i)) (Parmap.L l))".
Extract Constant Util.len => "(fun x -> Uint63.of_int (List.length x))".

Set Extraction Output Directory ".".
Extraction "Rewriter" elf_rw polhook counthook.
