open Cmdliner
open Util
open Uint63

type config = {
  update_symbols: bool;
  polhook: bool;
  input: string;
  output: string;
  pol: string option;
  runtime: string;
  json: string option;
  onlyjson: bool;
  lr: bool;
}

let serialize_dat (d:CFI.Rewriter.data) : Yojson.Basic.t =
  let ji x = `Int (toint x) in
  `Assoc [
    ("bi", ji d.arg.bi);
    ("bi'", ji d.arg.bi');
    ("bti", ji d.bti);
    ("ai", ji d.ai);
    ("len", `Int (List.length d.arg.code));
    ("devs", `List (List.map ji d.devs));
    ("dsets", `List (List.map (fun d -> `List (List.map ji d)) d.arg.dsets));
    ("tc", `List (List.map (fun ((h, tbl), ti) -> `Assoc [
      ("hash", match h with H_UBFX (a, b) -> `List [ji a; ji b] | H_EOR_UBFX (a, b, c) -> `List [ji a; ji b; ji c]);
      ("tbl", `List (List.map ji tbl));
      ("ti", ji ti);
    ]) d.tc));
    ("pol", `List (List.init (List.length d.arg.code) ((+) (toint d.arg.bi)) |>
      List.filter_map (fun i ->
        let lbl = d.arg.pol (of_int i) in
        if lt lbl (List.length d.tc |> of_int)
        then Some (`List [`Int i; ji lbl])
        else None)));
    ("rets", `List (List.map ji d.rets));
  ]

let save args bin' (dat: CFI.Rewriter.data) =
  Option.iter (fun file -> Yojson.Basic.to_file file (serialize_dat dat)) args.json;
  if args.update_symbols then (
    let* elf' = Packager.load_mem (String.concat "" (List.map Pstring.to_string bin')), "Error reading input" in
    Packager.update_symbols elf' dat.rel;
    Packager.update_dynamic_entry elf' dat.rel;
    Packager.write_and_free elf' args.output;
    Ok (Unix.chmod args.output 0o755)
  ) else (
    Out_channel.with_open_bin args.output (fun oc -> List.iter (Out_channel.output_string oc) (List.map Pstring.to_string bin'));
    Ok (Unix.chmod args.output 0o755)
  )

let main args =
  let bin = In_channel.with_open_bin args.input In_channel.input_all in
  let bin = to_strl bin in
  let runtime = to_strl args.runtime in
  let nrelax = to_nat 3 in
  let getpol () = (
    if args.polhook then Some (Fun.const zero, []) else
    match args.pol with
    | None -> Util.default_pol args.input
    | Some p -> Policy.read_policy args.input p
  ), "Error reading policy" in
  let hook =
    if args.polhook then CFI.Rewriter.polhook2
    else Fun.id in

  if args.onlyjson then
    let* pol, dsets = getpol () in
    let* dat = global_data ~pol ~dsets args.input, "Error getting data" in
    Ok (Option.iter (fun file -> Yojson.Basic.to_file file (serialize_dat dat)) args.json)
  else
    let* pol, dsets = getpol () in
    let* bin', dat = CFI.Rewriter.elf_rw hook bin runtime pol dsets nrelax args.lr, "Error rewriting" in
    save args bin' dat

let input =
  let doc = "The input ELF to rewrite." in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"INPUT" ~doc)

let output =
  let doc = "The output path of the rewritten ELF." in
  let absent = "save to INPUT_rw" in
  Arg.(value & pos 1 (some string) None & info [] ~docv:"OUTPUT" ~doc ~absent)

let policy =
  let doc = "The policy file to use." in
  let absent = "use permissive policy" in
  Arg.(value & opt (some string) None & info ["p"; "policy"] ~docv:"POLICY" ~doc ~absent)

let abort =
  let doc = "The file containing the content of the abort segment." in
  let absent = "abort prints an error and exits" in
  Arg.(value & opt (some string) None & info ["A"; "abort"] ~docv:"ABORT" ~doc ~absent)

let update_symbols =
  let doc = "Enable updating symbols" in
  Arg.(value & flag & info ["s"; "symbols"] ~doc)
let polhook =
  let doc = "Use policy collection hook" in
  Arg.(value & flag & info ["P"; "polhook"] ~doc)
let json =
  let doc = "Dump JSON data to $(docv), or dump to OUTPUT and exit if $(docv) is \"only\"" in
  Arg.(value & opt (some string) None & info ["j"; "json"] ~docv:"FILE" ~doc)
let lr =
  let doc = "Rewrite BL/BLR to link the original address" in
  Arg.(value & flag & info ["L"; "lr"] ~doc)
let config =
  let make input output runtime pol update_symbols polhook json lr =
    let output = Option.value output ~default:(input ^ "_rw") in
    let runtime = Option.fold runtime
      ~some:(fun x -> In_channel.with_open_bin x In_channel.input_all)
      ~none:(if polhook then Runtime.polhook2 else Runtime.base) in
    let onlyjson = json = Some "only" in
    let json = if json = Some "only" then Some output else json in
    { input; output; update_symbols; polhook; runtime; pol; json; onlyjson; lr } in
  Term.(const make $ input $ output $ abort $ policy $ update_symbols $ polhook $ json $ lr)
let cmd =
  let term = Term.(const main $ config) in
  let info = Cmd.info "a64-cfi" ~doc:"CFI rewriter for AArch64" in
  Cmd.v info term

let () = exit (Cmd.eval_result cmd)
